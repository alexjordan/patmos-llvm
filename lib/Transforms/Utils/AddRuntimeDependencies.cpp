//===-- AddRuntimeDependencies.cpp - Add declarations for rtlib ------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass adds declarations for rtlib.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "addruntimedeps"

#include "llvm/Transforms/Scalar.h"
#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Intrinsics.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/InstVisitor.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"

using namespace llvm;

STATISTIC(NumDeclsAdded, "Number of declarations added");

STATISTIC(NumIntrinsicsLowered, "Number of lowered intrinsic calls");
STATISTIC(NumIntrinsicsIgnored, "Number of ignored intrinsic calls");

static SmallPtrSet<Value *, 4> DeclsSet;


static cl::opt<std::string>
FloatABI("float-abi", cl::value_desc("soft|hard"),
        cl::desc("Enable adding deps to the softfloat runtime library and lowering float operations to rtlib calls"),
        cl::init("soft"));

static cl::opt<bool>
LowerCalls("lower-rtlib-calls", cl::init(false),
        cl::desc("Replace intrinsic calls and some operations with runtime library calls where possible"));


// VisualStudio defines setjmp as _setjmp
#if defined(_MSC_VER) && defined(setjmp) && \
                         !defined(setjmp_undefined_for_msvc)
#  pragma push_macro("setjmp")
#  undef setjmp
#  define setjmp_undefined_for_msvc
#endif

namespace {

  class CallConfig;

  class RuntimeInstructionVisitor {
    bool LowerCalls;
    Module *M;
    LLVMContext *Context;
    const TargetData *TD;

    SmallPtrSet<Constant*, 8> Used;
    SmallPtrSet<Constant*, 8> Lowered;

  public:
    RuntimeInstructionVisitor() : LowerCalls(false) {}

    void setLowerCalls(bool Lower) {
      LowerCalls = Lower;
    }

    void setTargetData(Module &M, const TargetData *TD) {
      this->M = &M;
      this->Context = &M.getContext();
      this->TD = TD;
    }

    /// return the referenced function declaration, if any
    Constant *processInstruction(Instruction *I, CallConfig &Config, CallInst **NewCI);

    /// Update llvm.used GlobalVariable with the added declarations
    void updateLLVMUsed();

  private:
    /// Lower the given instruction. Returns the new call instruction if lowering was performed, else NULL.
    CallInst *replaceInstruction(Instruction *I, CallConfig &Config, Constant *F);

  };


  class AddRuntimeDependencies : public ModulePass,
                          public InstVisitor<AddRuntimeDependencies>
  {
  protected:
    friend class InstVisitor<AddRuntimeDependencies>;

    class RuntimeInstructionVisitor RIC;
    bool HandleFloats;
  public:
    static char ID; // Pass identification, replacement for typeid

    AddRuntimeDependencies() : ModulePass(ID) {
      initializeAddRuntimeDependenciesPass(*PassRegistry::getPassRegistry());

      RIC.setLowerCalls(LowerCalls);

      // TODO maybe handle floats depending on type of FPU (only some/all float instructions, ..)
      HandleFloats = (FloatABI != "hard");
    }

    virtual ~AddRuntimeDependencies() { }

    virtual bool runOnModule(Module &M);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesCFG();
      AU.addRequired<TargetData>();
    }

    virtual void print(raw_ostream &O, const Module *M) const {}

  protected:
    void visitCallInst(CallInst &CI);

    void visitCastInst(CastInst &I);
    void visitFCmpInst(FCmpInst &I);
    void visitBinaryOperator(BinaryOperator &I);
    void visitUnaryInstruction(UnaryInstruction &I);

    void visitIntrinsicCall(CallInst *CI);

    const char *getFPFunctionName(Instruction *I, const char *FName, const char *DName, const char *LName) {
      switch (I->getOperand(0)->getType()->getTypeID()) {
      case Type::FloatTyID:
        return FName;
      case Type::DoubleTyID:
        return DName;
      case Type::X86_FP80TyID:
      case Type::FP128TyID:
      case Type::PPC_FP128TyID:
        return LName;
      default: llvm_unreachable("Invalid type in float instruction.");
        return 0; // To make eclipse happy..
      }
    }

    const char *getIntFunctionName(Instruction *I, const char *SName, const char *DName) {
      switch (I->getOperand(0)->getType()->getIntegerBitWidth()) {
      case 64:
        return DName;
      case 32:
        return SName;
      default: llvm_unreachable("Invalid type size in integer instruction.");
        return 0; // To make eclipse happy..
      }
    }

  };


  class CallConfig {
  public:
    CallConfig() {}
    virtual ~CallConfig() {}

    virtual Constant* getPrototype(LLVMContext &Context, Module &M, const TargetData &TD) = 0;

    /// return false when the instruction cannot be lowered.
    virtual bool addCallArguments(LLVMContext &Context, Module &M, const TargetData &TD,
                                  IRBuilder<> &Builder, SmallVectorImpl<Value*> &Args) = 0;

  };

  class SimpleCallConfig: public CallConfig {
    const char *FnName;
    User::const_op_iterator ArgBegin, ArgEnd;
    Type *RetTy;
    bool AllowLower;
  public:
    SimpleCallConfig(const char *FnName, User::const_op_iterator ArgBegin, User::const_op_iterator ArgEnd,
                             Type *RetTy, bool AllowLower)
     : CallConfig(), FnName(FnName), ArgBegin(ArgBegin), ArgEnd(ArgEnd),
       RetTy(RetTy), AllowLower(AllowLower) { }

    SimpleCallConfig(const char *FnName, CallSite &CS, Type* RetTy, bool AllowLower = true)
     : CallConfig(), FnName(FnName), ArgBegin(CS.arg_begin()), ArgEnd(CS.arg_end()),
       RetTy(RetTy), AllowLower(AllowLower) { }

    SimpleCallConfig(const char *FnName, Instruction &I, bool AllowLower = true)
     : CallConfig(), FnName(FnName), ArgBegin(I.op_begin()), ArgEnd(I.op_end()),
       RetTy(I.getOperand(0)->getType()), AllowLower(AllowLower) { }


    virtual Constant* getPrototype(LLVMContext &Context, Module &M, const TargetData &TD) {
      std::vector<Type *> ParamTys;
      for (User::const_op_iterator I = ArgBegin; I != ArgEnd; ++I)
        ParamTys.push_back((*I)->getType());
      return M.getOrInsertFunction(FnName, FunctionType::get(RetTy, ParamTys, false));
    }

    virtual bool addCallArguments(LLVMContext &Context, Module &M, const TargetData &TD,
                                  IRBuilder<> &Builder, SmallVectorImpl<Value*> &Args)
    {
      if (!AllowLower) return false;
      Args.append(ArgBegin, ArgEnd);
      return true;
    }
  };

  class DivModCallConfig: public CallConfig {
    const char *FnName;
    Type *ITy;
  public:
    DivModCallConfig(const char *FnName, Instruction &I)
     : CallConfig(), FnName(FnName), ITy(I.getOperand(0)->getType()) { }

    virtual Constant* getPrototype(LLVMContext &Context, Module &M, const TargetData &TD) {
      std::vector<Type *> ParamTys;
      ParamTys.push_back(ITy);
      ParamTys.push_back(ITy);
      ParamTys.push_back(ITy->getPointerTo(0));
      return M.getOrInsertFunction(FnName, FunctionType::get(ITy, ParamTys, false));
    }

    virtual bool addCallArguments(LLVMContext &Context, Module &M, const TargetData &TD,
                                  IRBuilder<> &Builder, SmallVectorImpl<Value*> &Args)
    {
      return false;
    }
  };

  class MemCallConfig: public CallConfig {
    const char *FnName;
    CallInst *CI;
    bool isMemset;
  public:
    MemCallConfig(const char *FnName, CallInst *CI, bool isMemset)
     : CallConfig(), FnName(FnName), CI(CI), isMemset(isMemset) { }

    virtual Constant* getPrototype(LLVMContext &Context, Module &M, const TargetData &TD) {
      return M.getOrInsertFunction(FnName,
            Type::getInt8PtrTy(Context),
            Type::getInt8PtrTy(Context),
            isMemset ? (Type*) Type::getInt32Ty(Context) : (Type*) Type::getInt8PtrTy(Context),
            TD.getIntPtrType(Context), (Type *)0);
    }

    virtual bool addCallArguments(LLVMContext &Context, Module &M, const TargetData &TD,
                                  IRBuilder<> &Builder, SmallVectorImpl<Value*> &Args)
    {
      IntegerType *IntPtr = TD.getIntPtrType(Context);
      Value *Size = Builder.CreateIntCast(CI->getArgOperand(2), IntPtr,
                                          /* isSigned */ false);

      Args.push_back( CI->getArgOperand(0) );
      if ( isMemset ) {
        Args.push_back( Builder.CreateIntCast(CI->getArgOperand(1),
                                               Type::getInt32Ty(Context),
                                               /* isSigned */ false) );
      } else {
        Args.push_back( CI->getArgOperand(1) );
      }
      Args.push_back( Size );

      return true;
    }
  };

}



char AddRuntimeDependencies::ID = 0;
INITIALIZE_PASS(AddRuntimeDependencies, "add-runtime-deps",
                "Add declarations, calls and dependencies for runtime library functions", false, false)

ModulePass *
llvm::createAddRuntimeDependenciesPass() { return new AddRuntimeDependencies(); }

//-----------------------------------------------------------------------------

bool AddRuntimeDependencies::runOnModule(Module &M) {
  RIC.setTargetData(M, &getAnalysis<TargetData>());

  visit(M);

  RIC.updateLLVMUsed();

  NumDeclsAdded = DeclsSet.size();
  return true;
}

void AddRuntimeDependencies::visitCallInst(CallInst &CI) {
  const Function *Callee = CI.getCalledFunction();

  if (Callee && CI.getCalledFunction()->isIntrinsic()) {
    visitIntrinsicCall(&CI);
  }
}

void AddRuntimeDependencies::visitIntrinsicCall(CallInst *CI) {
  IRBuilder<> Builder(CI->getParent(), CI);
  LLVMContext &Context = CI->getContext();

  bool wasHandled = true;
  Constant *F = NULL;
  CallInst *V;
  CallSite CS(CI);

  switch (CI->getCalledFunction()->getIntrinsicID()) {
    // Other intrinsics:
    // - va_start, va_end, va_copy
    // - gcroot, gcread, gcwrite
    // Not needed:
    // - flt_rounds, cttz, ctlz, ctpop: expanded to instructions
    case Intrinsic::memcpy:
    {
      MemCallConfig CC("memcpy", CI, false);
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::memmove:
    {
      MemCallConfig CC("memmove", CI, false);
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::memset:
    {
      MemCallConfig CC("memset", CI, true);
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    // The setjmp/longjmp intrinsics should only exist in the code if it was
    // never optimized (ie, right out of the CFE), or if it has been hacked on
    // by the lowerinvoke pass.  In both cases, the right thing to do is to
    // convert the call to an explicit setjmp or longjmp call.
    case Intrinsic::setjmp:
    {
      SimpleCallConfig CC("setjmp", CS, Type::getInt32Ty(Context));
      F = RIC.processInstruction(CI, CC, &V);

      if (V && !CI->getType()->isVoidTy())
        CI->replaceAllUsesWith(V);
      break;
    }
    case Intrinsic::longjmp:
    {
      SimpleCallConfig CC("longjmp", CS, Type::getVoidTy(Context));
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::sigsetjmp:
      // is removed
      if (!CI->getType()->isVoidTy())
        CI->replaceAllUsesWith(Constant::getNullValue(CI->getType()));
      break;
    case Intrinsic::siglongjmp:
    case Intrinsic::trap:
    {
      // Insert the call to abort
      SimpleCallConfig CC("abort", CS.arg_end(), CS.arg_end(), Type::getVoidTy(Context), false);
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }

    case Intrinsic::sqrt:
    {
      SimpleCallConfig CC(getFPFunctionName(CI, "sqrtf", "sqrt", "sqrtl"), CS, CI->getArgOperand(0)->getType());
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::sin:
    {
      SimpleCallConfig CC(getFPFunctionName(CI, "sinf", "sin", "sinl"), CS, CI->getArgOperand(0)->getType());
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::cos:
    {
      SimpleCallConfig CC(getFPFunctionName(CI, "cosf", "cos", "cosl"), CS, CI->getArgOperand(0)->getType());
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::log:
    {
      SimpleCallConfig CC(getFPFunctionName(CI, "logf", "log", "logl"), CS, CI->getArgOperand(0)->getType());
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::log2:
    {
      SimpleCallConfig CC(getFPFunctionName(CI, "log2f", "log2", "log2l"), CS, CI->getArgOperand(0)->getType());
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::log10:
    {
      SimpleCallConfig CC(getFPFunctionName(CI, "log10f", "log10", "log10l"), CS, CI->getArgOperand(0)->getType());
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::exp:
    {
      SimpleCallConfig CC(getFPFunctionName(CI, "expf", "exp", "expl"), CS, CI->getArgOperand(0)->getType());
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::exp2:
    {
      SimpleCallConfig CC(getFPFunctionName(CI, "exp2f", "exp2", "exp2l"), CS, CI->getArgOperand(0)->getType());
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::pow:
    {
      SimpleCallConfig CC(getFPFunctionName(CI, "powf", "pow", "powl"), CS, CI->getArgOperand(0)->getType());
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::powi:
    {
      SimpleCallConfig CC(getFPFunctionName(CI, "__powisf2", "__powidf2", "__powixf2"), CS, CI->getArgOperand(0)->getType());
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    case Intrinsic::fma: // fused multiply-add
    {
      SimpleCallConfig CC(getFPFunctionName(CI, "fmaf", "fma", "fmal"), CS, CI->getArgOperand(0)->getType());
      F = RIC.processInstruction(CI, CC, &V);
      break;
    }
    // TODO: (u|s)(mul|add|sub)_with_overflow ??

    default:
      /* ignore call to intrinsic function */
      wasHandled = false;
      break;
  }

  if (wasHandled) {
    if (F) DeclsSet.insert(F);

    if (CI->use_empty()) {
      CI->eraseFromParent();
      NumIntrinsicsLowered++;
    }
  } else {
    NumIntrinsicsIgnored++;
  }
}

void AddRuntimeDependencies::visitCastInst(CastInst &I) {
  if (!HandleFloats) return;

}

void AddRuntimeDependencies::visitFCmpInst(FCmpInst &I) {
  if (!HandleFloats) return;

}

void AddRuntimeDependencies::visitBinaryOperator(BinaryOperator &I) {
  Type *OpTy = I.getOperand(0)->getType();

  // TODO configure which instructions will be lowered to a runtime call.. maybe get infos
  // from backend, including RTLIB names ???

  // TODO this might be too conservative: if one of the arguments is a constant,
  // it might be lowered to a simpler set of instructions (e.g. shladd instead of div)

  // For now we do not lower div and mod, so that the backend can do some optimizations

  switch (I.getOpcode()) {
  case Instruction::UDiv:
  {
    SimpleCallConfig CC(getIntFunctionName(&I, "__udivsi3", "__udivdi3"), I, false);
    RIC.processInstruction(&I, CC, NULL);
    // TODO we do not know if we actually need it, but just in case the selector uses it..
    DivModCallConfig DM(getIntFunctionName(&I, "__udivmodsi3", "__udivmoddi3"), I);
    RIC.processInstruction(&I, DM, NULL);
    return;
  }
  case Instruction::SDiv:
  {
    SimpleCallConfig CC(getIntFunctionName(&I, "__divsi3", "__divdi3"), I, false);
    RIC.processInstruction(&I, CC, NULL);
    // TODO we do not know if we actually need it, but just in case the selector uses it..
    DivModCallConfig DM(getIntFunctionName(&I, "__divmodsi3", "__divmoddi3"), I);
    RIC.processInstruction(&I, DM, NULL);
    return;
  }
  case Instruction::URem:
  {
    SimpleCallConfig CC(getIntFunctionName(&I, "__umodsi3", "__umoddi3"), I, false);
    RIC.processInstruction(&I, CC, NULL);
    return;
  }
  case Instruction::SRem:
  {
    SimpleCallConfig CC(getIntFunctionName(&I, "__modsi3", "__moddi3"), I, false);
    RIC.processInstruction(&I, CC, NULL);
    return;
  }
  default: break;
  }

  if (OpTy->isIntegerTy(64)) {
    switch (I.getOpcode()) {
    case Instruction::Shl:
    {
      SimpleCallConfig CC("__ashldi3", I);
      RIC.processInstruction(&I, CC, NULL);
      return;
    }
    case Instruction::LShr:
    {
      SimpleCallConfig CC("__lshrdi3", I);
      RIC.processInstruction(&I, CC, NULL);
      return;
    }
    case Instruction::AShr:
    {
      SimpleCallConfig CC("__ashrdi3", I);
      RIC.processInstruction(&I, CC, NULL);
      return;
    }
    default: return;
    }
  }

  if (!HandleFloats) return;

  switch (I.getOpcode()) {
  case Instruction::FAdd:
  {
    SimpleCallConfig CC(getFPFunctionName(&I, "__addsf3", "__adddf3", "__addxf3"), I);
    RIC.processInstruction(&I, CC, NULL);
    return;
  }
  case Instruction::FSub:
  {
    SimpleCallConfig CC(getFPFunctionName(&I, "__subsf3", "__subdf3", "__subxf3"), I);
    RIC.processInstruction(&I, CC, NULL);
    return;
  }
  case Instruction::FMul:
  {
    SimpleCallConfig CC(getFPFunctionName(&I, "__mulsf3", "__muldf3", "__mulxf3"), I);
    RIC.processInstruction(&I, CC, NULL);
    return;
  }
  case Instruction::FDiv:
  {
    SimpleCallConfig CC(getFPFunctionName(&I, "__divsf3", "__divdf3", "__divxf3"), I);
    RIC.processInstruction(&I, CC, NULL);
    return;
  }
  case Instruction::FRem:
  {
    SimpleCallConfig CC(getFPFunctionName(&I, "fmodf", "fmod", "fmodl"), I);
    RIC.processInstruction(&I, CC, NULL);
    return;
  }
  default: break;
  }
}

void AddRuntimeDependencies::visitUnaryInstruction(UnaryInstruction &I) {
  if (!HandleFloats) return;


}


//-----------------------------------------------------------------------------

Constant* RuntimeInstructionVisitor::processInstruction(Instruction *I, CallConfig &Config, CallInst **NewCI) {

  Constant *F = Config.getPrototype(*Context, *M, *TD);
  CallInst *Result;

  bool lowered;

  if (LowerCalls) {
    Result = replaceInstruction(I, Config, F);
    lowered = (Result != NULL);
  } else {
    Result = NULL;
    lowered = false;
  }
  if (NewCI) {
    *NewCI = Result;
  }

  // Update llvm.used here
  if (!lowered && F) {
    Used.insert(F);
  } else if (lowered && F) {
    Lowered.insert(F);
  }

  return F;
}

CallInst *RuntimeInstructionVisitor::replaceInstruction(Instruction *I, CallConfig &Config, Constant *F) {
  SmallVector<Value *, 8> Args;
  IRBuilder<> Builder(I->getParent(), I);

  if (!Config.addCallArguments(*Context, *M, *TD, Builder, Args)) {
    return NULL;
  }

  CallInst *NewCI = Builder.CreateCall(F, Args);
  NewCI->setName(I->getName());
  if (!I->use_empty())
    I->replaceAllUsesWith(NewCI);

  return NewCI;
}

void RuntimeInstructionVisitor::updateLLVMUsed() {

  GlobalVariable *LLVMUsed = M->getGlobalVariable("llvm.used");

  if (Used.empty() && (!LLVMUsed || Lowered.empty())) {
    return;
  }

  // We always mark as used what we did not lower in this pass, even if another use was lowered
  SmallVector<Constant*, 8> UsedArray(Used.begin(), Used.end());

  // Read out llvm.used, merge with Used
  ConstantArray *Init = 0;
  if (LLVMUsed) {
    Init = dyn_cast<ConstantArray>(LLVMUsed->getInitializer());
    if (Init) {
      for (unsigned i = 0, e = Init->getNumOperands(); i != e; ++i) {
        Constant *GV = dyn_cast<Constant>(Init->getOperand(i)->stripPointerCasts());
        if (GV == 0 || Used.count(GV) == 0) continue;

        // TODO skip all values that have been lowered now. This may be unsafe, so make it optional.

        UsedArray.push_back(GV);
      }
    }
  }

  PointerType *Int8PtrTy = Type::getInt8PtrTy(*Context, 0);
  ArrayType *ATy = llvm::ArrayType::get(Int8PtrTy, UsedArray.size());

  for (unsigned i = 0, e = UsedArray.size(); i != e; ++i) {
    UsedArray[i] = ConstantExpr::getBitCast(UsedArray[i], Int8PtrTy);
  }

  Constant* NewInit = ConstantArray::get(ATy, UsedArray);

  // Cannot change the type of the variable, so create a new one, replace and erase old one
  GlobalVariable *NewUsed = new GlobalVariable(*M, ATy, false, GlobalValue::AppendingLinkage,
                                NewInit, "llvm.used");
  NewUsed->setSection("llvm.metadata");

  if (LLVMUsed) {
    if (Init) {
      Init->replaceAllUsesWith(NewInit);
      assert(Init->use_empty());
      delete Init;
    }
    LLVMUsed->replaceAllUsesWith(NewUsed);

    LLVMUsed->eraseFromParent();
  }

}

