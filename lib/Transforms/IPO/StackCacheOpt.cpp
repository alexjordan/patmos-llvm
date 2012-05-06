//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "scopt"
#include "llvm/Module.h"
#include "llvm/Analysis/CallSSA.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO.h"

using namespace llvm;

namespace {

  class StackCacheOpt : public ModulePass {
  public:
    StackCacheOpt() : ModulePass(ID) {
      initializeStackCacheOptPass(*PassRegistry::getPassRegistry());
    }
    static char ID; // Pass identification, replacement for typeid

    bool runOnModule(Module &M);

    void getAnalysisUsage(AnalysisUsage& AU) const {
      AU.addRequired<CallSSA>();
      AU.addPreserved<CallSSA>();
    }
  };
}

char StackCacheOpt::ID = 0;
INITIALIZE_PASS_BEGIN(StackCacheOpt, "scopt",
                "Stack Cache Optimization", true, false)
INITIALIZE_PASS_DEPENDENCY(CallSSA)
INITIALIZE_PASS_END(StackCacheOpt, "scopt",
                "Stack Cache Optimization", true, false)

ModulePass *llvm::createStackCacheOptPass() { return new StackCacheOpt(); }


bool StackCacheOpt::runOnModule(Module &M) {
  errs() << "FOO Stack cache opt\n";
  return true;
}

