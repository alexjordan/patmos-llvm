//==-- PatmosISelLowering.h - Patmos DAG Lowering Interface ------*- C++ -*-==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines the interfaces that Patmos uses to lower LLVM code into a
// selection DAG.
//
//===----------------------------------------------------------------------===//

#ifndef _LLVM_TARGET_PATMOS_ISELLOWERING_H_
#define _LLVM_TARGET_PATMOS_ISELLOWERING_H_

#include "Patmos.h"
#include "llvm/CodeGen/SelectionDAG.h"
#include "llvm/Target/TargetLowering.h"

namespace llvm {
  namespace PatmosISD {
    enum {
      FIRST_NUMBER = ISD::BUILTIN_OP_END,

      /// Return with a flag operand. Operand 0 is the chain operand.
      RET_FLAG,

      /// CALL - These operations represent an abstract call
      /// instruction, which includes a bunch of information.
      CALL,

      /// DYNALLOC - Dynamic Stack Allocation.
      DYNALLOC,

      /// multiplication
      MUL, MULU
    };
  } // end namespace PatmosISD

  class PatmosSubtarget;
  class PatmosTargetMachine;

  class PatmosTargetLowering : public TargetLowering {
  public:
    explicit PatmosTargetLowering(PatmosTargetMachine &TM);

    /// LowerOperation - Provide custom lowering hooks for some operations.
    virtual SDValue LowerOperation(SDValue Op, SelectionDAG &DAG) const;

    /// getTargetNodeName - This method returns the name of a target specific
    /// DAG node.
    virtual const char *getTargetNodeName(unsigned Opcode) const;

    virtual EVT getSetCCResultType(EVT VT) const;

  private:
    const PatmosSubtarget &Subtarget;
    const PatmosTargetMachine &TM;
    const TargetData *TD;

    SDValue LowerCCCCallTo(SDValue Chain, SDValue Callee,
                           CallingConv::ID CallConv, bool isVarArg,
                           bool isTailCall,
                           const SmallVectorImpl<ISD::OutputArg> &Outs,
                           const SmallVectorImpl<SDValue> &OutVals,
                           const SmallVectorImpl<ISD::InputArg> &Ins,
                           DebugLoc dl, SelectionDAG &DAG,
                           SmallVectorImpl<SDValue> &InVals) const;

    SDValue LowerCCCArguments(SDValue Chain,
                              CallingConv::ID CallConv,
                              bool isVarArg,
                              const SmallVectorImpl<ISD::InputArg> &Ins,
                              DebugLoc dl,
                              SelectionDAG &DAG,
                              SmallVectorImpl<SDValue> &InVals) const;

    SDValue LowerCallResult(SDValue Chain, SDValue InFlag,
                            CallingConv::ID CallConv, bool isVarArg,
                            const SmallVectorImpl<ISD::InputArg> &Ins,
                            DebugLoc dl, SelectionDAG &DAG,
                            SmallVectorImpl<SDValue> &InVals) const;
  public:
    virtual SDValue LowerCall(SDValue Chain, SDValue Callee, CallingConv::ID CallConv,
                      bool isVarArg, bool doesNotRet, bool &isTailCall,
                      const SmallVectorImpl<ISD::OutputArg> &Outs,
                      const SmallVectorImpl<SDValue> &OutVals,
                      const SmallVectorImpl<ISD::InputArg> &Ins,
                      DebugLoc dl, SelectionDAG &DAG,
                      SmallVectorImpl<SDValue> &InVals) const;

    virtual SDValue LowerFormalArguments(SDValue Chain,
                                 CallingConv::ID CallConv, bool isVarArg,
                                 const SmallVectorImpl<ISD::InputArg> &Ins,
                                 DebugLoc dl, SelectionDAG &DAG,
                                 SmallVectorImpl<SDValue> &InVals) const;

    virtual SDValue LowerReturn(SDValue Chain,
                        CallingConv::ID CallConv, bool isVarArg,
                        const SmallVectorImpl<ISD::OutputArg> &Outs,
                        const SmallVectorImpl<SDValue> &OutVals,
                        DebugLoc dl, SelectionDAG &DAG) const;

    /*
    virtual bool getPostIndexedAddressParts(SDNode *N, SDNode *Op,
                                            SDValue &Base,
                                            SDValue &Offset,
                                            ISD::MemIndexedMode &AM,
                                            SelectionDAG &DAG) const;
    */

    virtual std::pair<unsigned, const TargetRegisterClass*>
      getRegForInlineAsmConstraint(const std::string &Constraint,
                                   EVT VT) const;

    /// LowerDYNAMIC_STACKALLOC - Lower a dynamic stack allocation (aka alloca).
    SDValue LowerDYNAMIC_STACKALLOC(SDValue Op, SelectionDAG &DAG) const;

    /// LowerVASTART - Lower the va_start intrinsic to access parameters of
    /// variadic functions.
    SDValue LowerVASTART(SDValue Op, SelectionDAG &DAG) const;

    /// LowerMUL_LOHI - Lower Lo/Hi multiplications.
    SDValue LowerMUL_LOHI(SDValue Op, SelectionDAG &DAG) const;
  };
} // namespace llvm

#endif // _LLVM_TARGET_PATMOS_ISELLOWERING_H_






