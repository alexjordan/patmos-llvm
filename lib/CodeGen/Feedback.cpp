//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "sca"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/Analysis/StackCache.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/LiveIntervalAnalysis.h"
#include "llvm/CodeGen/LiveStackAnalysis.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineMemOperand.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/PseudoSourceValue.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Target/TargetInstrInfo.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include <vector>
using namespace llvm;

STATISTIC(NumFixed,      "Number of fixed stack objects");
STATISTIC(NumSpills,     "Number of spill slot stack objects");
STATISTIC(NumTemps,      "Number of temporary stack objects");
STATISTIC(NumVariable,   "Number of variable sized stack objects");

namespace {
  class StackFeedback : public MachineFunctionPass {
    MachineFeedback *MFB;
    MachineFrameInfo *MFI;
  public:
    static char ID; // Pass identification
    StackFeedback(MachineFeedback *mfb = NULL) :
      MachineFunctionPass(ID), MFB(mfb) {
        initializeStackFeedbackPass(*PassRegistry::getPassRegistry());
      }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
      MachineFunctionPass::getAnalysisUsage(AU);
    }

    virtual bool runOnMachineFunction(MachineFunction &MF);
    virtual const char* getPassName() const {
      return "Stack Feedback";
    }
  };
} // end anonymous namespace

char StackFeedback::ID = 0;

INITIALIZE_PASS_BEGIN(StackFeedback, "stack-feedback",
                "Stack info feedback pass", false, false)
//INITIALIZE_PASS_DEPENDENCY(SlotIndexes)
INITIALIZE_PASS_END(StackFeedback, "stack-slot-coloring",
                "Stack info feedback pass", false, false)

FunctionPass *llvm::createFeedbackPass(TargetMachine &tm) {
  return new StackFeedback(&tm.getFeedback());
}

bool StackFeedback::runOnMachineFunction(MachineFunction &MF) {

  int64_t StackSize = 0;
  MFI = MF.getFrameInfo();

  for (int i = MFI->getObjectIndexBegin(), e = MFI->getObjectIndexEnd();
       i != e; ++i) {
    if (MFI->isDeadObjectIndex(i))
      continue; // don't add to stack size

    int64_t sz = MFI->getObjectSize(i);
    if (sz == 0) {
      ++NumVariable;
    } else if (MFI->isFixedObjectIndex(i)) {
      ++NumFixed; // don't add to stack size
      continue;
    } else if (MFI->isSpillSlotObjectIndex(i)) {
      ++NumSpills;
    } else if (MFI->isTemporaryObjectIndex(i)) {
      ++NumTemps;
    }

    StackSize += sz;
  }

  MFB->getStackInfo()->StackSizes[MF.getFunction()] = StackSize;

  return false;
}
