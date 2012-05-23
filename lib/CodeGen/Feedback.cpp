//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

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
  DEBUG({
      dbgs() << "********** Stack Feedback **********\n"
             << "********** Function: " 
             << MF.getFunction()->getName() << '\n';
    });

  MFI = MF.getFrameInfo();
  MFB->getStackInfo()->StackSizes[MF.getFunction()] = MFI->getStackSize();
#if 0
  MRI = &MF.getRegInfo(); 
  TII = MF.getTarget().getInstrInfo();
  TRI = MF.getTarget().getRegisterInfo();
  LS = &getAnalysis<LiveStacks>();
  VRM = &getAnalysis<VirtRegMap>();
  loopInfo = &getAnalysis<MachineLoopInfo>();

  bool Changed = false;

  unsigned NumSlots = LS->getNumIntervals();
  if (NumSlots < 2) {
    if (NumSlots == 0 || !VRM->HasUnusedRegisters())
      // Nothing to do!
      return false;
  }

  // If there are calls to setjmp or sigsetjmp, don't perform stack slot
  // coloring. The stack could be modified before the longjmp is executed,
  // resulting in the wrong value being used afterwards. (See
  // <rdar://problem/8007500>.)
  if (MF.callsSetJmp())
    return false;

  // Gather spill slot references
  ScanForSpillSlotRefs(MF);
  InitializeSlots();
  Changed = ColorSlots(MF);

  NextColor = -1;
  SSIntervals.clear();
  for (unsigned i = 0, e = SSRefs.size(); i != e; ++i)
    SSRefs[i].clear();
  SSRefs.clear();
  OrigAlignments.clear();
  OrigSizes.clear();
  AllColors.clear();
  UsedColors.clear();
  for (unsigned i = 0, e = Assignments.size(); i != e; ++i)
    Assignments[i].clear();
  Assignments.clear();

  if (Changed) {
    for (MachineFunction::iterator I = MF.begin(), E = MF.end(); I != E; ++I)
      Changed |= RemoveDeadStores(I);
  }

  return Changed;
#endif
  return false;
}
