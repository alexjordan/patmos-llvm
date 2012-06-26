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

static cl::opt<std::string>
SCAOutputFilename("sca-output-file", cl::value_desc("filename"),
                  cl::desc("File to append stack analysis output to"), cl::Hidden);

namespace {
  class StackFeedback : public MachineFunctionPass {
    MachineFeedback *MFB;
    MachineFrameInfo *MFI;
    std::map<int,int> SlotClass;
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

    void analyzeStackAccesses(MachineFunction &MF);
    raw_ostream *createOutputFile();

    enum SlotClasses {
      SLOT_FIXED = 0,
      SLOT_SPILL,
      SLOT_TEMP,
      SLOT_VAR,
      SLOT_LAST
    };
  };
} // end anonymous namespace

char StackFeedback::ID = 0;

INITIALIZE_PASS_BEGIN(StackFeedback, "stack-feedback",
                "Stack info feedback pass", false, false)
//INITIALIZE_PASS_DEPENDENCY(SlotIndexes)
INITIALIZE_PASS_END(StackFeedback, "stack-feedback",
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
      SlotClass[i] = SLOT_VAR;
    } else if (MFI->isFixedObjectIndex(i)) {
      ++NumFixed; // don't add to stack size
      SlotClass[i] = SLOT_FIXED;
      continue;
    } else if (MFI->isSpillSlotObjectIndex(i)) {
      ++NumSpills;
      SlotClass[i] = SLOT_SPILL;
    } else if (MFI->isTemporaryObjectIndex(i)) {
      ++NumTemps;
      SlotClass[i] = SLOT_TEMP;
    }

    StackSize += sz;
  }

  MFB->getStackInfo()->StackSizes[MF.getFunction()] = StackSize;

  analyzeStackAccesses(MF);

  return false;
}

void StackFeedback::analyzeStackAccesses(MachineFunction &MF) {
  const TargetMachine &TM = MF.getTarget();
  const MachineMemOperand *MMO;
  int FI;

  // count stack access by class
  std::vector<int> SLoad(SLOT_LAST), SStore(SLOT_LAST);

  raw_ostream &OS = *createOutputFile();

  OS << "STATIC STACK ANALYSIS running on: " << MF.getFunction()->getName() << "\n";

  for (MachineFunction::iterator BB = MF.begin(), BBE = MF.end();
       BB != BBE; ++BB) {
    for (MachineBasicBlock::iterator MI = BB->begin(), ME = BB->end();
         MI != ME; ++MI) {
      FI = -999;
      if (TM.getInstrInfo()->hasLoadFromStackSlot(MI, MMO, FI)) {
        //if (MFI->isSpillSlotObjectIndex(FI))
        OS << "STACK LOAD [FI " << FI << "]: " << *MI;
        SLoad[SlotClass[FI]]++;
        continue;
      } else if (TM.getInstrInfo()->hasStoreToStackSlot(MI, MMO, FI)) {
        OS << "STACK STORE[FI " << FI << "]: " << *MI;
        SStore[SlotClass[FI]]++;
        continue;
      }

      for (MachineInstr::mmo_iterator o = MI->memoperands_begin(),
           oe = MI->memoperands_end(); o != oe; ++o) {
        if ((*o)->isLoad() && (*o)->getValue()) {
          OS << "LOAD: " << *MI;
          break;
        } else if ((*o)->isStore() && (*o)->getValue()) {
          OS << "STORE: " << *MI;
          break;
        }
      }
    }
  }
  OS << "=ssaa=" << "FIXED: " << SLoad[SLOT_FIXED] << " / " << SStore[SLOT_FIXED] << "\n";
  OS << "=ssaa=" << "SPILL: " << SLoad[SLOT_SPILL] << " / " << SStore[SLOT_SPILL] << "\n";
  OS << "=ssaa=" << "TEMP: " << SLoad[SLOT_TEMP] << " / " << SStore[SLOT_TEMP] << "\n";
  OS << "=ssaa=" << "VAR: " << SLoad[SLOT_VAR] << " / " << SStore[SLOT_VAR] << "\n";
  delete &OS;   // Close the file.
}

raw_ostream *StackFeedback::createOutputFile() {
  const std::string &OutputFilename = SCAOutputFilename.getValue();
  if (OutputFilename.empty())
    return new raw_fd_ostream(2, false); // stderr.
  if (OutputFilename == "-")
    return new raw_fd_ostream(1, false); // stdout.
  
  // Append mode is used because the info output file is opened and closed
  // each time -stats or -time-passes wants to print output to it. To
  // compensate for this, the test-suite Makefiles have code to delete the
  // info output file before running commands which write to it.
  std::string Error;
  raw_ostream *Result = new raw_fd_ostream(OutputFilename.c_str(),
                                           Error, raw_fd_ostream::F_Append);
  if (Error.empty())
    return Result;
  
  errs() << "Error opening sca-output-file '"
    << OutputFilename << " for appending!\n";
  delete Result;
  return new raw_fd_ostream(2, false); // stderr.
}
