//======-- PatmosFrameLowering.cpp - Patmos Frame Information -------=========//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file contains the Patmos implementation of TargetFrameLowering class.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "patmos-framelowering"
#include "PatmosFrameLowering.h"
#include "PatmosInstrInfo.h"
#include "PatmosMachineFunctionInfo.h"
#include "PatmosSinglePathInfo.h"
#include "PatmosSubtarget.h"
#include "PatmosTargetMachine.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/RegisterScavenging.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/PtrUseVisitor.h"

#include <list>

using namespace llvm;

namespace llvm {
  /// Count the number of FIs overflowing into the shadow stack
  STATISTIC(FIsNotFitSC, "FIs that did not fit in the stack cache");
}

/// EnableStackCache - Command line option to disable the usage of the stack
/// cache (enabled by default).
static cl::opt<bool> DisableStackCache("mpatmos-disable-stack-cache",
                            cl::init(false),
                            cl::desc("Disable the use of Patmos' stack cache"));

/// DisableAlloca - Command line option to prevent static stack objects from
/// being allocated on the stack cache (enabled by default).
static cl::opt<bool> DisableAlloca("mpatmos-disable-alloca-on-sc",
                            cl::init(false), cl::Hidden,
                            cl::desc("Disable alloca stack cache allocation"));

namespace llvm {
class AllocaAnalysis : public PtrUseVisitor<AllocaAnalysis> {
  typedef PtrUseVisitor<AllocaAnalysis> Base;
public:
  std::vector<Value*> Visited;
  AllocaAnalysis(const DataLayout &DL)
      : Base(DL) {}

  void visit(Instruction *I) {
    Visited.push_back(I);
    Base::visit(I);
  }
  // entry to our analysis
  PtrInfo start(Instruction *I) {
    Visited.push_back(I);
    return Base::visitPtr(*I);
  }
  // XXX this might be a PtrUseVisitor issue.
  // we can escape through a var arg
  void visitVAArgInst(VAArgInst &VAI) {
    PI.setEscapedAndAborted(&VAI);
  }
  // XXX this might be a PtrUseVisitor issue.
  // don't stop at PHIs!
  void visitPHINode(PHINode &PHI) {
    enqueueUsers(PHI);
  }
  // XXX this might be a PtrUseVisitor issue.
  // select is similar to PHI!
  void visitSelectInst(SelectInst &SI) {
    enqueueUsers(SI);
  }

  bool hasVisited(const Value *V) const {
    return std::find(Visited.begin(), Visited.end(), V) != Visited.end();
  }
  void dumpVisited() const {
    dbgs() << "PatmosSC: alloca ptr analysis visited:\n";
    for (std::vector<Value*>::const_iterator I = Visited.begin(), E =
         Visited.end(); I != E; ++I)
      dbgs() << "  " << **I << "\n";
  }
};
}


PatmosFrameLowering::PatmosFrameLowering(const PatmosTargetMachine &tm)
: TargetFrameLowering(TargetFrameLowering::StackGrowsDown, 4, 0), TM(tm),
  STC(tm.getSubtarget<PatmosSubtarget>())
{
}



bool PatmosFrameLowering::hasFP(const MachineFunction &MF) const {
  const MachineFrameInfo *MFI = MF.getFrameInfo();

  // Naked functions should not use the stack, they do not get a frame pointer.
  if (MF.getFunction()->hasFnAttribute(Attribute::Naked))
    return false;

  return (MF.getTarget().Options.DisableFramePointerElim(MF) ||
          MF.getFrameInfo()->hasVarSizedObjects() ||
          MFI->isFrameAddressTaken());
}


#if 0
bool PatmosFrameLowering::hasReservedCallFrame(const MachineFunction &MF) const {
  return !MF.getFrameInfo()->hasVarSizedObjects();
}
#endif


static unsigned int align(unsigned int offset, unsigned int alignment) {
  return ((offset + alignment - 1) / alignment) * alignment;
}


void PatmosFrameLowering::assignFIsToStackCache(MachineFunction &MF,
                                                BitVector &SCFIs,
                                                AllocaInfoMap &AIM) const
{
  MachineFrameInfo &MFI = *MF.getFrameInfo();
  PatmosMachineFunctionInfo &PMFI = *MF.getInfo<PatmosMachineFunctionInfo>();
  const std::vector<CalleeSavedInfo> &CSI = MFI.getCalleeSavedInfo();
  const TargetRegisterInfo *TRI = TM.getRegisterInfo();
  const PatmosTargetLowering *TLI =
    static_cast<const PatmosTargetLowering *>(TM.getTargetLowering());

  assert(MFI.isCalleeSavedInfoValid());

  // find all FIs used for callee saved registers
  for(std::vector<CalleeSavedInfo>::const_iterator i(CSI.begin()),
      ie(CSI.end()); i != ie; i++)
  {
    if (i->getReg() == Patmos::S0 && PMFI.getS0SpillReg()) continue;
    // Predicates are handled via aliasing to S0. They appear here when we
    // skip assigning s0 to a stack slot, not really sure why.
    if (Patmos::PRegsRegClass.contains(i->getReg())) continue;
    SCFIs[i->getFrameIdx()] = true;
  }

  // RegScavenging register
  if (TRI->requiresRegisterScavenging(MF)) {
    SCFIs[PMFI.getRegScavengingFI()] = true;
  }

  // Spill slots / storage introduced for single path conversion
  const std::vector<int> &SinglePathFIs = PMFI.getSinglePathFIs();
  for(unsigned i=0; i<SinglePathFIs.size(); i++) {
    SCFIs[SinglePathFIs[i]] = true;
  }

  // find FIs that qualify for the stack cache
  for(unsigned FI = 0, FIe = MFI.getObjectIndexEnd(); FI != FIe; FI++) {
    if (MFI.isDeadObjectIndex(FI))
      continue;

    // find all spill slots and locations for callee saved registers
    if (MFI.isSpillSlotObjectIndex(FI)) {
      SCFIs[FI] = true;
      continue;
    }

    if (DisableAlloca)
      continue;

    // a local escape analysis can identify stack objects (ie. static allocas),
    // which can be allocated on the stack cache
    AllocaInst *AI = NULL;
    if ((AI = const_cast<AllocaInst*>(MFI.getObjectAllocation(FI)))) {
      AllocaAnalysis *ALA = new AllocaAnalysis(*TLI->getDataLayout());
      //DEBUG(dbgs() << "PatmosSC: candidate alloca: " << *AI << "\n");
      AllocaAnalysis::PtrInfo PtrI = ALA->start(const_cast<AllocaInst*>(AI));
      if (PtrI.isEscaped() || PtrI.isAborted()) {
        Instruction *escapee = PtrI.getEscapingInst() ? PtrI.getEscapingInst()
                                                      : PtrI.getAbortingInst();
        assert(escapee && "Did not track a bad instruction");
        DEBUG(dbgs() << "PatmosSC: alloca escapes @ " << *escapee << "\n");
      } else {
        DEBUG(dbgs() << "PatmosSC: alloca does not escape: " << *AI << "\n");
        SCFIs[FI] = true;
      }
      // pass analysis info (+ ownership) to outside or delete it now
      if (SCFIs[FI])
        AIM[FI] = ALA;
      else
        delete ALA;
    } // end if(alloca)
  } // end for

}

void PatmosFrameLowering::patchSCAccess(MachineFunction &MF,
                                        const AllocaAnalysis *ALA) const {
  const PatmosInstrInfo *PII =
    static_cast<const PatmosInstrInfo*>(TM.getInstrInfo());

  DEBUG(ALA->dumpVisited());
  for (MachineFunction::iterator I = MF.begin(), E =MF.end(); I != E; ++I) {
    for (MachineBasicBlock::iterator II = I->begin(), EE = I->end(); II
         != EE; ++II) {
      MachineInstr *MI = II;
      if (!MI->memoperands_empty()) {
        assert(MI->hasOneMemOperand());
        const MachineMemOperand *mmo = *II->memoperands_begin();
        const Value *v = mmo->getValue();
        if (!v || !ALA->hasVisited(v)) {
          continue;
        }

        DEBUG(dbgs() << "PatmosSC: needs SC rewrite? " << *MI);
        if (PII->hasStackFIUse(MI)) {
          DEBUG(dbgs() << "  " << *mmo << " .. refers to FI, okay.\n");
          continue;
        }
        DEBUG(dbgs() << "  " << *mmo
              << " .. points to SC, redirect mem type\n");
        unsigned scopc = PII->getSCOpcode(MI->getOpcode());
        const MCInstrDesc &newMCID = PII->get(scopc);
        MI->setDesc(newMCID);
        DEBUG(dbgs() << "  rewritten: " << *MI);
      }
    }
  }
}


unsigned PatmosFrameLowering::assignFrameObjects(MachineFunction &MF,
                                                 bool UseStackCache) const
{
  MachineFrameInfo &MFI = *MF.getFrameInfo();
  PatmosMachineFunctionInfo &PMFI = *MF.getInfo<PatmosMachineFunctionInfo>();
  unsigned maxFrameSize = MFI.getMaxCallFrameSize();
  unsigned sumSS = 0, sumSC = 0, sumSCFull = 0, sumULO = 0;

  // defaults to false (all objects are assigned to shadow stack)
  BitVector SCFIs(MFI.getObjectIndexEnd());

  AllocaInfoMap AIM;

  if (UseStackCache) {
    assignFIsToStackCache(MF, SCFIs, AIM);
  }

  // assign new offsets to FIs

  // next stack slot in stack cache
  unsigned int SCOffset = 0;
  // next stack slot in shadow stack
  // Also reserve space for the call frame if we do not use a frame pointer.
  // This must be in sync with PatmosRegisterInfo::eliminateCallFramePseudoInstr
  unsigned int SSOffset = (hasFP(MF) ? 0 : maxFrameSize);

  // reorder FIs s.t. alloca objects are the end of the FI worklist
  // XXX reverse FI-for keeps ordinary FIs in order
  // XXX think about additional sort/selection criteria for SC allocation
  std::list<unsigned> SortedFIs;
  for(int FI = MFI.getObjectIndexEnd() - 1; FI >= 0; FI--) {
    if (MFI.isDeadObjectIndex(FI))
      continue;

    if (MFI.getObjectAllocation(FI))
      SortedFIs.push_back(FI);
    else
      SortedFIs.push_front(FI);
  }

  DEBUG(dbgs() << "PatmosSC: " << MF.getFunction()->getName() << "\n");
  DEBUG(MFI.print(MF, dbgs()));

  // allocate FIs in sorted order
  for(std::list<unsigned>::iterator I = SortedFIs.begin(), E = SortedFIs.end();
      I != E; ++I) {
    unsigned FI = *I;
    unsigned FIalignment = MFI.getObjectAlignment(FI);
    int64_t FIsize = MFI.getObjectSize(FI);

    if (FIsize > INT_MAX) {
      report_fatal_error("Frame objects with size > INT_MAX not supported.");
    }

    // be sure to catch some special stack objects not expected for Patmos
    assert(!MFI.isFixedObjectIndex(FI) && !MFI.isObjectPreAllocated(FI));


    // assigned to stack cache or shadow stack?
    if (SCFIs[FI]) {
      // alignment
      unsigned int next_SCOffset = align(SCOffset, FIalignment);

      // what are you?
      bool isAlloca = MFI.getObjectAllocation(FI);

      // check if the FI still fits into the SC
      if (align(next_SCOffset + FIsize, STC.getStackCacheBlockSize()) <=
          STC.getStackCacheSize()) {
        DEBUG(dbgs() << "PatmosSC: FI: " << FI
              << (isAlloca ? "(alloca)" : "") << " on SC: "
              << next_SCOffset << "(size=" << FIsize << ")\n");

        // reassign stack offset
        MFI.setObjectOffset(FI, next_SCOffset);

        // reserve space on the stack cache
        SCOffset = next_SCOffset + FIsize;

        // statistics
        sumSC += FIsize;

        if (isAlloca) {
          assert(AIM.count(FI));
          patchSCAccess(MF, AIM[FI]);
        }

        // the FI is assigned to the SC, process next FI
        continue;
      }
      else {
        // the FI did not fit in the SC -- fall-through and put it on the 
        // shadow stack
        SCFIs[FI] = false;
        FIsNotFitSC++;
        sumSCFull += MFI.getObjectSize(FI);
      }
    }

    // assign the FI to the shadow stack
    {
      assert(!SCFIs[FI]);

      // alignment
      SSOffset = align(SSOffset, FIalignment);

      DEBUG(dbgs() << "PatmosSC: FI: " << FI << " on SS: " << SSOffset
                   << "(" << MFI.getObjectOffset(FI) << ")\n");
      if (FIsize >= STC.getStackCacheSize() / 2)
        sumULO += FIsize;
      else
        sumSS += FIsize;

      // reassign stack offset
      MFI.setObjectOffset(FI, SSOffset);

      // reserve space on the shadow stack
      SSOffset += FIsize;
    }
  }

  // align stack frame on stack cache
  unsigned stackCacheSize = align(SCOffset, STC.getStackCacheBlockSize());

  assert(stackCacheSize <= STC.getStackCacheSize());

  // align shadow stack. call arguments are already included in SSOffset
  unsigned stackSize = align(SSOffset, getStackAlignment());

  // update offset of fixed objects
  for(unsigned FI = MFI.getObjectIndexBegin(), FIe = 0; FI != FIe; FI++) {
    // reassign stack offset
    MFI.setObjectOffset(FI, MFI.getObjectOffset(FI) + stackSize);
  }

  DEBUG(dbgs() << "scalloc:" << MF.getName()
    << "," << sumSC
    << "," << sumSS
    << "," << sumULO
    << "," << sumSCFull << "\n");

  // store assignment information
  PMFI.setStackCacheReservedBytes(stackCacheSize);
  PMFI.setStackCacheFIs(SCFIs);

  PMFI.setStackReservedBytes(stackSize);
  MFI.setStackSize(stackSize);

  // clean up
  for (AllocaInfoMap::iterator I = AIM.begin(), E = AIM.end(); I != E; ++I)
    delete I->second;

  return stackSize;
}



void PatmosFrameLowering::emitSTC(MachineFunction &MF, MachineBasicBlock &MBB,
                                  MachineBasicBlock::iterator &MI,
                                  unsigned Opcode) const {
  PatmosMachineFunctionInfo &PMFI = *MF.getInfo<PatmosMachineFunctionInfo>();

  // align the stack cache frame size
  unsigned alignedStackSize = STC.getAlignedStackFrameSize(
                                     PMFI.getStackCacheReservedBytes());
  // STC instructions are specified in words
  unsigned stackFrameSize = alignedStackSize / 4;

  if (stackFrameSize) {
    assert(isUInt<22>(stackFrameSize) && "Stack cache size exceeded.");

    DebugLoc DL = (MI != MBB.end()) ? MI->getDebugLoc() : DebugLoc();

    const TargetInstrInfo &TII = *TM.getInstrInfo();

    // emit reserve instruction
    AddDefaultPred(BuildMI(MBB, MI, DL, TII.get(Opcode)))
      .addImm(stackFrameSize);
  }
}

void PatmosFrameLowering::patchCallSites(MachineFunction &MF) const {
  // visit all basic blocks
  for (MachineFunction::iterator i(MF.begin()), ie(MF.end()); i != ie; ++i) {
    for (MachineBasicBlock::iterator j(i->begin()), je=(i->end()); j != je;
         j++) {
      // a call site?
      if (j->isCall()) {
        MachineBasicBlock::iterator p(llvm::next(j));
        emitSTC(MF, *i, p, Patmos::SENSi);
      }
    }
  }
}




void PatmosFrameLowering::emitPrologue(MachineFunction &MF) const {
  // get some references
  MachineBasicBlock &MBB     = MF.front();
  MachineFrameInfo *MFI      = MF.getFrameInfo();
  const TargetInstrInfo *TII = TM.getInstrInfo();

  MachineBasicBlock::iterator MBBI = MBB.begin();
  DebugLoc dl = MBBI != MBB.end() ? MBBI->getDebugLoc() : DebugLoc();

  //----------------------------------------------------------------------------
  // Handle the stack cache -- if enabled.

  if (MFI->getMaxAlignment() > 4) {
    dbgs() << "Stack alignment ";
    if (MF.getFunction()) dbgs() << "in " << MF.getFunction()->getName() << " ";
    dbgs() << "too large (" << MFI->getMaxAlignment() << ").\n";

    report_fatal_error("Stack alignment other than 4 byte is not supported");
  }

  // assign some FIs to the stack cache if possible
  unsigned stackSize = assignFrameObjects(MF, !DisableStackCache);

  if (!DisableStackCache) {
    // emit a reserve instruction
    emitSTC(MF, MBB, MBBI, Patmos::SRESi);

    // patch all call sites
    patchCallSites(MF);
  }

  //----------------------------------------------------------------------------
  // Handle the shadow stack


  // Do we need to allocate space on the stack?
  if (stackSize) {
    // adjust stack : sp -= stack size
    if (stackSize <= 0xFFF) {
      AddDefaultPred(BuildMI(MBB, MBBI, dl, TII->get(Patmos::SUBi), Patmos::RSP))
        .addReg(Patmos::RSP).addImm(stackSize);
    }
    else {
      AddDefaultPred(BuildMI(MBB, MBBI, dl, TII->get(Patmos::SUBl), Patmos::RSP))
        .addReg(Patmos::RSP).addImm(stackSize);
    }
  }

}

void PatmosFrameLowering::emitEpilogue(MachineFunction &MF,
                                       MachineBasicBlock &MBB) const {
  MachineBasicBlock::iterator MBBI = MBB.getLastNonDebugInstr();
  MachineFrameInfo *MFI            = MF.getFrameInfo();
  const TargetInstrInfo *TII       = TM.getInstrInfo();
  DebugLoc dl                      = MBBI->getDebugLoc();

  //----------------------------------------------------------------------------
  // Handle Stack Cache

  // emit a free instruction
  emitSTC(MF, MBB, MBBI, Patmos::SFREEi);

  //----------------------------------------------------------------------------
  // Handle Shadow Stack

  // Get the number of bytes from FrameInfo
  unsigned stackSize = MFI->getStackSize();

  // adjust stack  : sp += stack size
  if (stackSize) {
    if (stackSize <= 0xFFF) {
      AddDefaultPred(BuildMI(MBB, MBBI, dl, TII->get(Patmos::ADDi),
                             Patmos::RSP))
        .addReg(Patmos::RSP).addImm(stackSize);
    }
    else {
      AddDefaultPred(BuildMI(MBB, MBBI, dl, TII->get(Patmos::ADDl),
                             Patmos::RSP))
        .addReg(Patmos::RSP).addImm(stackSize);
    }
  }
}

void PatmosFrameLowering::processFunctionBeforeCalleeSavedScan(
                                  MachineFunction& MF, RegScavenger* RS) const {

  const TargetInstrInfo *TII = TM.getInstrInfo();
  const TargetRegisterInfo *TRI = TM.getRegisterInfo();
  MachineRegisterInfo &MRI = MF.getRegInfo();
  MachineFrameInfo &MFI = *MF.getFrameInfo();
  PatmosMachineFunctionInfo &PMFI = *MF.getInfo<PatmosMachineFunctionInfo>();

  // Insert instructions at the beginning of the entry block;
  // callee-saved-reg spills are inserted at front afterwards
  MachineBasicBlock &EntryMBB = MF.front();

  DebugLoc DL;

  // Do not emit anything for naked functions
  if (MF.getFunction()->hasFnAttribute(Attribute::Naked)) {
    return;
  }

  if (hasFP(MF)) {
    // if framepointer enabled, set it to point to the stack pointer.
    // Set frame pointer: FP = SP
    AddDefaultPred(BuildMI(EntryMBB, EntryMBB.begin(), DL,
          TII->get(Patmos::MOV), Patmos::RFP)).addReg(Patmos::RSP);
    // Mark RFP as used
    MRI.setPhysRegUsed(Patmos::RFP);
  }

  // load the current function base if it needs to be passed to call sites
  if (MFI.hasCalls()) {
    // If we have calls, we need to spill the call link registers
    MRI.setPhysRegUsed(Patmos::SRB);
    MRI.setPhysRegUsed(Patmos::SRO);
  } else {
    MRI.setPhysRegUnused(Patmos::SRB);
    MRI.setPhysRegUnused(Patmos::SRO);
  }

  // mark all predicate registers as used, for single path support
  // S0 is saved/restored as whole anyway
  if (PatmosSinglePathInfo::isEnabled(MF)) {
    MRI.setPhysRegUsed(Patmos::S0);
    MRI.setPhysRegUsed(Patmos::R26);
  }

  // If we need to spill S0, try to find an unused scratch register that we can
  // use instead. This only works if we do not have calls that may clobber
  // the register though.
  // It also makes no sense if we single-path convert the function,
  // because the SP converter introduces spill slots anyway.
  if (MRI.isPhysRegUsed(Patmos::S0) && !MF.getFrameInfo()->hasCalls()
      && !PatmosSinglePathInfo::isEnabled(MF)) {
    unsigned SpillReg = 0;
    BitVector Reserved = MRI.getReservedRegs();
    BitVector CalleeSaved(TRI->getNumRegs());
    const uint16_t *saved = TRI->getCalleeSavedRegs(&MF);
    while (*saved) {
      CalleeSaved.set(*saved++);
    }
    for (TargetRegisterClass::iterator i = Patmos::RRegsRegClass.begin(),
         e = Patmos::RRegsRegClass.end(); i != e; ++i) {
      if (MRI.isPhysRegUsed(*i) || *i == Patmos::R9) continue;
      if (Reserved[*i] || CalleeSaved[*i]) continue;
      SpillReg = *i;
      break;
    }
    if (SpillReg) {
      // Remember the register for the prologe-emitter and mark as used
      PMFI.setS0SpillReg(SpillReg);
      MRI.setPhysRegUsed(SpillReg);
    }
  }

  if (TRI->requiresRegisterScavenging(MF)) {
    const TargetRegisterClass *RC = &Patmos::RRegsRegClass;
    int fi = MFI.CreateStackObject(RC->getSize(), RC->getAlignment(), false);
    RS->addScavengingFrameIndex(fi);
    PMFI.setRegScavengingFI(fi);
  }
}

bool
PatmosFrameLowering::spillCalleeSavedRegisters(MachineBasicBlock &MBB,
                                      MachineBasicBlock::iterator MI,
                                      const std::vector<CalleeSavedInfo> &CSI,
                                      const TargetRegisterInfo *TRI) const {
  if (CSI.empty())
    return false;

  DebugLoc DL;
  if (MI != MBB.end()) DL = MI->getDebugLoc();

  MachineFunction &MF = *MBB.getParent();
  const TargetInstrInfo &TII = *TM.getInstrInfo();
  PatmosMachineFunctionInfo &PMFI =
                       *MF.getInfo<PatmosMachineFunctionInfo>();

  unsigned spilledSize = 0;
  for (unsigned i = CSI.size(); i != 0; --i) {
    unsigned Reg = CSI[i-1].getReg();
    // Add the callee-saved register as live-in. It's killed at the spill.
    MBB.addLiveIn(Reg);

    // as all PRegs are aliased with S0, a spill of a Preg will cause
    // a spill of S0
    if (Patmos::PRegsRegClass.contains(Reg))
      continue;

    // Spill S0 to a register instead to a slot if there is a free register
    if (Reg == Patmos::S0 && PMFI.getS0SpillReg()) {
      TII.copyPhysReg(MBB, MI, DL, PMFI.getS0SpillReg(), Reg, true);
      prior(MI)->setFlag(MachineInstr::FrameSetup);
      continue;
    }

    // copy to R register first, then spill
    if (Patmos::SRegsRegClass.contains(Reg)) {
      TII.copyPhysReg(MBB, MI, DL, Patmos::R9, Reg, true);
      prior(MI)->setFlag(MachineInstr::FrameSetup);
      Reg = Patmos::R9;
    }

    // spill
    const TargetRegisterClass *RC = TRI->getMinimalPhysRegClass(Reg);
    TII.storeRegToStackSlot(MBB, MI, Reg, true,
        CSI[i-1].getFrameIdx(), RC, TRI);
    prior(MI)->setFlag(MachineInstr::FrameSetup);

    // increment spilled size
    spilledSize += 4;
  }

  return true;
}

bool
PatmosFrameLowering::restoreCalleeSavedRegisters(MachineBasicBlock &MBB,
                                        MachineBasicBlock::iterator MI,
                                        const std::vector<CalleeSavedInfo> &CSI,
                                        const TargetRegisterInfo *TRI) const {
  if (CSI.empty())
    return false;

  DebugLoc DL;
  if (MI != MBB.end()) DL = MI->getDebugLoc();

  MachineFunction &MF = *MBB.getParent();
  const TargetInstrInfo &TII = *TM.getInstrInfo();
  PatmosMachineFunctionInfo &PMFI = *MF.getInfo<PatmosMachineFunctionInfo>();

  // if framepointer enabled, first restore the stack pointer.
  if (hasFP(MF)) {
    // Restore stack pointer: SP = FP
    AddDefaultPred(BuildMI(MBB, MI, DL, TII.get(Patmos::MOV), Patmos::RSP))
      .addReg(Patmos::RFP);
  }

  // restore the callee saved registers
  for (unsigned i = CSI.size(); i != 0; --i) {
    unsigned Reg = CSI[i-1].getReg();
    unsigned tmpReg = Reg;

    // SZ is aliased with PRegs
    if (Patmos::PRegsRegClass.contains(Reg))
        continue;

    // Spill S0 to a register instead to a slot if there is a free register
    if (Reg == Patmos::S0 && PMFI.getS0SpillReg()) {
      TII.copyPhysReg(MBB, MI, DL, Reg, PMFI.getS0SpillReg(), true);
      prior(MI)->setFlag(MachineInstr::FrameSetup);
      continue;
    }

    // copy to special register after reloading
    if (Patmos::SRegsRegClass.contains(Reg))
      tmpReg = Patmos::R9;

    // load
    const TargetRegisterClass *RC = TRI->getMinimalPhysRegClass(tmpReg);
    TII.loadRegFromStackSlot(MBB, MI, tmpReg, CSI[i-1].getFrameIdx(), RC, TRI);
    prior(MI)->setFlag(MachineInstr::FrameSetup);

    // copy, if needed
    if (tmpReg != Reg)
    {
      TII.copyPhysReg(MBB, MI, DL, Reg, tmpReg, true);
      prior(MI)->setFlag(MachineInstr::FrameSetup);
    }
  }

  return true;
}

void PatmosFrameLowering::
eliminateCallFramePseudoInstr(MachineFunction &MF, MachineBasicBlock &MBB,
                              MachineBasicBlock::iterator I) const {
  const TargetInstrInfo &TII = *TM.getInstrInfo();

  // We need to adjust the stack pointer here (and not in the prologue) to
  // handle alloca instructions that modify the stack pointer before ADJ*
  // instructions. We only need to do that if we need a frame pointer, otherwise
  // we reserve size for the call stack frame in FrameLowering in the prologue.
  if (TM.getFrameLowering()->hasFP(MF)) {
    MachineInstr &MI = *I;
    DebugLoc dl = MI.getDebugLoc();
    int Size = MI.getOperand(0).getImm();
    unsigned Opcode;
    if (MI.getOpcode() == Patmos::ADJCALLSTACKDOWN) {
      Opcode = (Size <= 0xFFF) ? Patmos::SUBi : Patmos::SUBl;
    }
    else if (MI.getOpcode() == Patmos::ADJCALLSTACKUP) {
      Opcode = (Size <= 0xFFF) ? Patmos::ADDi : Patmos::ADDl;
    }
    else {
        llvm_unreachable("Unsupported pseudo instruction.");
    }
    if (Size)
      AddDefaultPred(BuildMI(MBB, I, dl, TII.get(Opcode), Patmos::RSP))
                                                  .addReg(Patmos::RSP)
                                                  .addImm(Size);
  }
  // erase the pseudo instruction
  MBB.erase(I);
}


