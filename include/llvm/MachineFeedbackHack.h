//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_MACHINE_FEEDBACK_HACK_H
#define LLVM_MACHINE_FEEDBACK_HACK_H

namespace llvm {
  class SCStackInfo;

  class MachineFeedback {
    SCStackInfo *SCSI;
  public:
    MachineFeedback();
    virtual ~MachineFeedback();
    SCStackInfo *getStackInfo() { return SCSI; }
    void dump() const;
  };
} // End llvm namespace

#endif
