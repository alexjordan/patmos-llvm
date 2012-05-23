//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/StackCache.h"
#include "llvm/MachineFeedbackHack.h"

using namespace llvm;

MachineFeedback::MachineFeedback() : SCSI(new SCStackInfo()) {}
MachineFeedback::~MachineFeedback() {
  delete SCSI;
}

void MachineFeedback::dump() const {
  SCSI->dump();
}
