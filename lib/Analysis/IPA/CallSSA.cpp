//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/CallSSA.h"
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Module.h"
#include "llvm/Assembly/Writer.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;

char CallSSA::ID = 0;
INITIALIZE_PASS_BEGIN(CallSSA, "callssa",
                "Interprocedural control flow with calls", true, true)
INITIALIZE_AG_DEPENDENCY(CallGraph)
INITIALIZE_PASS_END(CallSSA, "callssa",
                "Interprocedural control flow with calls", true, true)

bool CallSSA::runOnModule(Module &m) {
  errs() << "FOO CallSSA Analysis\n";
  CallGraph& CG = getAnalysis<CallGraph>();
  CG.dump();
  return false;
}

