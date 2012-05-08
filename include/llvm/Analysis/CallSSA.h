//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_CALLSSA_H
#define LLVM_ANALYSIS_CALLSSA_H

#include "llvm/ADT/SetVector.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Pass.h"

namespace llvm {

class CallSSA : public ModulePass {
public:
  static char ID; // Pass identification, replacement for typeid
  CallSSA() : ModulePass(ID) {
    initializeCallSSAPass(*PassRegistry::getPassRegistry());
  }

  /// run - This incorporates all types used by the specified module
  bool runOnModule(Module &M);

  /// getAnalysisUsage - We do not modify anything.
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<CallGraph>();
    AU.setPreservesAll();
  }

  void convertCalls(BasicBlock *dst, const BasicBlock *src, Value *Chain);


};

} // End llvm namespace

#endif
