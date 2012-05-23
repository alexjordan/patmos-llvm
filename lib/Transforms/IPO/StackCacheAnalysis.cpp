//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "sca"
#include "llvm/Module.h"
#include "llvm/Analysis/CallSSA.h"
#include "llvm/Analysis/StackCache.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO.h"

using namespace llvm;
using namespace cssa;
using namespace boost;

namespace {

  class StackCacheAnalysis : public ModulePass {
  public:
    StackCacheAnalysis(SCStackInfo *SCSI = NULL) : ModulePass(ID) {
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

char StackCacheAnalysis::ID = 0;
INITIALIZE_PASS_BEGIN(StackCacheAnalysis, "scanalyze",
                "Stack Cache Analysis", true, false)
INITIALIZE_PASS_DEPENDENCY(CallSSA)
INITIALIZE_PASS_END(StackCacheAnalysis, "scanalyze",
                "Stack Cache Analysis", true, false)

// this pass is meant to be created by a special 'sca' tool only, it won't
// work as an 'opt' pass.
ModulePass *llvm::createStackCacheAnalysisPass(SCStackInfo *SCSI) {
  return new StackCacheAnalysis(SCSI);
}


bool StackCacheAnalysis::runOnModule(Module &M) {
  errs() << "FOO Stack cache opt\n";
  CallSSA &CS = getAnalysis<CallSSA>();
  graph_t G = CS.getGraph();
  DEBUG(dbgs() << "#nodes: " << num_vertices(G) << "\n");
  DEBUG(dbgs() << "#edges: " << num_edges(G) << "\n");

  //cssa::View(G, "foo");

  return true;
}

void SCStackInfo::dump() const {
  dbgs() << "Stack size per function:\n";
  for (std::map<const Function*, uint64_t>::const_iterator I = StackSizes.begin(),
       E = StackSizes.end(); I != E; ++I)
    dbgs() << I->first->getName() << ": " << I->second << "\n";
}
