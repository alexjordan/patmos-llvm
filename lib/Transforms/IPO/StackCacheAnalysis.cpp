//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "sca"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/CallSSA.h"
#include "llvm/Analysis/StackCache.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Module.h"

#include <stack>
#include "boost/foreach.hpp"

using namespace llvm;
using namespace cssa;
using namespace boost;

namespace {

  struct StackSize {
    uint64_t sz;
    StackSize(uint64_t s = 0) : sz(s) {}
    friend StackSize operator+ (const StackSize &LHS, const StackSize &RHS);
  };

  raw_ostream& operator<<(raw_ostream &os, const StackSize &ss);


  typedef CallGraphNode CGN;
  typedef std::map<CGN*, StackSize> maxstack_t;

  class StackCacheAnalysis : public ModulePass {
    SCStackInfo *SCSI;
    maxstack_t MaxStack;
  public:
    StackCacheAnalysis(SCStackInfo *scsi = NULL)
      : ModulePass(ID), SCSI(scsi) {
      initializeStackCacheOptPass(*PassRegistry::getPassRegistry());
    }
    static char ID; // Pass identification, replacement for typeid

    bool runOnModule(Module &M);

    void bottomUp(Module &M);

    void getAnalysisUsage(AnalysisUsage& AU) const {
      AU.addRequired<CallSSA>();
      AU.addRequired<CallGraph>();
      AU.setPreservesAll();
    }

    static const uint64_t unlimited;
  };
}

// Implement std::max
namespace std {
  inline StackSize
  max(StackSize &LHS, StackSize &RHS) {
    return StackSize(max(LHS.sz, RHS.sz));
  }
}

const uint64_t StackCacheAnalysis::unlimited = std::numeric_limits<uint64_t>::max();

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
  //CallSSA &CS = getAnalysis<CallSSA>();
  //graph_t G = CS.getGraph();
  //DEBUG(dbgs() << "#nodes: " << num_vertices(G) << "\n");
  //DEBUG(dbgs() << "#edges: " << num_edges(G) << "\n");

  //cssa::View(G, "foo");
  bottomUp(M);

  return true;
}

void StackCacheAnalysis::bottomUp(Module &M) {
  CallGraph& CG = getAnalysis<CallGraph>();
  assert(SCSI);
  SCStackInfo::ssmap_t &StackSizes = SCSI->StackSizes;

  typedef GraphTraits<CallGraphNode*> CGT;
  CGN *root = CG.getRoot();
  assert(root->getFunction());

  typedef std::vector<CGN*> scc_t;
  std::vector<scc_t> SCCs;
  std::set<CGN*> Blacklist;
  for (scc_iterator<CallGraph*> I = scc_begin(&CG), E = scc_end(&CG); I != E;
       ++I) {
    scc_t &scc = *I;
    // check for recursive function
    if (scc.size() == 1) {
      CGN *cgn = scc.back();
      if (std::find(CGT::child_begin(cgn), CGT::child_end(cgn), cgn) !=
          CGT::child_end(cgn)) {
        DEBUG(dbgs() << cgn->getFunction()->getName()  << " is recursive\n");
        Blacklist.insert(cgn);
        MaxStack[cgn] = unlimited;
        continue;
      }
    // or recursive component
    } else {
      BOOST_FOREACH(CGN *cgn, scc) {
        DEBUG(dbgs() << cgn->getFunction()->getName()  << " is part of SCC\n");
        Blacklist.insert(cgn);
        MaxStack[cgn] = unlimited;
      }
    }
    DEBUG(dbgs() << "SCC #" << SCCs.size() << " (" << scc.size() << "):\n");
    SCCs.push_back(*I);
    BOOST_FOREACH(CGN *n, SCCs.back())
      DEBUG(n->dump());
  }

  // traversal
  std::stack<CGN*> Stack;
  std::set<CGN*> Seen(Blacklist);
  Stack.push(root);
  while (Stack.size()) {
    CGN *cgn = Stack.top();
    bool pendingChildren = false;

    for (CGT::ChildIteratorType I = CGT::child_begin(cgn),
         E = CGT::child_end(cgn); I != E; ++I) {
      CGN *succ = *I;
      if (Seen.count(succ))
        continue;
      if (succ == CG.getExternalCallingNode() ||
          succ == CG.getCallsExternalNode()) {
        DEBUG(dbgs() << "skipping ext-node\n");
        continue;
      }
      //if (succ->getFunction()->isDeclaration()) {
      //  DEBUG(dbgs() << "skipping function declaration\n");
      //  continue;
      //}
      Stack.push(succ);
      pendingChildren = true;
    }
    if (!pendingChildren) {
      cgn->dump();
      Seen.insert(cgn);
      Stack.pop();

      Function *func = cgn->getFunction();
      assert(func);
      if (func->isDeclaration()) {
        DEBUG(dbgs() << "function declaration '" << func->getName()
              << "' -> assuming stack size 0.\n");
        MaxStack[cgn] = 0;
        continue;
      }

      // figure maximum stack depth from children
      StackSize max = 0;
      for (CGT::ChildIteratorType I = CGT::child_begin(cgn),
           E = CGT::child_end(cgn); I != E; ++I) {
        CGN *child = *I;
        if (!MaxStack.count(child)) {
          errs() << "child max-stack missing for node:\n";
          child->dump();
          llvm_unreachable("bad traversal");
        }
        max = std::max(max, MaxStack[child]);
      }
      if (!StackSizes.count(cgn->getFunction())) {
        errs() << "stack size info missing for func: "
          << cgn->getFunction()->getName() << "\n";
        llvm_unreachable("missing stack info");
      }
      MaxStack[cgn] = max + StackSizes[cgn->getFunction()];
    }
  }

  dbgs() << "Max stack depth:\n";
  for (maxstack_t::const_iterator I = MaxStack.begin(),
       E = MaxStack.end(); I != E; ++I)
    dbgs() << I->first->getFunction()->getName() << ": " << I->second << "\n";
}

namespace {
inline StackSize operator+(const StackSize &LHS, const StackSize &RHS) {
  if (LHS.sz == StackCacheAnalysis::unlimited ||
      RHS.sz == StackCacheAnalysis::unlimited)
    return StackSize(StackCacheAnalysis::unlimited);
  return StackSize(LHS.sz + RHS.sz);
}

raw_ostream& operator<<(raw_ostream &OS, const StackSize &SS) {
  if (SS.sz == StackCacheAnalysis::unlimited)
    OS << "<unlimited>";
  else
    OS << SS.sz;
  return OS;
}
}

void SCStackInfo::dump() const {
  dbgs() << "Stack size per function:\n";
  for (std::map<const Function*, uint64_t>::const_iterator I = StackSizes.begin(),
       E = StackSizes.end(); I != E; ++I)
    dbgs() << I->first->getName() << ": " << I->second << "\n";
}
