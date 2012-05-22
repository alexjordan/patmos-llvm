//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/CallSSA.h"
#include "llvm/Assembly/Writer.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/PassManager.h"

#include <stack>
#include "boost/foreach.hpp"

using namespace llvm;
using namespace cssa;
using namespace boost;

char CallSSA::ID = 0;
INITIALIZE_PASS_BEGIN(CallSSA, "callssa",
                "Interprocedural control flow with calls", true, true)
INITIALIZE_AG_DEPENDENCY(CallGraph)
INITIALIZE_PASS_END(CallSSA, "callssa",
                "Interprocedural control flow with calls", true, true)

bool CallSSA::runOnModule(Module &m) {
  CallGraph& CG = getAnalysis<CallGraph>();

  typedef CallGraphNode CGN;
  typedef GraphTraits<CallGraphNode*> CGT;
  CGN *root = CG.getRoot();
  assert(root->getFunction());
  //root->getFunction()->dump();

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
        continue;
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
    bool children = false;

    for (CGT::ChildIteratorType I = CGT::child_begin(cgn),
         E = CGT::child_end(cgn); I != E; ++I) {
      CGN *succ = *I;
      if (Seen.count(succ))
        continue;
      if (succ == CG.getExternalCallingNode()) {
        DEBUG(dbgs() << "skipping ext-node\n");
        continue;
      }
      if (succ->getFunction()->isDeclaration()) {
        DEBUG(dbgs() << "skipping function declaration\n");
        continue;
      }
      Stack.push(succ);
      children = true;
    }
    if (!children) {
      cgn->dump();
      Seen.insert(cgn);
      Stack.pop();
      runOnFunction(*cgn->getFunction());
    }
  }

  return false;
}

bool CallSSA::runOnFunction(Function &F) {
  // the source function
  DominatorTree &DT = getAnalysis<DominatorTree>(F);

  // backedges in the source function
  typedef std::pair<const BasicBlock*, const BasicBlock*> Edge_t;
  SmallVector<Edge_t, 32> BEs;
  FindFunctionBackedges(F, BEs);

  LLVMContext &C = getGlobalContext();
  Module *M = new Module("callSSA", getGlobalContext());
  Type *chainType = IntegerType::get(C, 32);

  Constant *c = M->getOrInsertFunction("cSSA_main", chainType, NULL);
  Function *newF = cast<Function>(c);

  std::map<const BasicBlock*, BasicBlock*> BBmap;

  // create all blocks and map them to the original ones
  BOOST_FOREACH(const BasicBlock &rBB,
                std::make_pair(F.begin(), F.end())) {
    const BasicBlock *BB = &rBB;
    BasicBlock *newBB = BasicBlock::Create(C, BB->getName(), newF);
    BBmap[BB] = newBB;
  }

  // the entry gets the alloca'd variable for the call chain
  Value *Chain;
  {
  IRBuilder<> bld(&newF->getEntryBlock());
  Chain = bld.CreateAlloca(chainType, 0, "chain.addr");
  }

  // backedges need to be processed separately
  std::list<Use*> BEUses;

  // populate all blocks with calls and control flow
  BOOST_FOREACH(const BasicBlock &rBB,
                std::make_pair(F.begin(), F.end())) {
    const BasicBlock *BB = &rBB;
    BasicBlock *newBB = BBmap[BB];
    IRBuilder<> bld(newBB);

    convertCalls(newBB, BB, Chain);

    const Instruction *TI = BB->getTerminator();

    // create a use by returning the chain at every return
    if (isa<ReturnInst>(TI)) {
      Value *v = bld.CreateLoad(Chain, "chain.ret");
      bld.CreateRet(v);
      continue;
    }

    // clone and remap branches
    const BranchInst *BI = dyn_cast<BranchInst>(TI);
    assert(BI);
    Instruction *I = BI->clone();
    BOOST_FOREACH(Use &U, std::make_pair(I->op_begin(), I->op_end())) {
      if (BasicBlock *dst = dyn_cast<BasicBlock>(U.get())) {
        // redirect branch to block in the new function
        BasicBlock *mappedDst = BBmap[dst];

        // unwind backedges
        Edge_t e = std::make_pair(BB, dst);
        if (std::find(BEs.begin(), BEs.end(), e) != BEs.end()) {
          errs() << "BE head: " << dst->getName() << "\n";
          const BranchInst *BI = dyn_cast<BranchInst>(dst->getTerminator());
          assert(BI && BI->isConditional());
          BasicBlock *loopSucc = BI->getSuccessor(0);
          BasicBlock *exitSucc = BI->getSuccessor(1);
          if (!DT.dominates(loopSucc, BB))
            std::swap(loopSucc, exitSucc);
          assert(DT.dominates(loopSucc, BB));
          errs() << "BE: " << loopSucc->getName() << " dominates loop source\n";
          mappedDst = BBmap[exitSucc];
        }

        errs() << "redirecting from: " << U.get()->getName();
        errs() << " to: " << mappedDst->getName() << "\n";
        U.set(mappedDst);
      } else {
        U.set(UndefValue::get(bld.getInt1Ty()));
      }
    }
    newBB->getInstList().push_back(I);
  }

  FunctionPassManager FPM(M);
  FPM.add(createPromoteMemoryToRegisterPass());
  FPM.run(*newF);

  M->dump();


  // translate result to graph
  graph_t graph;
  translate(graph, *newF);
  View(graph, F.getName());

  delete M;
  return false;
}

optional<node_prop_t> CallSSA::translateInst(Instruction *I) const {
  switch (I->getOpcode()) {
  case Instruction::Call:
    break;
  default:
    return optional<node_prop_t>();
  }
  node_prop_t np;
  assert(CallMap.count(I));
  np.func = CallMap.find(I)->second;
  return optional<node_prop_t>(np);
}

void CallSSA::translate(graph_t &G, Function &F) {
  std::map<Instruction*, vertex_t> instMap;
  std::map<BasicBlock*, vertex_t> bbMap;

  vertex_t s = add_vertex(node_prop_t("s"), G);
  vertex_t t = add_vertex(node_prop_t("t"), G);

  std::list<std::pair<BasicBlock*, vertex_t> > Worklist;
  Worklist.push_back(std::make_pair(&F.getEntryBlock(), s));
  while (Worklist.size()) {
    BasicBlock *BB;
    vertex_t v;
    boost::tie(BB,v) = Worklist.front();
    Worklist.pop_front();

    if (bbMap.count(BB)) {
      add_edge(v, bbMap[BB], G);
      continue;
    }

    BOOST_FOREACH(Instruction &I, std::make_pair(BB->begin(), BB->end())) {
      optional<node_prop_t> node = translateInst(&I);
      if (node) {
        vertex_t u = v;
        v = add_vertex(*node, G);
        add_edge(u,v, G);
        instMap[&I] = v;
        if (!bbMap.count(BB))
          bbMap[BB] = v;
      }
    }
    TerminatorInst *TI = BB->getTerminator();
    if (isa<ReturnInst>(TI))
      add_edge(v, t, G);

    for (succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
      assert(*SI != BB && "self loop?");
      Worklist.push_back(std::make_pair(*SI, v));
    }
  }
}


Constant *getChainFunction(ImmutableCallSite &CS, Module *M) {
  LLVMContext &C = M->getContext();
  std::string name = "call.";
  name += CS.getCalledValue()->getName();
  Constant *cf = M->getOrInsertFunction(name,
                                        IntegerType::get(C, 32), /* ret i32 */
                                        IntegerType::get(C, 32), /* arg i32 */
                                        NULL);
  return cf;
}

void CallSSA::convertCalls(BasicBlock *dst, const BasicBlock *src,
                           Value *chain) {
   IRBuilder<> bld(dst);
   Module *M = dst->getParent()->getParent();
   for (BasicBlock::const_iterator I = src->begin(), E = src->end();
        I != E; ++I) {
     ImmutableCallSite CS(I);
     if (!CS.isCall())
       continue;
     // load previous chain
     Value *u = bld.CreateLoad(chain, "chain.reload");
     // call with chain as argument
     Value *v = bld.CreateCall(getChainFunction(CS, M), u, "chain");
     // store returned chain value
     bld.CreateStore(v, chain);
     // keep a mapping of call functions
     assert(CS.getCalledFunction());
     CallMap[v] = CS.getCalledFunction();
   }
}

