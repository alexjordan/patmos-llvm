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
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/CallSSA.h"
#include "llvm/Assembly/Writer.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/CommandLine.h"
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
#include "llvm/Analysis/LoopPass.h"

#include <stack>
#include "boost/foreach.hpp"

#define VIEW(F, name) \
if (ViewLoopPeeling) { \
  dbgs() << (name) << "\n"; \
  (F).viewCFGOnly(); \
}


using namespace llvm;
using namespace cssa;
using namespace boost;

static cl::opt<bool> ViewLoopPeeling("view-sca-peeling", cl::Hidden,
    cl::desc("View a lot of intermediate graphs"));

STATISTIC(NumMultiExitLoops, "Number of multi-exit loops handled");

char CallSSA::ID = 0;
INITIALIZE_PASS_BEGIN(CallSSA, "callssa",
                "Interprocedural control flow with calls", true, true)
INITIALIZE_AG_DEPENDENCY(CallGraph)
INITIALIZE_PASS_END(CallSSA, "callssa",
                "Interprocedural control flow with calls", true, true)

struct LoopPeel : public LoopPass {
  static char ID; // Pass identification, replacement for typeid
  Value *Chain;
  std::map<Value*, const Function*> &CallMap;
  LoopPeel(Value *Chain, std::map<Value*, const Function*> &CM)
      : LoopPass(ID), Chain(Chain), CallMap(CM) {
    initializeLoopSimplifyPass(*PassRegistry::getPassRegistry());
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<PostDominatorTree>();
    AU.addRequired<LoopInfo>();
  }
  virtual bool runOnLoop(Loop *L, LPPassManager &LPM);

  void redirectBackedges(Loop *L, BasicBlock *target);
  void removeObsolete(Loop *L, BasicBlock *BB, PostDominatorTree *PDT);

  std::map<Loop*, SmallVector<BasicBlock*, 4> > ExitCheck;
};
char LoopPeel::ID = 0;
#if 0
INITIALIZE_PASS_BEGIN(LoopPeel, "loop-peel",
                "CallSSA loop peeling", true, false)
INITIALIZE_PASS_DEPENDENCY(PostDominatorTree)
INITIALIZE_PASS_DEPENDENCY(LoopInfo)
INITIALIZE_PASS_END(LoopPeel, "loop-peel",
                "CallSSA loop peeling", true, false)
#endif

struct LoopCheck : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid
  LoopCheck() : FunctionPass(ID) {}

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<LoopInfo>();
    AU.setPreservesAll();
  }
  virtual bool runOnFunction(Function &F) {
    LoopInfo &LI = getAnalysis<LoopInfo>();
    if (!LI.empty()) {
      dbgs() << "loops after transformation:\n";
      BOOST_FOREACH(Loop *L, std::make_pair(LI.begin(), LI.end()))
        L->dump();
      assert(0);
    }
    return false;
  }
};
char LoopCheck::ID = 0;

bool CallSSA::runOnModule(Module &m) {
#if 0
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
#endif
  return false;
}

static void removeSucc(BasicBlock *BB, BasicBlock *toRemove) {
  dbgs() << "rmove " << toRemove->getName() << " from " << BB->getName() << "\n";
  TerminatorInst *TI = BB->getTerminator();
  // find suitable successor
  BasicBlock *newSucc = NULL;
  int remIdx = -1;
  for (unsigned i = 0, e = TI->getNumSuccessors(); i < e; ++i) {
    if (TI->getSuccessor(i) == toRemove)
      remIdx = i;
    else
      newSucc = TI->getSuccessor(i);
  }
  assert(newSucc && "nothing found to reroute");
  if (remIdx >= 0)
    TI->setSuccessor(remIdx, newSucc);
}

static bool loopsize_greater(const Loop* left, const Loop *right) {
  return left->getLoopDepth() > right->getLoopDepth();
}

cssa::graph_t CallSSA::getGraph(const Function &F, Pass *P) {
  if (!F.size()) {
    IncompleteAnalysis = true;
    assert(false && "incomplete");
    return graph_t();
  }

  DominatorTree &DT = getAnalysis<DominatorTree>(*const_cast<Function*>(&F));
  PostDominatorTree &PDT = getAnalysis<PostDominatorTree>(*const_cast<Function*>(&F));
  LoopInfo &LI = getAnalysis<LoopInfo>(*const_cast<Function*>(&F));

  std::list<const Loop*> LoopInfoWalker(LI.begin(), LI.end());
  std::list<const Loop*> WL;
  while (LoopInfoWalker.size()) {
    const Loop *L = LoopInfoWalker.front();
    LoopInfoWalker.pop_front();
    if (L->getExitBlock() == 0)
      WL.push_back(L);
    LoopInfoWalker.insert(LoopInfoWalker.end(), L->begin(), L->end());
  }

  BOOST_FOREACH(const Loop *L, WL) {

    unsigned depth = L->getLoopDepth();
    L->dump();
    SmallVector<BasicBlock*, 4> Exits;
    L->getExitBlocks(Exits);
    BOOST_FOREACH(BasicBlock *E, Exits) {
      dbgs() << "E: " << E->getName() << "\n";
      assert(LI.getLoopDepth(E) <= depth);
    }
  }

  LLVMContext &C = getGlobalContext();
  Module *M = new Module("callSSA", getGlobalContext());
  Type *chainType = IntegerType::get(C, 32);

  Constant *c = M->getOrInsertFunction("cSSA_main", chainType, NULL);
  Function *newF = cast<Function>(c);

  typedef std::map<const BasicBlock*, BasicBlock*> bbmap_t;
  bbmap_t BBmap, WorkMap;

  // create all blocks and map them to the original ones
  BOOST_FOREACH(const BasicBlock &rBB,
                std::make_pair(F.begin(), F.end())) {
    const BasicBlock *BB = &rBB;
    BasicBlock *newBB = BasicBlock::Create(C, BB->getName(), newF);
    BBmap[BB] = newBB;
    WorkMap[BB] = newBB;
  }

  // the entry gets the alloca'd variable for the call chain
  Value *Chain;
  {
  IRBuilder<> bld(&newF->getEntryBlock());
  Chain = bld.CreateAlloca(chainType, 0, "chain.addr");
  }

#if 0
  dbgs() << "original F\n";
  F.viewCFGOnly();

  std::set<BasicBlock*> Obsolete;

  // handle loops (that need cloning) first
  std::list<const Loop*> LoopInfoWalker(LI.begin(), LI.end());
  std::list<const Loop*> WL;
  std::set<const Loop*> Done;
  //LoopInfoWalker.insert(LI.begin(), LI.end());
  while (LoopInfoWalker.size()) {
    const Loop *L = LoopInfoWalker.front();
    LoopInfoWalker.pop_front();
    if (L->getUniqueExitBlock() == 0)
      WL.push_back(L);
    LoopInfoWalker.insert(LoopInfoWalker.end(), L->begin(), L->end());
  }
  WL.sort(loopsize_greater);
  BOOST_FOREACH(const Loop *L, WL)
    L->dump();
  dbgs() << WL.size() << " loop(s)\n";

  std::map<const BasicBlock*, BasicBlock*> Headers;
  BOOST_FOREACH(const Loop *L, WL) {

    dbgs() << "multi-exit loop:\n";
    L->dump();
    ++NumMultiExitLoops;

    bbmap_t Newmap;
    const BasicBlock *header = L->getHeader();

    BasicBlock *newBB = BasicBlock::Create(C, header->getName() + ".hdr", newF);
    IRBuilder<> bld(newBB);
    bld.CreateBr(BBmap[header]);
    Headers[header] = BBmap[header];
    BBmap[header] = newBB;
    newF->viewCFGOnly();
  }
#endif

  // populate all blocks with calls and control flow
  BOOST_FOREACH(bbmap_t::value_type v, WorkMap) {
    const BasicBlock *BB = v.first;
    BasicBlock *newBB = v.second;
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

#if 0
        // loop-backedge?
        if (LI.isLoopHeader(dst) && LI[BB] == LI[dst]) {
          const Loop *L = LI[dst];
          if (const BasicBlock *uniqx = L->getUniqueExitBlock())
            mappedDst = BBmap[uniqx];
          else { // multi-exit
            mappedDst = BBmap[BB]; // self, block gets removed later

            // by removing the backedge, blocks that are post-dominated by it
            // also need to be removed. the point for cutting them off would be
            // the post-dom frontier, but LLVM does not have this (anymore).
            std::list<const DomTreeNode*> Walker;
            Walker.push_back(PDT.getNode(const_cast<BasicBlock*>(BB)));
            while (Walker.size()) {
              const DomTreeNode *DTN = Walker.front();
              Walker.pop_front();
              dbgs() << "obs: " << DTN->getBlock()->getName() << "\n";
              // mark as obsolete, remove later
              Obsolete.insert(BBmap[DTN->getBlock()]);
              Walker.insert(Walker.end(), DTN->begin(), DTN->end());
            }
          }
        }

#endif
        U.set(mappedDst);
      } else {
        U.set(UndefValue::get(bld.getInt1Ty()));
      }
    }
    newBB->getInstList().push_back(I);
  }

#if 0
  BOOST_FOREACH(const Loop *L, WL) {
    bbmap_t Lmap;
    BOOST_FOREACH(BasicBlock *BB,
                  std::make_pair(L->block_begin(), L->block_end())) {
      if (!Lmap.count(BB)) {
        BasicBlock *newBB = BasicBlock::Create(C, BB->getName() + ".dup", newF);
        Lmap[BB] = newBB;
      }
    }


    BOOST_FOREACH(bbmap_t::value_type v, Lmap) {

      const BasicBlock *BB = v.first;
      BasicBlock *newBB = v.second;

      IRBuilder<> bld(newBB);

      convertCalls(newBB, BB, Chain);
      const Instruction *TI = BB->getTerminator();
      assert(!isa<ReturnInst>(TI));
      const BranchInst *BI = dyn_cast<BranchInst>(TI);
      assert(BI);
      Instruction *I = BI->clone();
      BOOST_FOREACH(Use &U, std::make_pair(I->op_begin(), I->op_end())) {
        if (BasicBlock *dst = dyn_cast<BasicBlock>(U.get())) {
          BasicBlock *mappedDst;
          if (Headers.count(dst))
            mappedDst = Headers[dst];
          else if (Lmap.count(dst))
            mappedDst = Lmap[dst]; // stays inside the cloned loop
          else {
            // exit or backedge, connect to orig. exit or header
            mappedDst = BBmap[dst];
          }
          U.set(mappedDst);
        } else {
          U.set(UndefValue::get(bld.getInt1Ty()));
        }
      }
      newBB->getInstList().push_back(I);
    }
    newF->viewCFGOnly();

    // remove the loop placeholder, forwarding its users to the cloned header
    BasicBlock *OH = BBmap[L->getHeader()];
    for (Value::use_iterator UI = OH->use_begin(), UE = OH->use_end();
         UI != UE; ++UI)
      UI->replaceUsesOfWith(OH, Lmap[L->getHeader()]);
    OH->eraseFromParent();

    newF->viewCFGOnly();
    assert(false);
  }

  if (NumMultiExitLoops) {
    dbgs() << "after multi-exit cloning\n";
    newF->viewCFGOnly();
  }


  // XXX this only works only for a single obsoleted block per loop...
  BOOST_FOREACH(BasicBlock *O, Obsolete) {
    for (pred_iterator SI = pred_begin(O), SE = pred_end(O); SI != SE; ++SI) {
      if (!Obsolete.count(*SI)) // only the edges on the frontier need to go
        removeSucc(*SI, O);
    }
  }
  dbgs() << "after obsolete removal\n";
  newF->viewCFGOnly();
#endif

  VIEW(F, "orig");

  {
  FunctionPassManager FPM(M);
  FPM.add(new LoopPeel(Chain, CallMap)); // before reg2mem!
  FPM.add(createPromoteMemoryToRegisterPass());
  FPM.run(*newF);
  }

  M->dump();

  // are we actually loop free?
  {
  FunctionPassManager FPM(M);
  FPM.add(new LoopCheck());
  FPM.run(*newF);
  }

  // translate result to graph
  graph_t graph;
  translate(graph, *newF);
  graph[graph_bundle].F = &F;
  //cssa::View(graph, "foo");

  delete M;
  return graph;
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

struct RecursiveTranslate {
  typedef std::vector<vertex_t> vv_t;
  graph_t &G;
  std::map<BasicBlock*, vv_t> bbMap;
  CallSSA *CSSA;
  vertex_t t;

  RecursiveTranslate(graph_t &G, CallSSA *cssa) : G(G), CSSA(cssa) {}

  void preWalk(BasicBlock *Root) {
    std::set<BasicBlock*> Seen;
    std::list<BasicBlock*> WL;
    vv_t vv;
    vv.push_back(t);

    WL.push_back(Root);

    while (WL.size()) {
      BasicBlock *BB;
      BB = WL.front();
      WL.pop_front();

      if (Seen.count(BB))
        continue;
      Seen.insert(BB);

      if (BB->size() > 1)
        continue;
      else
        dbgs() << BB->getName() << " is empty\n";

      bbMap[BB] = vv;
      for (pred_iterator SI = pred_begin(BB), SE = pred_end(BB); SI != SE; ++SI) {
        if (!Seen.count(*SI))
          WL.push_back(*SI);
      }
    }
  }


  vv_t getVertex(BasicBlock *BB) {
    if (bbMap.count(BB))
      return bbMap[BB];

    bool hasNode = false;
    vertex_t f, v;
    BasicBlock::InstListType &IL = BB->getInstList();
    BOOST_FOREACH(Instruction &I, std::make_pair(IL.rbegin(), IL.rend())) {
      optional<node_prop_t> node = CSSA->translateInst(&I);
      if (node) {
        vertex_t u = add_vertex(*node, G);
        if (hasNode) {
          add_edge(v,u,G);
        } else {
          f = u;
          hasNode = true;
        }
        v = u;
      }
    }
    //if (!hasNode) {
    //  node_prop_t np("foo");
    //  f = add_vertex(np, G);
    //  v = f;
    //}

    vv_t ff;
    if (hasNode)
      ff.push_back(f);

    for (succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
      assert(*SI != BB && "self loop?");
      BOOST_FOREACH(vertex_t u, getVertex(*SI))
        if (hasNode)
          add_edge(v, u, G);
        else
          ff.push_back(u);
    }

    TerminatorInst *TI = BB->getTerminator();
    if ((isa<ReturnInst>(TI))) {
      if (hasNode)
        add_edge(v,t,G);
      else
        ff.push_back(t);
    }

    bbMap[BB] = ff;
    return ff;
  }
};

void CallSSA::translate(graph_t &G, Function &F) {
  std::map<Instruction*, vertex_t> instMap;
  std::map<BasicBlock*, vertex_t> bbMap;

  vertex_t s = add_vertex(node_prop_t("s"), G);
  vertex_t t = add_vertex(node_prop_t("t"), G);
  G[graph_bundle].s = s;
  G[graph_bundle].t = t;

  RecursiveTranslate Rec(G, this);
  Rec.t = t;
  BOOST_FOREACH(BasicBlock &rBB, std::make_pair(F.begin(), F.end())) {
    BasicBlock *BB = &rBB;
    if (succ_begin(BB) == succ_end(BB)) {
      dbgs() << BB->getName() << " is root.\n";
      Rec.preWalk(BB);
      break;
    }
  }


  BOOST_FOREACH(vertex_t u, Rec.getVertex(&F.getEntryBlock()))
    add_edge(s,u,G);

#if 0
  std::set<BasicBlock*> Seen;
  typedef std::list<std::pair<BasicBlock*, vertex_t> > wl_t;;
  std::list<std::pair<BasicBlock*, vertex_t> > Worklist;

  // kick off (w/ entry node)
  Worklist.push_back(std::make_pair(&F.getEntryBlock(), s));

  while (Worklist.size()) {
    BasicBlock *BB;
    vertex_t v;
    boost::tie(BB,v) = Worklist.front();
    Worklist.pop_front();

    dbgs() << "cur: " << BB->getName() << "\n";
    dbgs() << "WL: ";
    BOOST_FOREACH(wl_t::value_type val, Worklist) {
      dbgs() << val.first->getName() << " ";
    }
    dbgs() << "\n";
    if (bbMap.count(BB)) {
      add_edge(v, bbMap[BB], G);
      continue;
    }

    //assert(Seen.count(BB) == 0);

    bool first = true;
    BasicBlock::InstListType &IL = BB->getInstList();
    BOOST_FOREACH(Instruction &I, std::make_pair(IL.rbegin(), IL.rend())) {
      optional<node_prop_t> node = translateInst(&I);
      if (node) {
        vertex_t u = add_vertex(*node, G);
        add_edge(v,u, G);
        instMap[&I] = u;
        if (first) {
          assert(!bbMap.count(BB));
          bbMap[BB] = u;
          first = false;
        }
        v = u;
      }
    }
    //TerminatorInst *TI = BB->getTerminator();
    //if (isa<ReturnInst>(TI))
    //  add_edge(v, t, G);

    // block has no node that could become its head, 
    //if (!bbMap.count(BB))
    //  bbMap[BB] = v;

    unsigned sz = Worklist.size();
    for (succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
      assert(*SI != BB && "self loop?");
      Worklist.push_front(std::make_pair(*SI, v));
    }

    // no succs?
    if (sz == Worklist.size()) {
      // we must be in the entry block then
      TerminatorInst *TI = BB->getTerminator();
      assert(isa<ReturnInst>(TI));
      add_edge(v,t,G);
    }
  }
#endif
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
  if (!cssa::convertCalls(dst, src, chain, CallMap)) {
     IncompleteAnalysis = true;
     assert(false && "incomplete");
  }
}

bool cssa::convertCalls(BasicBlock *dst, const BasicBlock *src,
                        Value *chain, std::map<Value*, const Function*> &CallMap) {
   IRBuilder<> bld(dst);
   Module *M = dst->getParent()->getParent();
   for (BasicBlock::const_iterator I = src->begin(), E = src->end();
        I != E; ++I) {
     ImmutableCallSite CS(I);
     if (!CS.isCall())
       continue;
     if (!CS.getCalledFunction()) {
       errs() << "unresolved call: " << *I << "\n";
       return false;
     }
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
   return true;
}

static BasicBlock *getBlock(User *U) {
  Instruction *I = dyn_cast<Instruction>(U);
  assert(I);
  return I->getParent();
}

void LoopPeel::removeObsolete(Loop *L, BasicBlock *BB, PostDominatorTree *PDT) {
  // by removing the backedge, blocks that are post-dominated by it
  // also need to be removed. the point for cutting them off would be
  // the post-dom frontier, but LLVM does not have this (anymore).
  std::list<const DomTreeNode*> Walker;
  std::set<BasicBlock*> Obsolete;
  assert(PDT->dominates(L->getHeader(), BB));
  Obsolete.insert(BB);
  Walker.push_back(PDT->getNode(BB));
  while (Walker.size()) {
    const DomTreeNode *DTN = Walker.front();
    Walker.pop_front();
    dbgs() << "obs: " << DTN->getBlock()->getName() << "\n";
    Obsolete.insert(DTN->getBlock()); // mark as obsolete, remove later
    Walker.insert(Walker.end(), DTN->begin(), DTN->end());
  }

  // now find the post-dominance frontier...
  typedef std::map<BasicBlock*, BasicBlock*> edgemap_t;
  edgemap_t Edges;
  BOOST_FOREACH(BasicBlock *O, Obsolete) {
    dbgs() << "obs: " << O->getName() << ": " << O->getNumUses() << "\n";
    for (Value::use_iterator UI = O->use_begin(), UE = O->use_end();
         UI != UE; ++UI) {
      User *U = *UI;
      BasicBlock *Pred = dyn_cast<Instruction>(U)->getParent();
      dbgs() << "pred: " << Pred->getName() << "\n";
      if (!Obsolete.count(Pred)) // only the edges on the frontier need to go
        Edges[Pred] = O;
    }
  }
  BOOST_FOREACH(edgemap_t::value_type e, Edges) {
    dbgs() << "cut: " << e.first->getName() << " - " << e.second->getName() << "\n";
    VIEW(*e.first->getParent(), "cutting");
    removeSucc(e.first, e.second);
  }
  LoopInfo &LI = getAnalysis<LoopInfo>();
  BOOST_FOREACH(BasicBlock *BB, Obsolete) {
    dbgs() << "obs remove: " << BB->getName() << "\n";
    LI.removeBlock(BB);
  }
}

void LoopPeel::redirectBackedges(Loop *L, BasicBlock *target) {
  BasicBlock *H = L->getHeader();
  PostDominatorTree *PDT = new PostDominatorTree();
  PDT->runOnFunction(*H->getParent());
  std::set<User*> Users;
  for (Value::use_iterator UI = H->use_begin(), UE = H->use_end();
       UI != UE; ++UI) {
    User *U = *UI;
    Instruction *I = dyn_cast<Instruction>(U);
    if (L->contains(I->getParent()))
      Users.insert(U); // user inside loop means this is a backedge
  }

  BOOST_FOREACH(User *U, Users) {
    BasicBlock *BB = dyn_cast<Instruction>(U)->getParent();
    U->replaceUsesOfWith(H, target ? target : BB);
    dbgs() << "redirecting backedge in " << BB->getName() << "\n";
    if (!target)
      // O (and maybe others) have most likely become obsolete
      removeObsolete(L, BB, PDT);
  }
  delete PDT;
}
bool LoopPeel::runOnLoop(Loop *L, LPPassManager &LPM) {
  Function *F = L->getHeader()->getParent();
  LLVMContext &C = getGlobalContext();
  typedef std::map<const BasicBlock*, BasicBlock*> bbmap_t;

  L->dump();

#if 0
  if (ExitCheck.count(L)) {
    SmallVector<BasicBlock*, 4> Exits;
    L->getExitBlocks(Exits);
    assert(Exits.size() == ExitCheck[L].size());
  }

  Loop *PL;
  if ((PL = L->getParentLoop())) {
    SmallVector<BasicBlock*, 4> Exits;
    PL->getExitBlocks(Exits);
    ExitCheck[PL] = Exits;
  }
#endif

  VIEW(*F, "runOnLoop");

  BasicBlock *exit, *H = L->getHeader();
  if (exit = L->getExitBlock()) {
    // simple loop
    for (Value::use_iterator UI = H->use_begin(), UE = H->use_end();
         UI != UE; ++UI) {
      User *U = *UI;
      Instruction *I = dyn_cast<Instruction>(U);
      if (L->contains(I->getParent()))
        U->replaceUsesOfWith(H, exit);
    }
    VIEW(*F, "simple loop transformed");
  } else {
    // multi-exit loop
    NumMultiExitLoops++;

    // clone loop blocks
    bbmap_t Lclones;
    BOOST_FOREACH(BasicBlock *BB,
                  std::make_pair(L->block_begin(), L->block_end())) {
      BasicBlock *newBB = BasicBlock::Create(C, BB->getName() + ".dup", F);
      Lclones[BB] = newBB;
    }

    // peeled header replaces original header
    for (Value::use_iterator UI = H->use_begin(), UE = H->use_end();
         UI != UE; ++UI)
      if (!L->contains(getBlock(*UI)))
        UI->replaceUsesOfWith(H, Lclones[H]);
    VIEW(*F, "header replaced");


    bbmap_t Lmap(Lclones);
    Lmap[H] = H; // point backedges to original header
    BOOST_FOREACH(bbmap_t::value_type v, Lclones) {

      const BasicBlock *BB = v.first;
      BasicBlock *newBB = v.second;

      IRBuilder<> bld(newBB);

      convertCalls(newBB, BB, Chain, CallMap);
      const Instruction *TI = BB->getTerminator();
      assert(!isa<ReturnInst>(TI));
      const BranchInst *BI = dyn_cast<BranchInst>(TI);
      assert(BI);
      Instruction *I = BI->clone();
      BOOST_FOREACH(Use &U, std::make_pair(I->op_begin(), I->op_end())) {
        if (BasicBlock *dst = dyn_cast<BasicBlock>(U.get())) {
          BasicBlock *mappedDst = dst;
          if (Lmap.count(dst))
            mappedDst = Lmap[dst]; // stays inside the cloned loop
          U.set(mappedDst);
        } else {
          U.set(UndefValue::get(bld.getInt1Ty()));
        }
      }
      newBB->getInstList().push_back(I);
    }

    VIEW(*F, "before redirectBackedges");
    redirectBackedges(L, NULL);
    VIEW(*F, "after redirectBackedges");

    // update loop info
    LoopInfo &LI = getAnalysis<LoopInfo>();
    BOOST_FOREACH(bbmap_t::value_type v, Lclones)
      L->addBasicBlockToLoop(v.second, LI.getBase());
    L->moveToHeader(Lclones[H]);
    BOOST_FOREACH(bbmap_t::value_type v, Lclones)
      assert(LI.getLoopFor(v.second) == L);
  }
  LoopInfo &LI = getAnalysis<LoopInfo>();
  dbgs() << "loops after hacking:\n";
  BOOST_FOREACH(Loop *L, std::make_pair(LI.begin(), LI.end()))
    L->dump();
  LPM.deleteLoopFromQueue(L);

  return true;
}
