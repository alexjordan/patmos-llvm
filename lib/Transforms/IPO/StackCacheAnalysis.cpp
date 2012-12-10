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
#include "llvm/Analysis/StackCache.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Module.h"

#include <stack>
#include "boost/foreach.hpp"
#include "boost/tuple/tuple.hpp"

using namespace llvm;
using namespace cssa;
using namespace boost;

STATISTIC(CallSitesCallExt,      "Number call sites that cannot be analyzed");
STATISTIC(CallSitesGood,         "Number call sites that can be analyzed");
STATISTIC(CallSitesRec,          "Number call sites to recursive");
STATISTIC(CallSitesOmitted,      "Number call sites omitted (in recursive)");

namespace {
  enum StackCacheSettings {
    BlockSize = 16,
    NumBlocks = 2
  };

  struct StackSize {
    uint64_t sz;
    StackSize(uint64_t s = 0) : sz(s) {}
    void operator+= (const StackSize &RHS);
    void operator-= (const StackSize &RHS);
    friend bool operator== (const StackSize &LHS, const StackSize &RHS);
    friend bool operator< (const StackSize &LHS, const StackSize &RHS);
    friend StackSize operator+ (const StackSize &LHS, const StackSize &RHS);
    friend raw_ostream& operator<< (raw_ostream &os, const StackSize &ss);
  };

  uint64_t toBlocks(uint64_t sz) { return (sz + BlockSize - 1) / BlockSize; }

  struct StackState {
    StackSize reserved, spilled;
    StackState(int res = 0) : reserved(res) {}

    StackState reserve(const StackSize &ss) {
      StackState newSS(*this);
      uint64_t res = toBlocks(ss.sz);
      uint64_t spill = std::max<int>(res - available(), 0);
      assert(spill <= NumBlocks && "stack too small");
      newSS.reserved += res - spill;
      return newSS;
    }
    StackState free(const StackSize &ss) {
      StackState newSS(*this);
      newSS.reserved -= toBlocks(ss.sz);
      return newSS;
    }

    uint64_t available() const { return NumBlocks - reserved.sz; }
    bool operator==(const StackState &RHS) const {
      return (reserved == RHS.reserved);
    }
    bool operator<(const StackState &RHS) const {
      return reserved < RHS.reserved;
    }
    friend raw_ostream& operator<<(raw_ostream &os, const StackState &ss);
  };

  class AnalysisNode;
  class ReserveNode;
  class FreeNode;
  class CallNode;

  class AnalysisVisitor {
  public:
    virtual ~AnalysisVisitor() {}
    virtual void visit(ReserveNode *n) = 0;
    virtual void visit(FreeNode *n) = 0;
    virtual void visit(CallNode *n) = 0;
  };

  typedef std::vector<AnalysisNode*> an_map_t;

  class AnalysisNode {
    StackState inState;
    StackState outState;
    an_map_t &AM;
  public:
    vertex_t v;
    graph_t &G;
    AnalysisNode(vertex_t v, graph_t &G, an_map_t &AM)
      : AM(AM), v(v), G(G) {}
    virtual ~AnalysisNode() {}
    StackState getInState() const { return inState; }
    StackState getOutState() const { return outState; }
    void setInState(const StackState &ss) { inState = ss; }
    void setOutState(const StackState &ss) { outState = ss; }
    const AnalysisNode *getNode(vertex_t v) const { return AM[v]; }
    AnalysisNode *getNode(vertex_t v) { return AM[v]; }
    const Function *getFunction() { return G[graph_bundle].F; }
    virtual void setCaller(AnalysisNode *N) {}
    virtual void accept(AnalysisVisitor *visitor) = 0;
    virtual StackState calcInState() const;
    bool updateInState();
    bool updateOutState(const StackState &ss);
  };

  class ReserveNode : public AnalysisNode {
    AnalysisNode *Caller;
  public:
    ReserveNode(vertex_t v, graph_t &G, an_map_t &AM)
      : AnalysisNode(v,G,AM), Caller(NULL) {}
    void accept(AnalysisVisitor *visitor) { visitor->visit(this); }
    virtual void setCaller(AnalysisNode *N) { Caller = N; }
    StackState calcInState() const;
  };
  class FreeNode : public AnalysisNode {
    AnalysisNode *Caller;
  public:
    FreeNode(vertex_t v, graph_t &G, an_map_t &AM)
      : AnalysisNode(v,G,AM), Caller(NULL) {}
    void accept(AnalysisVisitor *visitor) { visitor->visit(this); }
    virtual void setCaller(AnalysisNode *N) { Caller = N; }
    AnalysisNode *getCaller() { return Caller; }
  };
  class CallNode : public AnalysisNode {
  public:
    AnalysisNode *Callee, *Ret;
    CallNode(vertex_t v, graph_t &G, an_map_t &AM)
      : AnalysisNode(v,G,AM), Callee(NULL), Ret(NULL) {}
    void accept(AnalysisVisitor *visitor) { visitor->visit(this); }
    bool updateOutFromRet();
  };

  typedef GraphTraits<CallGraphNode*> CGT;
  typedef CallGraphNode CGN;
  typedef std::map<CGN*, StackSize> maxstack_t;

  class StackCacheAnalysis : public ModulePass, public AnalysisVisitor {
    SCStackInfo *SCSI;
    maxstack_t MaxStack;        // accumulated stack depth
    std::set<CGN*> Blacklist;   // nodes we don't want to visit

    // topdown traversal stuff
    typedef std::map<const Function*, graph_t> graph_cache_t;
    typedef std::list<AnalysisNode*> worklist_t;
    graph_cache_t GraphCache;
    worklist_t Worklist;
    std::list<std::vector<AnalysisNode*> > AllNodeMaps;
  public:
    StackCacheAnalysis(SCStackInfo *scsi = NULL)
      : ModulePass(ID), SCSI(scsi) {
      initializeStackCacheOptPass(*PassRegistry::getPassRegistry());
    }
    static char ID; // Pass identification, replacement for typeid

    bool runOnModule(Module &M);
    void runTests(Module &M);
    void antest(const graph_t &G);

    bool bottomUp(Module &M);
    void topDown(Module &M);

    // topdown related..
    static AnalysisNode *makeNode(vertex_t v, graph_t &G, an_map_t &AM);
    graph_t &getGraph(const Function *F);
    void visit(ReserveNode *N);
    void visit(FreeNode *N);
    void visit(CallNode *N);

    void getAnalysisUsage(AnalysisUsage& AU) const {
      AU.addRequired<CallSSA>();
      AU.addRequired<CallGraph>();
      AU.addRequired<DominatorTree>();
      AU.addRequired<PostDominatorTree>();
      AU.addRequired<LoopInfo>();
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

  if (false) {
    runTests(M);
    return false;
  }

  CallSSA &CS = getAnalysis<CallSSA>();
  if (CS.isIncomplete()) {
    errs() << "StackCacheAnalysis: incomplete call-ssa, aborting\n";
    return false;
  }

  bool complete;

  //cssa::View(G, "foo");
  complete = bottomUp(M);

  if (!complete) {
    errs() << "StackCacheAnalysis: incomplete call-ssa, aborting\n";
    return false;
  }

  if (true) {
    dbgs() << " CG ANALYSIS\n";
    runTests(M);
    return false;
  }

  topDown(M);

  return true;
}

bool StackCacheAnalysis::bottomUp(Module &M) {
  CallGraph& CG = getAnalysis<CallGraph>();
  assert(SCSI);
  SCStackInfo::ssmap_t &StackSizes = SCSI->StackSizes;

  CGN *root = CG.getRoot();
  if (!root->getFunction()) {
    errs() << "StackCacheAnalysis: no root function\n";
    return false;
  }

  typedef std::vector<CGN*> scc_t;
  std::vector<scc_t> SCCs;
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
    //DEBUG(dbgs() << "SCC #" << SCCs.size() << " (" << scc.size() << "):\n");
    //SCCs.push_back(*I);
    //BOOST_FOREACH(CGN *n, scc) {
    //  if (Function *F = n->getFunction())
    //    DEBUG(dbgs() << "Call graph node for function: '"
    //          << F->getName() << "'");
    //  else
    //    DEBUG(dbgs() << "Call graph node <<null function>>");
    //}
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
        MaxStack[succ] = 0;
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
      DEBUG(dbgs() << "traversal @ ");
      DEBUG(cgn->dump());
      Seen.insert(cgn);
      Stack.pop();

      Function *func = cgn->getFunction();
      assert(func);
      if (func->isDeclaration()) {
        DEBUG(dbgs() << "function declaration '" << func->getName()
              << "' -> assuming stack size 0.\n");
        MaxStack[cgn] = 0;
        Blacklist.insert(cgn);
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
    if (Function *F = I->first->getFunction())
      dbgs() << F->getName() << ": " << I->second << "\n";

  return true;
}

void StackCacheAnalysis::topDown(Module &M) {
  CallSSA &CS = getAnalysis<CallSSA>();
  CallGraph& CG = getAnalysis<CallGraph>();
  CGN *root = CG.getRoot();
  Function *F = root->getFunction();
  assert(F);


  // traversal

  graph_t &G = getGraph(F);
  AllNodeMaps.push_back(std::vector<AnalysisNode*>());
  std::vector<AnalysisNode*> &ANs = AllNodeMaps.back();
  ANs.resize(num_vertices(G));
  BOOST_FOREACH(vertex_t v, vertices(G)) {
    ANs[v] = makeNode(v, G, ANs);
  }

  // kick off propagation
  ANs[G[graph_bundle].s]->setInState(StackState(-1));
  Worklist.push_back(ANs[G[graph_bundle].s]);
  bool AnalysisComplete = true;

  while (Worklist.size()) {

    // lazy analysis. we have to check again if something was undefined
    if (CS.isIncomplete()) {
      errs() << "StackCacheAnalysis: incomplete call-ssa, aborting\n";
      AnalysisComplete = false;
      break;
    }

    AnalysisNode *N = Worklist.front();
    Worklist.pop_front();
    N->accept(this);
  }

  if (AnalysisComplete) {
    DEBUG(dbgs() << "--- end state ---\n");
    DEBUG(dbgs() << "[IN]:  " << ANs[G[graph_bundle].t]->getInState() << "\n");
    DEBUG(dbgs() << "[OUT]: " << ANs[G[graph_bundle].t]->getOutState() << "\n");
    assert(ANs[G[graph_bundle].t]->getOutState().reserved == 0);
  } else
    errs() << "StackCacheAnalysis: analysis was incomplete\n";



  BOOST_FOREACH(std::vector<AnalysisNode*> &vec, AllNodeMaps)
    BOOST_FOREACH(AnalysisNode *n, vec)
      delete n;
}

AnalysisNode *StackCacheAnalysis::makeNode(vertex_t v,
                                           graph_t &G,
                                           an_map_t &AM) {
  if (v == G[graph_bundle].s)
    return new ReserveNode(v,G,AM);
  else if (v == G[graph_bundle].t)
    return new FreeNode(v,G,AM);
  else
    return new CallNode(v,G,AM);
}

void StackCacheAnalysis::visit(ReserveNode *N) {
  SCStackInfo::ssmap_t &StackSizes = SCSI->StackSizes;
  dbgs() << "visit: s\n";
  if (!N->updateInState())
    return;
  if (!N->updateOutState(N->getInState().reserve(StackSizes[N->getFunction()])))
    return;

  BOOST_FOREACH(vertex_t w, adjacent_vertices(N->v, N->G))
    Worklist.push_back(N->getNode(w));
}

void StackCacheAnalysis::visit(FreeNode *N) {
  SCStackInfo::ssmap_t &StackSizes = SCSI->StackSizes;
  dbgs() << "visit: t\n";
  if (!N->updateInState())
    return;
  if (!N->updateOutState(N->getInState().free(StackSizes[N->getFunction()])))
    return;
  if (AnalysisNode *C = N->getCaller())
    Worklist.push_back(C);
}

void StackCacheAnalysis::visit(CallNode *N) {
  const Function *F = N->G[N->v].func;

  DEBUG(dbgs() << "visit: call " << F->getName() << "\n");

  if (N->updateInState()) {
    // incoming state changed -> propagate to call
    CallGraph& CG = getAnalysis<CallGraph>();
    if (Blacklist.count(CG[F])) {
      DEBUG(dbgs() << "visit: ..skipping call\n");
      if (!N->updateOutState(N->getInState()))
        return;
      BOOST_FOREACH(vertex_t w, adjacent_vertices(N->v, N->G))
        Worklist.push_back(N->getNode(w));
      return;
    }
    if (!N->Callee) {
      // create subgraph analysis nodes
      graph_t &G = getGraph(F);
      if (num_vertices(G) < 2) {
        return;
      }
      AllNodeMaps.push_back(std::vector<AnalysisNode*>());
      std::vector<AnalysisNode*> &ANs = AllNodeMaps.back();
      ANs.resize(num_vertices(G));
      BOOST_FOREACH(vertex_t v, vertices(G)) {
        ANs[v] = StackCacheAnalysis::makeNode(v, G, ANs);
        ANs[v]->setCaller(N);
      }
      N->Callee = ANs[G[graph_bundle].s];
      N->Ret = ANs[G[graph_bundle].t];
    }
    Worklist.push_back(N->Callee);
  } else if (N->updateOutFromRet()) {
    // stack state of the call changed -> update our out-state
    BOOST_FOREACH(vertex_t w, adjacent_vertices(N->v, N->G))
      Worklist.push_back(N->getNode(w));
  }
}

graph_t &StackCacheAnalysis::getGraph(const Function *F) {
  CallSSA &CS = getAnalysis<CallSSA>();

  graph_cache_t::iterator it = GraphCache.find(F);
  if (it == GraphCache.end()) {
    DEBUG(dbgs() << "Fetching cssa-graph for " << F->getName() << "...\n");
    boost::tie(it, tuples::ignore) =
      GraphCache.insert(std::make_pair(F, CS.getGraph(*F, this)));
  }

  //if (num_vertices(it->second) > 2)
  //  View(it->second, it->first->getName());

  return it->second;
}

StackState AnalysisNode::calcInState() const {
  StackState in;
  BOOST_FOREACH(vertex_t u, inv_adjacent_vertices(v,G))
    in = std::max(in, getNode(u)->getOutState());
  return in;
}

bool AnalysisNode::updateInState() {
  StackState in = calcInState();
  if (in == getInState())
    return false;
  DEBUG(dbgs() << "[IN]:  " << in << "\n");
  setInState(in);
  return true;
}

bool AnalysisNode::updateOutState(const StackState &out) {
  if (out == getOutState())
    return false;
  DEBUG(dbgs() << "[OUT]: " << out << "\n");
  setOutState(out);
  return true;
}

StackState ReserveNode::calcInState() const {
  if (Caller)
    return Caller->getInState();
  return StackState();
}

bool CallNode::updateOutFromRet() {
  assert(Ret);
  StackState out = Ret->getOutState();
  if (out == getOutState())
    return false;
  DEBUG(dbgs() << "[OUT]: " << out << "\n");
  setOutState(out);
  return true;
}

namespace {
uint64_t add_sat(uint64_t a, uint64_t b) {
  uint64_t c = a + b;
  return std::max(c, std::max(a,b));
}

void StackSize::operator+= (const StackSize &RHS) {
  sz = add_sat(sz, RHS.sz);
}

void StackSize::operator-= (const StackSize &RHS) {
  assert(sz >= RHS.sz);
  sz -= RHS.sz;
}

inline StackSize operator+(const StackSize &LHS, const StackSize &RHS) {
  return StackSize(add_sat(LHS.sz, RHS.sz));
}

inline bool operator==(const StackSize &LHS, const StackSize &RHS) {
  return LHS.sz == RHS.sz;
}

inline bool operator< (const StackSize &LHS, const StackSize &RHS) {
  return LHS.sz < RHS.sz;
}

raw_ostream& operator<<(raw_ostream &OS, const StackSize &SS) {
  if (SS.sz == StackCacheAnalysis::unlimited)
    OS << "<unlimited>";
  else
    OS << SS.sz;
  return OS;
}

raw_ostream& operator<<(raw_ostream &os, const StackState &ss) {
  os << "R: " << ss.reserved;
  return os;
}
}

//
// implement SCStackInfo
//
void SCStackInfo::dump() const {
  dbgs() << "Stack size per function:\n";
  for (std::map<const Function*, uint64_t>::const_iterator I = StackSizes.begin(),
       E = StackSizes.end(); I != E; ++I)
    dbgs() << I->first->getName() << ": " << I->second << "\n";
}

//
// testing
//
static std::string toString(vertex_t v, const graph_t &G) {
  if (G[v].func)
    return "call: " + G[v].func->getName().str() + "()";
  else
    return G[v].str;
}

namespace Test {
  class AnalysisNode;
  typedef std::pair<AnalysisNode*, AnalysisNode*> callsite_t;

struct Global {
  StackCacheAnalysis *SCA;
  SCStackInfo::ssmap_t StackSizes;
  typedef std::map<boost::tuple<AnalysisNode*, vertex_t, const Function*>,
          AnalysisNode*> map_t;
  map_t Map;
  std::set<AnalysisNode*> Worklist;

  Global(StackCacheAnalysis *SCA) : SCA(SCA) {}

  AnalysisNode *getNode(AnalysisNode *CallSite, vertex_t v, const graph_t &G) {
    return getNode(CallSite, v, G[graph_bundle].F);
  }
  AnalysisNode *getNode(AnalysisNode *CS, vertex_t v, const Function *F) {
    assert(false && "not impl");
    /*
    map_t::iterator it;
    map_t::key_type key = boost::make_tuple(CS,v,F);
    if ((it = Map.find(key)) != Map.end())
      return it->second;
    AnalysisNode *N = makeNode(v,SCA->getGraph(F));
    Map[key] = N;
    return N;
    */
  }
  void work();
  void newCall(const callsite_t &CS, const graph_t &G);
  void newCall(const callsite_t &CS, const Function *F) {
    newCall(CS, SCA->getGraph(F));
  }
};

struct Local {
  uint64_t StackSize;
  typedef std::map<vertex_t, AnalysisNode*> map_t;
  map_t Map;
  Global *A;

  Local(Global *g) : A(g) {}

  void addToWorklist(AnalysisNode *N) { A->Worklist.insert(N); }
  void newCall(const callsite_t &CS, const Function *F) { A->newCall(CS, F); }

  AnalysisNode *getNode(vertex_t v, const graph_t& G) {
    map_t::iterator it;
    if ((it = Map.find(v)) != Map.end())
      return it->second;
    AnalysisNode *N = makeNode(v,G);
    Map[v] = N;
    return N;
  }
  AnalysisNode *makeNode(vertex_t v, const graph_t &G);
};

class AnalysisNode {
public:
  Local *L;
  StackState inState;
  StackState outState;
public:
  vertex_t v;
  const graph_t &G;
  const Function *F;
  AnalysisNode(vertex_t v, const graph_t &G)
    : L(NULL), v(v), G(G), F(G[graph_bundle].F) {}
  virtual ~AnalysisNode() {}
  void set(Local *local) { L = local; }
  void succs() {
    BOOST_FOREACH(vertex_t u, adjacent_vertices(v,G))
      dbgs() << "succ: " << L->getNode(u,G) << " " << toString(u,G) << "\n";
  }
  void kick(const StackState &SS) {
    inState = SS;
    L->addToWorklist(this);
  }
  virtual void update() = 0;
  void propagate() {
    BOOST_FOREACH(vertex_t u, adjacent_vertices(v,G)) {
      L->getNode(u,G)->inState = outState;
      L->addToWorklist(L->getNode(u,G));
    }
  }

};
class ReserveNode : public AnalysisNode {
public:
  ReserveNode(vertex_t v, const graph_t &G) : AnalysisNode(v,G) {}
  void update() {
    outState = inState.reserve(L->StackSize);
    dbgs() << "[" << F->getName() << "] reserve out: " << outState << "\n";
    propagate();
  }
#if 0
      dbgs() << "leaf graph, ";
      dbgs() << "stack use: " << StackSizes[I] << "\n";
      for (int s = 0; s <= NumBlocks; ++s) {
        StackState ss(s);
        dbgs() << "state before: " << ss << "\n";
        ss = ss.reserve(StackSizes[I]);
        dbgs() << "state between: " << ss << "\n";
        ss = ss.free(StackSizes[I]);
        dbgs() << "state after: " << ss << "\n";
      }
#endif
};
class FreeNode : public AnalysisNode {
  AnalysisNode *Return;
public:
  FreeNode(vertex_t v, const graph_t &G) : AnalysisNode(v,G), Return(0) {}
  void update() {
    outState = inState.free(L->StackSize);
    dbgs() << "[" << F->getName() << "]free out: " << outState << "\n";
    assert(Return && "analysis over");
    Return->inState = outState;
    L->addToWorklist(Return);
  }
  void setParent(AnalysisNode *N) { Return = N; }
};

class CallDeferNode : public AnalysisNode {
  AnalysisNode *Return;
public:
  CallDeferNode(vertex_t v, const graph_t &G, AnalysisNode *R)
    : AnalysisNode(v,G), Return(R) {}
  void update() {
    L->newCall(std::make_pair(this, Return), G[v].func);
  }
};

class EnsureNode : public AnalysisNode {
public:
  EnsureNode(vertex_t v, const graph_t &G)
    : AnalysisNode(v,G) {}
  void update() {
    dbgs() << "ensure: " << inState << "\n";
    succs();
    propagate();
  }
};

AnalysisNode *Local::makeNode(vertex_t v, const graph_t &G) {
  AnalysisNode *N;
  if (v == G[graph_bundle].s)
    N = new ReserveNode(v,G);
  else if (v == G[graph_bundle].t)
    N = new FreeNode(v,G);
  else {
    // it's a call
    AnalysisNode *M = new EnsureNode(v,G);
    M->set(this);
    N = new CallDeferNode(v,G,M);
  }

  N->set(this);
  return N;
}

void Global::work() {
  while (Worklist.size()) {
    AnalysisNode *N = *Worklist.begin();
    Worklist.erase(Worklist.begin());
    N->update();
  }
}
void Global::newCall(const callsite_t &CS, const graph_t &G) {
  // set up local context
  Local *L = new Local(this);
  L->StackSize = StackSizes[G[graph_bundle].F];

  // create the entry node
  AnalysisNode *S = new ReserveNode(G[graph_bundle].s, G);
  S->set(L);
  S->kick(StackState());
  L->Map[G[graph_bundle].s] = S;

  // and the exit node
  FreeNode *T = new FreeNode(G[graph_bundle].s, G);
  T->set(L);
  T->setParent(CS.second);
  L->Map[G[graph_bundle].t] = T;
}

class AnalysisRoot : public AnalysisNode {
public:
  AnalysisRoot() : AnalysisNode(0, graph_t()) {}
  void update() {
    dbgs() << "analysis root reached\n";
  }
};
}

void StackCacheAnalysis::antest(const graph_t &G) {
  /*
  Test::AnalysisNode *S = glob.makeNode(G[graph_bundle].s, G);
  S->succs();
  */
  SCStackInfo::ssmap_t &StackSizes = SCSI->StackSizes;
  Test::Global glob(this);
  glob.StackSizes = StackSizes;
  Test::AnalysisRoot RN;
  glob.newCall(std::make_pair(&RN, &RN), G);
  glob.work();
}

namespace llvm {
raw_ostream &operator<<(raw_ostream &OS, const CallGraphNode &CGN) {
  if (Function *F = CGN.getFunction())
    OS << "Call graph node for function: '" << F->getName() << "'";
  else
    OS << "Call graph node <<null function>>";
  return OS;
}
}

void StackCacheAnalysis::runTests(Module &M) {
#if 0
  SCStackInfo::ssmap_t &StackSizes = SCSI->StackSizes;
  for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I) {
    if (I->isDeclaration())
      continue;
    getGraph(I);

    /*
    BOOST_FOREACH(vertex_t v, vertices(G)) {
      dbgs() << toString(v,G) << "\n";
      if (G[v].func) {
      } else {
        BOOST_FOREACH(vertex_t u, adjacent_vertices(v,G))
          dbgs() << "succ: " << toString(u,G) << "\n";
      }
    }
    View(G, "foo");
    */

  }
  {
    CallGraph& CG = getAnalysis<CallGraph>();
    CGN *root = CG.getRoot();
    Function *F = root->getFunction();
    assert(F);
    antest(getGraph(F));
  }
#endif
  BOOST_FOREACH(CGN *cgn, Blacklist)
    dbgs() << "blacklist: " << *cgn << "\n";

  CallGraph& CG = getAnalysis<CallGraph>();
  CGN *callsext = CG.getCallsExternalNode();
  CGN *extcalling = CG.getExternalCallingNode();

  for(CallGraph::iterator I = CG.begin(), E = CG.end(); I != E; ++I) {
    CGN *cgn = I->second;
    if (cgn == extcalling)
      continue;
    cgn->dump();

    BOOST_FOREACH(const CallGraphNode::CallRecord &CR, *cgn) {
      //dbgs() << "call to " << *CR.second << "\n";
      if (Blacklist.count(cgn)) {
        cgn->getFunction()->dump();
        ++CallSitesOmitted;
      }
      else if (Blacklist.count(CR.second))
        ++CallSitesRec;
      else if (CR.second == callsext)
        ++CallSitesCallExt;
      else
        ++CallSitesGood;
    }
  }
}


