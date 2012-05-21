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
#include "llvm/Analysis/Dominators.h"
#include "llvm/Pass.h"

#include <boost/config.hpp>
#include <boost/graph/adjacency_list.hpp>
#include "boost/optional.hpp"

namespace llvm {

namespace cssa {
struct node_prop_t;

// graph definition
typedef boost::adjacency_list<boost::listS,
                              boost::vecS,
                              boost::bidirectionalS,
                              node_prop_t
                             > graph_t;

// graphviz output
void View(const graph_t& G, const std::string &Name);
void Write(std::ostream &O, const graph_t& G, const std::string &Name);

// vertex and edge properties
struct node_prop_t {
  const llvm::Function *func;
  std::string str;
  node_prop_t() : func(NULL) {}
  node_prop_t(const std::string &s) : func(NULL), str(s) {}
};

// convenience typdefs
typedef boost::graph_traits<graph_t>::vertex_descriptor vertex_t;
}

class CallSSA : public ModulePass {
  cssa::graph_t Graph;
  std::map<Value*, const Function*> CallMap;
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
    AU.addRequired<DominatorTree>();
    AU.setPreservesAll();
  }

  const cssa::graph_t &getGraph() const { return Graph; }

protected:
  void convertCalls(BasicBlock *dst, const BasicBlock *src, Value *Chain);
  void translate(Function &F);
  boost::optional<cssa::node_prop_t> translateInst(Instruction *I) const;

};

} // End llvm namespace

#endif
