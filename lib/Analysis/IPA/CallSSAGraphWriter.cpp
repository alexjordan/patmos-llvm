//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/CallSSA.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

#include <boost/config.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/graphviz.hpp>

using namespace llvm;
using namespace cssa;

struct vertex_label_writer {
  const graph_t &G;
  vertex_label_writer(const graph_t &G) : G(G) { }

  void operator()(std::ostream& out,
                  const vertex_t& v) const {
    std::string name = G[v].str;
    if (G[v].func)
      name = G[v].func->getName().str() + "()";

    out << "[label=\"" << name << "\"]";
  }

  std::string getName(Instruction *I) const {
    assert(I);
    CallSite CS(I);
    if (CS.isCall())
      return CS.getCalledValue()->getName().str() + "()";
    return "?";
  }
};

void cssa::View(const graph_t &G, const std::string &Name) {
  std::string ErrMsg;
  sys::Path Filename = sys::Path::GetTemporaryDirectory(&ErrMsg);
  if (Filename.isEmpty()) {
    errs() << "Error: " << ErrMsg << "\n";
    return;
  }
  Filename.appendComponent(Name + ".dot");
  if (Filename.makeUnique(true,&ErrMsg)) {
    errs() << "Error: " << ErrMsg << "\n";
    return;
  }

  errs() << "Writing '" << Filename.str() << "'... ";

  std::ofstream O(Filename.c_str());
  Write(O, G, Name);

  DisplayGraph(Filename, true, GraphProgram::DOT);
}

void cssa::Write(std::ostream &O,
                               const graph_t& G,
                               const std::string &Name) {
  boost::write_graphviz(O, G,
                        vertex_label_writer(G));
}

