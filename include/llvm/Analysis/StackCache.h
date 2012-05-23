//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_STACK_CACHE_H
#define LLVM_STACK_CACHE_H

#include "llvm/Support/DataTypes.h"
#include <map>

namespace llvm {
  class Function;

  class SCStackInfo {
  public:
    typedef std::map<const Function*, uint64_t> ssmap_t;
    ssmap_t StackSizes;
    void dump() const;
  };
} // End llvm namespace

#endif

