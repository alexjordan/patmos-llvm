//===-- PatmosFixupKinds.h - Patmos Specific Fixup Entries ----------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_PATMOS_PATMOSFIXUPKINDS_H
#define LLVM_PATMOS_PATMOSFIXUPKINDS_H

#include "llvm/MC/MCFixup.h"

namespace llvm {
namespace Patmos {
  // Although most of the current fixup types reflect a unique relocation
  // one can have multiple fixup types for a given relocation and thus need
  // to be uniquely named.
  //
  // This table *must* be in the save order of
  // MCFixupKindInfo Infos[Patmos::NumTargetFixupKinds]
  // in PatmosAsmBackend.cpp.
  //
  enum Fixups {
    // ALU immediate data fixup resulting in R_PATMOS_12.
    FK_Patmos_12 = FirstTargetFixupKind,

    // Call direct fixup, 2bit immediate, resulting in R_PATMOS_22
    FK_Patmos_22,

    // TODO do we need fixups for 7bit memory offset, or 12/22/32bit cache relative branches

    // Marker
    LastTargetFixupKind,
    NumTargetFixupKinds = LastTargetFixupKind - FirstTargetFixupKind
  };
} // namespace Patmos
} // namespace llvm


#endif // LLVM_PATMOS_PATMOSFIXUPKINDS_H