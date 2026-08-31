/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.External

/-!
# SLH-DSA external-interface canaries

Direct boundary examples that distinguish the pure and pre-hash domains, context placement,
DER-OID placement, digest placement, and the required 255/256-byte rejection boundary.
-/

public section

namespace SLHDSA.ExternalTest

open SLHDSA.External

def twoBytePrehash : PrehashDescriptor where
  oidDer := [0x06, 0x01, 0x2a]
  outputLength := 2
  digest := fun _ => #v[0xaa, 0xbb]

/-- Rejects a wrong pure domain byte or a missing empty-context length byte. -/
example : encodePureMessage [] [0xcc] = .ok [0x00, 0x00, 0xcc] := by
  decide

/-- Rejects wrong ordering among domain, context length, context, DER OID, and digest. -/
example : encodePrehashMessage twoBytePrehash [0x10, 0x11] [0xff] =
    .ok [0x01, 0x02, 0x10, 0x11, 0x06, 0x01, 0x2a, 0xaa, 0xbb] := by
  decide

/-- The largest permitted context is accepted and contributes exactly 257 prefix bytes. -/
example : (encodePureMessage (List.replicate 255 0x7f) []).map List.length = .ok 257 := by
  decide

/-- The first forbidden context length is rejected with its observed size. -/
example : encodePureMessage (List.replicate 256 0x7f) [] = .error (.contextTooLong 256) := by
  decide

/-- Pure and pre-hash encodings remain separated even when both context and content are empty. -/
example : encodePureMessage [] [] ≠ encodePrehashMessage twoBytePrehash [] [] := by
  decide

end SLHDSA.ExternalTest
