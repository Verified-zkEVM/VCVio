/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Alexander Hicks
-/

module

public import Mathlib.Data.UInt

/-!
# Shared byte encodings

Fixed-width big-endian encoding of natural numbers. Values wider than the
requested width retain their least significant bytes.
-/

public section

namespace VCVio.Algorithms.Encoding

/-- Encode a natural number in exactly `width` bytes, most significant byte first. -/
@[expose] def natToBytesBE (x width : ℕ) : List UInt8 :=
  (List.range width).map (fun i => UInt8.ofNat (x / 256 ^ (width - 1 - i) % 256))

@[simp] theorem natToBytesBE_length (x width : ℕ) :
    (natToBytesBE x width).length = width := by
  simp [natToBytesBE]

end VCVio.Algorithms.Encoding
