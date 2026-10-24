/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.BitVec

/-!
# A separately transcribed Foundation/SAW statement

Foundation's `algorithms/Keccak/theorems/Main.saw` asks SAW to prove `h2bTest`.
This module transcribes that concrete statement: reverse each byte and keep
the first fourteen bits of `0xA32E`. It checks the statement in Lean without
importing a SAW certificate. The transcription is an additional trusted step;
this module makes no claim about an extracted Keccak implementation.
-/

public section

namespace Cryptol.Bridge.KeccakStatement

/-- Big-endian observations after reversing the bits within each input byte. -/
@[expose] def h2bPrefix {m n : Nat} (input : BitVec (8 * m)) : Fin n → Bool :=
  fun i => input.getMsbD ((i.val / 8) * 8 + (7 - i.val % 8))

/-- The concrete `h2bTest` statement also submitted by Foundation's SAW script. -/
theorem h2bTest : h2bPrefix (m := 2) (n := 14) (BitVec.ofNat 16 0xA32E) =
    fun i => (BitVec.ofNat 14 0b11000101011101).getMsbD i.val := by
  decide

end Cryptol.Bridge.KeccakStatement
