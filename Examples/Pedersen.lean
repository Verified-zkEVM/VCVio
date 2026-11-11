/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.Schemes.Pedersen
public import Mathlib.Algebra.Field.ZMod

/-!
# Opening a Pedersen commitment

In the additive group modulo 101, take generator 1 and public parameter 9. Committing to
message 3 with randomness 7 gives 34. Checking the opening is deterministic; correctness
also holds for the scheme's randomly sampled commitments. This small arithmetic example
provides no computational binding guarantee. The general reduction is in
`VCVio/Schemes/Pedersen.lean`.
-/

public section

namespace Examples.Pedersen

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

example : (pedersenCommit (F := ZMod 101) (1 : ZMod 101)).verify 9 3 34 7 = true := by
  decide

example : (pedersenCommit (F := ZMod 101) (1 : ZMod 101)).verify 9 4 34 7 = false := by
  decide

example : (pedersenCommit (F := ZMod 101) (1 : ZMod 101)).PerfectlyCorrect :=
  pedersenCommit.correct

end Examples.Pedersen
