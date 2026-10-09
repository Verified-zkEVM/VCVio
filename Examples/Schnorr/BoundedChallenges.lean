/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Schnorr.ChallengeRestriction
public import Mathlib.Data.ZMod.Basic

/-!
# Bounded integer challenges inside Schnorr's scalar field

The map from `Fin c` into `ZMod p` is injective when `c ≤ p`. Primality of `p` is
the separate hypothesis that makes `ZMod p` a field for the Schnorr instantiation.
No concrete group or computational discrete-log assumption is supplied by this embedding.
-/

public section

namespace Schnorr

/-- Encode a bounded integer challenge as a scalar modulo `p`. -/
@[expose]
def boundedChallenge (p c : ℕ) (x : Fin c) : ZMod p := x.val

/-- The finite challenge policy meets the special-soundness injectivity requirement. -/
theorem boundedChallenge_injective (p c : ℕ) (hc : c ≤ p) :
    Function.Injective (boundedChallenge p c) := by
  intro x y h
  apply Fin.ext
  have hv := congrArg ZMod.val h
  simpa only [boundedChallenge, ZMod.val_natCast_of_lt (x.isLt.trans_le hc),
    ZMod.val_natCast_of_lt (y.isLt.trans_le hc)] using hv

end Schnorr
