/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericPairing
public import Mathlib.Algebra.Field.ZMod

/-! # A numerical Type 3 powers discrete-logarithm bound

A pairing query on the first powers, followed by a scalar guess, exercises the
`(2, 1)`-DLog bound over the field with 101 elements.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace GroupModel

/-- One target append and no source appends give the bound `19/101` for the
`(2, 1)`-DLog experiment with multiplication as its pairing. -/
theorem pairing_dlog_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    letI : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
      fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
    let A : OracleComp (genSpec (ZMod 101) pairingSig) (ZMod 101) := do
      let _ ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 1 1))
      pure 0
    Pr{let b ← (PairingDLog.experiment (1 : ZMod 101) 1
      (PairingDLog.Adversary.ofGeneric (q₁ := 2) (q₂ := 1)
        (LinearMap.mul (ZMod 101) (ZMod 101)) A))}[b = true] ≤ (19 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
    fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
  dsimp only
  apply (PairingDLog.experiment_ofGeneric_le
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1 one_ne_zero one_ne_zero
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : ZMod 101) ≠ 0))
    2 1 _ 0 0 1 ?_ ?_ ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => trivial⟩
  · exact ⟨by decide, fun _ => trivial⟩
  · exact ⟨by decide, fun _ => trivial⟩

end GroupModel
