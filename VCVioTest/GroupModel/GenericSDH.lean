/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericSDH
public import Mathlib.Algebra.Field.ZMod

/-! # Numerical strong Diffie–Hellman bounds

Over the field with 101 elements, multiplication supplies the Type 3 pairing.
Each adversary makes a pairing query and tests equality in the target group.
With source degree two and one target append, the bounds are `21/100` and `23/100`.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace GroupModel

/-- One pairing and one equality test give the generic `t`-SDH bound `21/100`
for a degree-two SRS over `ZMod 101`. -/
theorem tsdh_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    letI : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
      fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
    let A : OracleComp (genSpec (ZMod 101) pairingSig) (ZMod 101 × Handle) := do
      let h ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 1 1))
      let _ ← (genSpec (ZMod 101) pairingSig).query (.inl (.eq .gₜ h 0))
      pure (0, 1)
    Pr{let b ← (TSDH.experiment (1 : ZMod 101) 1
      (TSDH.Adversary.ofGeneric (D := 2) (LinearMap.mul (ZMod 101) (ZMod 101)) A))}[b = true] ≤
      (21 / 100 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
    fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
  dsimp only
  apply (TSDH.experiment_ofGeneric_le
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1 one_ne_zero one_ne_zero
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : ZMod 101) ≠ 0))
    2 _ 0 0 1 ?_ ?_ ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩

/-- One pairing and one equality test give the generic ARSDH bound `23/100`
for a degree-two SRS and a three-element output set over `ZMod 101`. -/
theorem arsdh_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    letI : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
      fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
    let A : OracleComp (genSpec (ZMod 101) pairingSig)
        (Finset (ZMod 101) × Handle × Handle) := do
      let h ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 1 1))
      let _ ← (genSpec (ZMod 101) pairingSig).query (.inl (.eq .gₜ h 0))
      pure ({0, 1, 2}, 0, 1)
    Pr{let b ← (ARSDH.experiment (1 : ZMod 101) 1
      (ARSDH.Adversary.ofGeneric (D := 2) (LinearMap.mul (ZMod 101) (ZMod 101)) A))}[b = true] ≤
      (23 / 100 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
    fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
  dsimp only
  apply (ARSDH.experiment_ofGeneric_le
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1 one_ne_zero one_ne_zero
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : ZMod 101) ≠ 0))
    2 _ 0 0 1 ?_ ?_ ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩

end GroupModel
