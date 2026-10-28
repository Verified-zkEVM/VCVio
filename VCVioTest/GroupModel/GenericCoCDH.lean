/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericCoCDH
public import Mathlib.Algebra.Field.ZMod

/-! # A numerical Type 3 co-CDH bound

One pairing query and an equality test exercise the co-CDH bound over the field with
101 elements. The equality answer selects either the challenge handle or an out-of-range handle.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace GroupModel

/-- One target append, no source appends, and a free equality test yield co-CDH success
at most `13/101`, even when the adversary returns an out-of-range source handle. -/
theorem cocdh_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    letI : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
      fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
    let A : OracleComp (genSpec (ZMod 101) pairingSig) Handle := do
      let t : Handle ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 1 1))
      let same : Bool ← (genSpec (ZMod 101) pairingSig).query (.inl (.eq .gₜ t 1))
      pure (if same then 2 else 3)
    Pr{let b ← (_root_.CoCDH.experiment (1 : ZMod 101) 1
      (CoCDH.Adversary.ofGeneric (LinearMap.mul (ZMod 101) (ZMod 101)) A))}[b = true] ≤
        (13 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
    fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
  dsimp only
  apply (CoCDH.experiment_ofGeneric_le
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1
    (by
      constructor
      · intro a b h
        simpa only [smul_eq_mul, mul_one] using h
      · intro a
        exact ⟨a, by simp⟩)
    one_ne_zero
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : ZMod 101) ≠ 0))
    _ 0 0 1 ?_ ?_ ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩

end GroupModel
