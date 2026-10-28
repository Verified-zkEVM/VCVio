/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericCoCDHIso
public import Mathlib.Algebra.Field.ZMod

/-! # A numerical Type 2 co-CDH bound

One source-map query, one pairing query and an equality test exercise the co-CDH bound
over the field with 101 elements. The equality answer selects either the source-map output
handle or an out-of-range handle.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace GroupModel

/-- One first-source append, one target append, and a free equality test yield co-CDH success
at most `10/101`, including an out-of-range first-source output on one equality branch. -/
theorem cocdh_iso_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    letI : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
      fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
    let A : OracleComp (genSpec (ZMod 101) pairingIsoSig) Handle := do
      let u : Handle ← (genSpec (ZMod 101) pairingIsoSig).query (.inl (.lin () 1))
      let t : Handle ← (genSpec (ZMod 101) pairingIsoSig).query (.inl (.bil () u 1))
      let same : Bool ← (genSpec (ZMod 101) pairingIsoSig).query (.inl (.eq .gₜ t 1))
      pure (if same then u else 2)
    Pr{let b ← (_root_.CoCDH.isoExperiment (1 : ZMod 101)
      (CoCDH.IsoAdversary.ofGeneric LinearMap.id
        (LinearMap.mul (ZMod 101) (ZMod 101)) A))}[b = true] ≤
        (10 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
    fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
  dsimp only
  apply (CoCDH.isoExperiment_ofGeneric_le
    (LinearMap.id) (LinearMap.mul (ZMod 101) (ZMod 101)) 1
    (by
      constructor
      · intro a b h
        simpa only [LinearMap.id_apply, smul_eq_mul, mul_one] using h
      · intro a
        exact ⟨a, by simp⟩)
    one_ne_zero
    (by simpa only [LinearMap.mul_apply', LinearMap.id_apply, one_mul] using
      (one_ne_zero : (1 : ZMod 101) ≠ 0))
    _ 1 0 1 ?_ ?_ ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ =>
      ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩⟩
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ =>
      ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩⟩
  · exact ⟨by decide, fun _ => ⟨Or.inr (by decide), fun _ =>
      ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩⟩

end GroupModel
