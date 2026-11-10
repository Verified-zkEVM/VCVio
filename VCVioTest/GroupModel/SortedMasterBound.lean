/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.MasterBound
public import Mathlib.Algebra.Field.ZMod

/-! # Sorted master bounds for a Type 3 pairing

A bilinear query multiplies two linear inputs and consumes only the target-sort budget.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace GroupModel

/-- Linear source inputs and quadratic target entries form a closed Type 3 degree bound. -/
theorem pairing_degreeClosed_one_one_two :
    pairingSig.DegreeClosed (fun | .g₁ => 1 | .g₂ => 1 | .gₜ => 2) := by
  exact degreeClosed_pairingSig 1 1 0

/-- One pairing of linear inputs satisfies the sorted joint-variation bound over `ZMod 5`. -/
theorem pairing_bilinear_masterBound :
    let tbl : Tbl (fun _ : PSort => MvPolynomial Unit (ZMod 5)) :=
      fun | .g₁ => [MvPolynomial.X ()] | .g₂ => [MvPolynomial.X ()] | .gₜ => []
    let oa : OracleComp (genSpec (ZMod 5) pairingSig) Handle :=
      (genSpec (ZMod 5) pairingSig).query (.inl (.bil () 0 0))
    let : MeasurableSpace ((Unit → ZMod 5) ×
      (Handle × Tbl (fun _ : PSort => MvPolynomial Unit (ZMod 5)))) := ⊤
    measureETVDist
      (do let x ← $ᵗ (Unit → ZMod 5)
          let z ← runGen (symbolic (ZMod 5) pairingSig Unit)
            (fun _ p => MvPolynomial.eval x p) oa tbl
          pure (x, z))
      (do let x ← $ᵗ (Unit → ZMod 5)
          let z ← runGen (symbolic (ZMod 5) pairingSig Unit) (fun _ => id) oa tbl
          pure (x, z)) ≤ 4 / 5 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : Fintype PSort := ⟨{.g₁, .g₂, .gₜ}, by intro s; cases s <;> simp⟩
  let : MeasurableSpace ((Unit → ZMod 5) ×
      (Handle × Tbl (fun _ : PSort => MvPolynomial Unit (ZMod 5)))) := ⊤
  let tbl : Tbl (fun _ : PSort => MvPolynomial Unit (ZMod 5)) :=
    fun | .g₁ => [MvPolynomial.X ()] | .g₂ => [MvPolynomial.X ()] | .gₜ => []
  let oa : OracleComp (genSpec (ZMod 5) pairingSig) Handle :=
    (genSpec (ZMod 5) pairingSig).query (.inl (.bil () 0 0))
  let D : PSort → ℕ := fun | .g₁ => 1 | .g₂ => 1 | .gₜ => 2
  let n : PSort → ℕ := fun | .g₁ => 0 | .g₂ => 0 | .gₜ => 1
  have hn : ∀ s, IsQueryBoundP oa (appendsTo s) (n s) := by
    intro s
    cases s <;> exact ⟨by decide, fun _ => trivial⟩
  have hd : DegreeLE D tbl := by
    intro s p hp
    cases s <;> simp_all [tbl, D]
  have hε (s : PSort) (f : MvPolynomial Unit (ZMod 5))
      (hf : f ≠ 0) (hfD : f.totalDegree ≤ D s) :
      Pr{let x ← $ᵗ (Unit → ZMod 5)}[MvPolynomial.eval x f = 0] ≤
        (D s : ℝ≥0∞) / 5 := by
    simpa only [ZMod.card, Nat.cast_ofNat] using prob_eval_zero_univ_le_div f hf hfD
  have h := measureETVDist_runGen_symbolic_le_of_target ($ᵗ (Unit → ZMod 5))
    pairing_degreeClosed_one_one_two hε oa hn tbl hd
  have huniv : (Finset.univ : Finset PSort) = {.g₁, .g₂, .gₜ} := rfl
  norm_num [huniv, tbl, n, D] at h
  convert h using 1
  · simp only [oa, bind_pure_comp]
  · simp only [ENNReal.div_eq_inv_mul]
    ring

end GroupModel
