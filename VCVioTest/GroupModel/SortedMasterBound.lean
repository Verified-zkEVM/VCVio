/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.MasterBound
public import Mathlib.Algebra.Field.ZMod

/-!
# Sorted master bounds for a Type 3 pairing

A bilinear query multiplies two linear inputs and consumes only the target-sort budget. A free
equality query then compares the product `X * X` with the zero default of the target sort. The
evaluated run sees a collision exactly when the hidden point is zero, so the joint distance of
the two runs is exactly `1/5` over `ZMod 5`, below the sorted master bound `4/5`. Without a
degree-closed target bound the theorem does not apply: the source bounds `1` and `1` close only
with a target bound of at least `2`.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace GroupModel

/-- Linear source inputs and quadratic target entries form a closed Type 3 degree bound. -/
theorem pairing_degreeClosed_one_one_two :
    pairingSig.DegreeClosed (fun | .g₁ => 1 | .g₂ => 1 | .gₜ => 2) := by
  exact degreeClosed_pairingSig 1 1 0

/-- Linear source inputs with a linear target bound are not closed. -/
theorem not_pairing_degreeClosed_one_one_one :
    ¬ pairingSig.DegreeClosed (fun | .g₁ => 1 | .g₂ => 1 | .gₜ => 1) := by
  rw [pairingSig_degreeClosed_iff]
  decide

/-- One pairing of linear inputs followed by a comparison with the target zero default satisfies
the sorted joint-variation bound `4/5` over `ZMod 5`. -/
theorem pairing_bilinear_masterBound :
    let tbl : Tbl (fun _ : PSort => MvPolynomial Unit (ZMod 5)) :=
      fun | .g₁ => [MvPolynomial.X ()] | .g₂ => [MvPolynomial.X ()] | .gₜ => []
    let oa : OracleComp (genSpec (ZMod 5) pairingSig) Bool := do
      let _ ← (genSpec (ZMod 5) pairingSig).query (.inl (.bil () 0 0))
      (genSpec (ZMod 5) pairingSig).query (.inl (.eq .gₜ 0 1))
    let : MeasurableSpace ((Unit → ZMod 5) ×
      (Bool × Tbl (fun _ : PSort => MvPolynomial Unit (ZMod 5)))) := ⊤
    measureETVDist
      (do let x ← $ᵗ (Unit → ZMod 5)
          let z ← runGen (symbolic (ZMod 5) pairingSig Unit)
            (fun _ p => MvPolynomial.eval x p) oa tbl
          pure (x, z))
      (do let x ← $ᵗ (Unit → ZMod 5)
          let z ← runGen (symbolic (ZMod 5) pairingSig Unit) (fun _ => id) oa tbl
          pure (x, z)) ≤ 4 / 5 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : MeasurableSpace ((Unit → ZMod 5) ×
      (Bool × Tbl (fun _ : PSort => MvPolynomial Unit (ZMod 5)))) := ⊤
  let tbl : Tbl (fun _ : PSort => MvPolynomial Unit (ZMod 5)) :=
    fun | .g₁ => [MvPolynomial.X ()] | .g₂ => [MvPolynomial.X ()] | .gₜ => []
  let oa : OracleComp (genSpec (ZMod 5) pairingSig) Bool := do
    let _ ← (genSpec (ZMod 5) pairingSig).query (.inl (.bil () 0 0))
    (genSpec (ZMod 5) pairingSig).query (.inl (.eq .gₜ 0 1))
  let D : PSort → ℕ := fun | .g₁ => 1 | .g₂ => 1 | .gₜ => 2
  let n : PSort → ℕ := fun | .g₁ => 0 | .g₂ => 0 | .gₜ => 1
  have hn : ∀ s, IsQueryBoundP oa (appendsTo s) (n s) := by
    intro s
    cases s <;> exact ⟨by decide, fun _ => ⟨by decide, fun _ => trivial⟩⟩
  have hd : DegreeLE D tbl := by
    intro s p hp
    cases s <;> simp_all [tbl, D]
  have hε (s : PSort) (f : MvPolynomial Unit (ZMod 5))
      (hf : f ≠ 0) (hfD : f.totalDegree ≤ D s) :
      Pr{let x ← $ᵗ (Unit → ZMod 5)}[MvPolynomial.eval x f = 0] ≤
        (D s : ℝ≥0∞) / 5 := by
    simpa only [ZMod.card, Nat.cast_ofNat] using prEvent_eval_eq_zero_univ_le_div f hf hfD
  have h := measureETVDist_runGen_symbolic_le_of_target ($ᵗ (Unit → ZMod 5))
    pairing_degreeClosed_one_one_two hε oa hn tbl hd
  have huniv : (Finset.univ : Finset PSort) = {.g₁, .g₂, .gₜ} := rfl
  norm_num [huniv, tbl, n, D] at h
  convert h using 1
  · simp only [oa, bind_pure_comp]
  · simp only [ENNReal.div_eq_inv_mul]
    ring

/-- The two runs of `pairing_bilinear_masterBound` are exactly `1/5` apart: the product `X * X`
evaluates to the zero default exactly when the hidden point is zero, and the exact run never
sees that collision. -/
theorem pairing_bilinear_masterBound_exact :
    let tbl : Tbl (fun _ : PSort => MvPolynomial Unit (ZMod 5)) :=
      fun | .g₁ => [MvPolynomial.X ()] | .g₂ => [MvPolynomial.X ()] | .gₜ => []
    let oa : OracleComp (genSpec (ZMod 5) pairingSig) Bool := do
      let _ ← (genSpec (ZMod 5) pairingSig).query (.inl (.bil () 0 0))
      (genSpec (ZMod 5) pairingSig).query (.inl (.eq .gₜ 0 1))
    let : MeasurableSpace ((Unit → ZMod 5) ×
      (Bool × Tbl (fun _ : PSort => MvPolynomial Unit (ZMod 5)))) := ⊤
    measureETVDist
      (do let x ← $ᵗ (Unit → ZMod 5)
          let z ← runGen (symbolic (ZMod 5) pairingSig Unit)
            (fun _ p => MvPolynomial.eval x p) oa tbl
          pure (x, z))
      (do let x ← $ᵗ (Unit → ZMod 5)
          let z ← runGen (symbolic (ZMod 5) pairingSig Unit) (fun _ => id) oa tbl
          pure (x, z)) = 1 / 5 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro tbl oa _
  let : MeasurableSpace (Unit → ZMod 5) := ⊤
  let XX : MvPolynomial Unit (ZMod 5) := MvPolynomial.X () * MvPolynomial.X ()
  let tbl' := append tbl .gₜ XX
  have hb : (symbolic (ZMod 5) pairingSig Unit).bil () (MvPolynomial.X ()) (MvPolynomial.X ()) =
      XX :=
    symbolic_bil_apply _ _ _ _
  have ho (x : Unit → ZMod 5) :
      runGen (symbolic (ZMod 5) pairingSig Unit) (fun _ p => MvPolynomial.eval x p) oa tbl =
        pure (decide (x () = 0), tbl') := by
    change (pure (decide (MvPolynomial.eval x ((symbolic (ZMod 5) pairingSig Unit).bil ()
        (MvPolynomial.X ()) (MvPolynomial.X ())) = MvPolynomial.eval x 0),
        append tbl .gₜ ((symbolic (ZMod 5) pairingSig Unit).bil ()
          (MvPolynomial.X ()) (MvPolynomial.X ()))) :
      ProbComp (Bool × Tbl (fun _ : PSort => MvPolynomial Unit (ZMod 5)))) = _
    rw [hb]
    simp [XX, tbl']
  have he : runGen (symbolic (ZMod 5) pairingSig Unit) (fun _ => id) oa tbl =
      pure (false, tbl') := by
    change (pure (decide ((symbolic (ZMod 5) pairingSig Unit).bil ()
        (MvPolynomial.X ()) (MvPolynomial.X ()) = 0),
        append tbl .gₜ ((symbolic (ZMod 5) pairingSig Unit).bil ()
          (MvPolynomial.X ()) (MvPolynomial.X ()))) :
      ProbComp (Bool × Tbl (fun _ : PSort => MvPolynomial Unit (ZMod 5)))) = _
    rw [hb]
    simp [XX, tbl', MvPolynomial.X_ne_zero]
  have hzero : Pr{let x ← $ᵗ (Unit → ZMod 5)}[x () = 0] = (1 / 5 : ℝ≥0∞) := by
    have hx : ∀ x : Unit → ZMod 5, x () = 0 ↔ x = fun _ => 0 :=
      fun x => ⟨fun h => funext fun u => h, fun h => h ▸ rfl⟩
    rw [prEvent_congr _ _ _ hx, SampleableType.prEvent_uniformSample_eq_singleton]
    simp [ZMod.card]
  simp only [ho, he, pure_bind]
  apply le_antisymm
  · have hmix := measureETVDist_bind_bind_le_lintegral ($ᵗ (Unit → ZMod 5))
      (fun x => (pure (x, decide (x () = 0), tbl') : ProbComp _))
      (fun x => (pure (x, false, tbl') : ProbComp _))
      Measurable.of_discrete Measurable.of_discrete
      (fun x => Pr{let _ ← (pure () : ProbComp Unit)}[x () = 0])
      (Filter.Eventually.of_forall fun x => by
        by_cases hx : x () = 0
        · simpa [hx] using measureETVDist_le_one _ _
        · simp [hx, measureETVDist_self])
    refine hmix.trans_eq ?_
    rw [← prEvent_bind_of_discrete ($ᵗ (Unit → ZMod 5)) (fun x => pure (x () = 0))]
    simpa only [bind_pure_comp] using hzero
  · have hv := prEvent_le_prEvent_add_measureETVDist
      (($ᵗ (Unit → ZMod 5)) >>= fun x => (pure (x, decide (x () = 0), tbl') : ProbComp _))
      (($ᵗ (Unit → ZMod 5)) >>= fun x => (pure (x, false, tbl') : ProbComp _))
      (fun w => w.2.1 = true) Measurable.of_discrete
    simpa [hzero] using hv

end GroupModel
