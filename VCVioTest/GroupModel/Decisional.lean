/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericDDH
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

/-!
# Relation-kernel examples and separations

With one group operation over the field with 101 elements, the decisional bound for the DDH
polynomial lists (`ddhTables_sameKernel`) is `45/101`. Repeated
variables introduce a relation, and one free equality test between the repeated entries
separates the hidden-point runs by more than the decisional bound would allow, so its kernel
clause cannot be dropped. Zero padding preserves the vanishing condition but is observable
through the fresh handle returned by a group operation, so its length clause cannot be dropped
either.
-/

public section

open OracleComp OracleSpec MeasureTheory MvPolynomial
open scoped ENNReal

namespace GroupModel

/-- Repeating one variable creates a linear relation absent from independent variables. -/
theorem repeated_variable_not_sameKernel :
    ¬ SameKernel (F := ZMod 5) (ι := Fin 3)
      (fun _ : Unit => [1, X 0, X 0]) (fun _ : Unit => [1, X 0, X 1]) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro h
  have he := h.eq_iff () (Pi.single 1 1) (Pi.single 2 1)
  simp [evRepr_apply, Pi.single_apply] at he

/-- Uniform generic DDH runs with one group operation over the field with 101 elements differ by
at most `45/101`, jointly with the hidden point: each side has `choose 6 2 = 15` collision pairs,
at degree two on the left and degree one on the right. -/
theorem ddh_uniform_bound {α : Type} [MeasurableSpace (((Fin 3) → ZMod 101) × α)]
    (oa : OracleComp (genSpec (ZMod 101) groupSig) α)
    (hq : IsQueryBoundP oa (fun i => isGroupOp i = true) 1) :
    measureETVDist
      (do let x ← $ᵗ ((Fin 3) → ZMod 101)
          let z ← runGen (symbolic (ZMod 101) groupSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) oa (fun _ => [1, X 0, X 1, X 0 * X 1])
          pure (x, z.1))
      (do let x ← $ᵗ ((Fin 3) → ZMod 101)
          let z ← runGen (symbolic (ZMod 101) groupSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) oa (fun _ => [1, X 0, X 1, X 2])
          pure (x, z.1)) ≤ 45 / 101 := by
  let : Fact (Nat.Prime 101) := ⟨by norm_num⟩
  have hb := measureETVDist_runGen_sameKernel_uniform_le oa hq
    (fun _ => [1, X 0, X 1, X 0 * X 1]) (fun _ => [1, X 0, X 1, X 2])
    (ddhTables_degreeLE (F := ZMod 101)).1 (ddhTables_degreeLE (F := ZMod 101)).2
    ddhTables_sameKernel
  refine hb.trans (le_of_eq ?_)
  simp [ZMod.card, Nat.choose]
  simp only [div_eq_mul_inv]
  ring

/-- The kernel clause of `SameKernel` cannot be dropped from
`measureETVDist_runGen_sameKernel_uniform_le`. Over the field with 17 elements the tables
`[1, X₀, X₀]` and `[1, X₀, X₁]` have the same length and degree one but different relation
kernels. One free equality test between their last two entries separates the uniform
hidden-point runs by at least `16/17`, more than that theorem's right side for these tables with
no group operations, `12/17`. -/
theorem kernel_clause_separation :
    let T₀ : Tbl (fun _ : Unit => MvPolynomial (Fin 2) (ZMod 17)) := fun _ => [1, X 0, X 0]
    let T₁ : Tbl (fun _ : Unit => MvPolynomial (Fin 2) (ZMod 17)) := fun _ => [1, X 0, X 1]
    let oa : OracleComp (genSpec (ZMod 17) groupSig) Bool :=
      (genSpec (ZMod 17) groupSig).query (.inl (.eq () 1 2))
    let : MeasurableSpace ((Fin 2 → ZMod 17) × Bool) := ⊤
    let dist := measureETVDist
      (do let x ← $ᵗ (Fin 2 → ZMod 17)
          let z ← runGen (symbolic (ZMod 17) groupSig (Fin 2))
            (fun _ p => MvPolynomial.eval x p) oa T₀
          pure (x, z.1))
      (do let x ← $ᵗ (Fin 2 → ZMod 17)
          let z ← runGen (symbolic (ZMod 17) groupSig (Fin 2))
            (fun _ p => MvPolynomial.eval x p) oa T₁
          pure (x, z.1))
    (∀ s, (T₀ s).length = (T₁ s).length) ∧ DegreeLE 1 T₀ ∧ DegreeLE 1 T₁ ∧
      ¬ SameKernel T₀ T₁ ∧ (16 / 17 : ℝ≥0∞) ≤ dist ∧
      (((∑ s, (T₀ s).length) + 0 + 1).choose 2 : ℝ≥0∞) *
          ((1 : ℝ≥0∞) / Fintype.card (ZMod 17)) +
        (((∑ s, (T₁ s).length) + 0 + 1).choose 2 : ℝ≥0∞) *
          ((1 : ℝ≥0∞) / Fintype.card (ZMod 17)) < dist := by
  intro T₀ T₁ oa _ dist
  let : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hsep : (1 : ℝ≥0∞) ≤ dist + 1 / 17 := by
    have hrun (T : Tbl (fun _ : Unit => MvPolynomial (Fin 2) (ZMod 17)))
        (x : Fin 2 → ZMod 17) :
        runGen (symbolic (ZMod 17) groupSig (Fin 2)) (fun _ p => MvPolynomial.eval x p) oa T =
          pure (decide (MvPolynomial.eval x (lookup T () 1) =
            MvPolynomial.eval x (lookup T () 2)), T) := rfl
    simp only [dist, hrun, pure_bind]
    let left : ProbComp ((Fin 2 → ZMod 17) × Bool) := do
      let x ← $ᵗ (Fin 2 → ZMod 17)
      pure (x, decide (MvPolynomial.eval x (lookup T₀ () 1) =
        MvPolynomial.eval x (lookup T₀ () 2)))
    let right : ProbComp ((Fin 2 → ZMod 17) × Bool) := do
      let x ← $ᵗ (Fin 2 → ZMod 17)
      pure (x, decide (MvPolynomial.eval x (lookup T₁ () 1) =
        MvPolynomial.eval x (lookup T₁ () 2)))
    have h := prEvent_le_prEvent_add_measureETVDist left right
      (fun w => w.2 = true) Measurable.of_discrete
    have hl : Pr{let w ← left}[w.2 = true] = 1 := by
      simp [left, T₀, lookup]
    have hr : Pr{let w ← right}[w.2 = true] ≤ 1 / 17 := by
      have hsz := prEvent_eval_eq_zero_univ_le_div (F := ZMod 17) (ι := Fin 2) (d := 1)
        (X 0 - X 1) (sub_ne_zero.mpr ((MvPolynomial.X_injective (σ := Fin 2) (R := ZMod 17)).ne
          (by decide)))
        ((MvPolynomial.totalDegree_sub _ _).trans (by simp))
      simpa [right, T₁, lookup, sub_eq_zero, ZMod.card] using hsz
    rw [hl] at h
    exact h.trans ((add_le_add hr le_rfl).trans_eq (add_comm _ _))
  have h16 : (16 / 17 : ℝ≥0∞) ≤ dist := by
    have hs : (16 / 17 : ℝ≥0∞) = 1 - 1 / 17 := by
      refine ENNReal.eq_sub_of_add_eq (by norm_num) ?_
      rw [ENNReal.div_add_div_same]
      norm_num
      exact ENNReal.div_self (by norm_num) (by norm_num)
    rw [hs]
    exact tsub_le_iff_right.mpr hsep
  refine ⟨fun _ => rfl, ?_, ?_, ?_, h16, ?_⟩
  · intro s p hp
    simp only [T₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp
  · intro s p hp
    simp only [T₁, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp
  · intro h
    have he := h.eq_iff () (Pi.single 1 1) (Pi.single 2 1)
    simp [T₀, T₁, evRepr_apply, Pi.single_apply] at he
  · refine lt_of_lt_of_le ?_ h16
    simp only [T₀, T₁, Fintype.sum_unique, List.length_cons, List.length_nil, ZMod.card]
    rw [← add_mul, mul_one_div]
    exact ENNReal.div_lt_div_right (by norm_num) (by norm_num) (by norm_num [Nat.choose])

/-- The vanishing condition alone cannot hide unequal lengths: a fresh handle separates
empty and singleton-zero tables with joint uniform-run distance one. -/
theorem empty_zero_uniform_separation :
    let T₀ : Tbl (fun _ : Unit => MvPolynomial (Fin 3) (ZMod 5)) := fun _ => []
    let T₁ : Tbl (fun _ : Unit => MvPolynomial (Fin 3) (ZMod 5)) := fun _ => [0]
    let oa : OracleComp (genSpec (ZMod 5) groupSig) Handle :=
      (genSpec (ZMod 5) groupSig).query (.inl (.add () 0 0))
    let : MeasurableSpace (((Fin 3) → ZMod 5) × Handle) := ⊤
    (∀ s (r : Coeffs (ZMod 5)), evRepr (T₀ s) r = 0 ↔ evRepr (T₁ s) r = 0) ∧
    ¬ SameKernel T₀ T₁ ∧
    measureETVDist
      (do let x ← $ᵗ ((Fin 3) → ZMod 5)
          let z ← runGen (symbolic (ZMod 5) groupSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) oa T₀
          pure (x, z.1))
      (do let x ← $ᵗ ((Fin 3) → ZMod 5)
          let z ← runGen (symbolic (ZMod 5) groupSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) oa T₁
          pure (x, z.1)) = 1 := by
  dsimp only
  refine ⟨by simp [evRepr_apply], ?_, ?_⟩
  · intro h
    have hl := (h ()).1
    simp at hl
  · let : MeasurableSpace (((Fin 3) → ZMod 5) × Handle) := ⊤
    let left : ProbComp (((Fin 3) → ZMod 5) × Handle) := do
      let x ← $ᵗ ((Fin 3) → ZMod 5)
      pure (x, 0)
    let right : ProbComp (((Fin 3) → ZMod 5) × Handle) := do
      let x ← $ᵗ ((Fin 3) → ZMod 5)
      pure (x, 1)
    change measureETVDist left right = 1
    apply le_antisymm (measureETVDist_le_one left right)
    have h := prEvent_le_prEvent_add_measureETVDist left right
      (fun w => w.2 = 0) Measurable.of_discrete
    simpa [left, right] using h

end GroupModel
