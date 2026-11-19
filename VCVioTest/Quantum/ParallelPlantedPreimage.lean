/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.ParallelPlantedPreimage
public import Mathlib.Data.ZMod.Basic

/-!
# Secret-input preimage search regressions

The real game samples its target by evaluating the same table as the adversary's oracle.
Finite counting distinguishes any-preimage recovery from recovering the hidden input and from
independent-target search. Pure quantum strategies check the exact guessing baseline, target
dependence, singleton domains and ranges, missing mass, and both resource-bound interfaces.
-/

public section

open Quantum ProbabilityTheory MeasureTheory Matrix
open scoped ENNReal ComplexOrder Kronecker

namespace VCVioTest.QuantumParallelPlantedPreimage

/-- A half-mass input whose failed mass remains lost. -/
@[expose, reducible]
noncomputable def halfInput : SubState Unit where
  matrix := Matrix.diagonal fun _ ↦ (1 / 2 : ℂ)
  posSemidef := Matrix.PosSemidef.diagonal (by intro u; norm_num [Complex.nonneg_iff])
  trace_re_le_one := by norm_num [Matrix.trace, Matrix.diag]

/-- The public target selects the returned input; there are no oracle calls. -/
@[expose, reducible]
noncomputable def noQuery {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (out : Y → X) (ρ : SubState Unit) :
    PlantedPreimageAdversary X Y LocalSig.instruments (fun _ ↦ X) (QReg.of Unit) where
  interp _ := .instruments
  program target := QuantumComp.pure (out target)
  initial _ := ρ
  guess _ leaf := leaf.2

private theorem pure_recovery {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
    (H : X → Y) (ρ : SubState Unit) (out : X) (target : Y) :
    (parallelOracleRuntime H).evalDistMap .instruments
      (QuantumComp.pure (X := fun _ : QReg ↦ X) (A := QReg.of Unit) out)
      ρ (fun leaf ↦ H leaf.2 = target) {True} =
        ENNReal.ofReal ρ.matrix.trace.re * (if H out = target then 1 else 0) := by
  classical
  have ht : (ρ.matrix ⊗ₖ (parallelOracleRuntime H).init.matrix).trace.re =
      ρ.matrix.trace.re := by
    change (ρ.prod (SubState.basis ())).matrix.trace.re = _
    rw [SubState.trace_re_prod, SubState.trace_basis]
    norm_num
  rw [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (MeasurableSet.singleton True),
    tsum_eq_single ⟨QReg.of Unit, out⟩]
  · by_cases h : H out = target <;>
      simp [QuantumRuntime.matrix_jointPost, QuantumRuntime.run_pure,
        DSubInstrument.branch_ret_self, ht, h]
  · intro p hp
    simp [QuantumRuntime.matrix_jointPost, QuantumRuntime.run_pure,
      DSubInstrument.branch_ret_of_ne _ hp]

private theorem noQuery_eq_count {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
    (out : Y → X) (ρ : SubState Unit) :
    plantedPreimageAdvantage (noQuery out ρ) =
      ENNReal.ofReal ρ.matrix.trace.re * (Fintype.card X : ℝ≥0∞)⁻¹ *
        (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun p : X × (X → Y) ↦
          p.2 (out (p.2 p.1)) = p.2 p.1).card : ℝ≥0∞) := by
  classical
  unfold plantedPreimageAdvantage
  simp only [pure_recovery]
  have hc : (∑ p : X × (X → Y), if p.2 (out (p.2 p.1)) = p.2 p.1
      then (1 : ℝ≥0∞) else 0) =
        ((Finset.univ.filter fun p : X × (X → Y) ↦
          p.2 (out (p.2 p.1)) = p.2 p.1).card : ℝ≥0∞) := by
    rw [Finset.sum_ite]
    simp
  rw [← hc, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro secret _
  apply Finset.sum_congr rfl
  intro H _
  ring

/-- Among eighteen uniform table/secret pairs, twelve accept a fixed returned input.
Only nine have that input equal to the actual secret, so the game counts extra preimages. -/
example : (Finset.univ.filter fun p : Fin 2 × (Fin 2 → ZMod 3) ↦
    p.2 0 = p.2 p.1).card = 12 ∧
    (Finset.univ.filter fun p : Fin 2 × (Fin 2 → ZMod 3) ↦ (0 : Fin 2) = p.1).card = 9 := by
  decide

/-- A non-Boolean cyclic range gives two-thirds success without a query, rather than the
one-third probability for an independent target. -/
theorem no_query_density :
    plantedPreimageAdvantage (noQuery (fun _ : ZMod 3 ↦ (0 : Fin 2)) (SubState.basis ())) =
      2 / 3 := by
  rw [noQuery_eq_count]
  have hc : (Finset.univ.filter fun p : Fin 2 × (Fin 2 → ZMod 3) ↦
      p.2 0 = p.2 p.1).card = 12 := by decide
  norm_num [hc, SubState.trace_basis]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-- Public targets may select different programs, not only different final predicates. -/
theorem target_dependent_guess :
    plantedPreimageAdvantage
      (noQuery (fun target : ZMod 3 ↦ (if target = 0 then (0 : Fin 2) else 1))
        (SubState.basis ())) = 2 / 3 := by
  rw [noQuery_eq_count]
  have hc : (Finset.univ.filter fun p : Fin 2 × (Fin 2 → ZMod 3) ↦
      p.2 (if p.2 p.1 = 0 then 0 else 1) = p.2 p.1).card = 12 := by decide
  norm_num [hc, SubState.trace_basis]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-- Missing mass halves the exact guessing baseline and is not postselected away. -/
theorem no_query_half_mass :
    plantedPreimageAdvantage (noQuery (fun _ : ZMod 3 ↦ (0 : Fin 2)) halfInput) = 1 / 3 := by
  rw [noQuery_eq_count]
  have hc : (Finset.univ.filter fun p : Fin 2 × (Fin 2 → ZMod 3) ↦
      p.2 0 = p.2 p.1).card = 12 := by decide
  norm_num [hc, halfInput, Matrix.trace, Matrix.diag,
    ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-- The only domain input is always a preimage of the published target. -/
theorem singleton_domain :
    plantedPreimageAdvantage (noQuery (fun _ : ZMod 5 ↦ ()) (SubState.basis ())) = 1 := by
  rw [noQuery_eq_count]
  have hc : (Finset.univ.filter fun p : Unit × (Unit → ZMod 5) ↦
      p.2 () = p.2 p.1).card = 5 := by decide
  norm_num [hc, SubState.trace_basis]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-- A singleton answer group has every input as a preimage, with no avoiding-base sampler. -/
theorem singleton_range :
    plantedPreimageAdvantage (noQuery (fun _ : ZMod 1 ↦ (0 : Fin 2)) halfInput) = 1 / 2 := by
  rw [noQuery_eq_count]
  have hc : (Finset.univ.filter fun p : Fin 2 × (Fin 2 → ZMod 1) ↦
      p.2 0 = p.2 p.1).card = 2 := by decide
  norm_num [hc, halfInput, Matrix.trace, Matrix.diag,
    ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-- The point-budget theorem applies to the real target-dependent family at its exact baseline. -/
example : plantedPreimageAdvantage
    (noQuery (fun target : ZMod 3 ↦ (if target = 0 then (0 : Fin 2) else 1))
      (SubState.basis ())) ≤ 2 / 3 := by
  have h := plantedPreimageAdvantage_le_of_isPointBound
    (noQuery (fun target : ZMod 3 ↦ (if target = 0 then (0 : Fin 2) else 1))
      (SubState.basis ()))
    (q := 0) (Q := 0) (fun _ ↦ by simp) (fun _ ↦ by simp)
  norm_num [plantedTargetDensity, ENNReal.ofReal_div_of_pos] at h ⊢
  exact h.2

/-- The width-budget theorem handles singleton ranges through its unconditional cap. -/
example : plantedPreimageAdvantage (noQuery (fun _ : ZMod 1 ↦ (0 : Fin 2)) halfInput) ≤ 1 := by
  have h := plantedPreimageAdvantage_le
    (noQuery (fun _ : ZMod 1 ↦ (0 : Fin 2)) halfInput)
    (q := 0) (k := 0) (fun _ ↦ by simp) (fun _ ↦ by simp)
  simpa [plantedTargetDensity] using h

end VCVioTest.QuantumParallelPlantedPreimage
