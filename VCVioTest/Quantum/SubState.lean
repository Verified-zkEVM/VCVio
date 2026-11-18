/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.Homogeneous
public import VCVio.Quantum.Oracle.Parallel

/-!
# Substate normalization regressions

Empty registers need no fictitious basis vector. A rank-two substate normalizes its matrix
while every operational observation retains the original successful mass.
-/

public section

open Quantum Matrix MeasureTheory
open scoped ENNReal ComplexOrder

namespace VCVioTest.QuantumSubState

/-- Normalization is defined even for a register without any basis elements. -/
example (ρ : SubState Empty) : ρ.normalize.matrix = 0 := by
  ext a
  exact a.elim

/-- An empty register has no successful mass. -/
example (ρ : SubState Empty) : ρ.mass = 0 := by
  simp [SubState.mass, Matrix.trace]

/-- Unequal populations in a rank-two mixture with successful mass one half. -/
noncomputable def unequalMixture : SubState Bool where
  matrix := Matrix.diagonal fun b ↦ if b then (3 / 8 : ℂ) else 1 / 8
  posSemidef := Matrix.PosSemidef.diagonal (by intro b; cases b <;> norm_num [Complex.nonneg_iff])
  trace_re_le_one := by norm_num [Matrix.trace, Matrix.diag, Fintype.sum_bool]

/-- Normalization preserves relative populations rather than selecting one basis state. -/
example : unequalMixture.normalize.matrix =
    Matrix.diagonal (fun b ↦ if b then (3 / 4 : ℂ) else 1 / 4) := by
  ext a b
  cases a <;> cases b <;>
    norm_num [unequalMixture, SubState.matrix_normalize, Matrix.trace, Matrix.diag,
      Fintype.sum_bool, Matrix.diagonal_apply]

/-- The original mass is one half even though the normalized matrix has trace one. -/
theorem mass_unequalMixture : unequalMixture.mass = 1 / 2 := by
  norm_num [SubState.mass, unequalMixture, Matrix.trace, Matrix.diag, Fintype.sum_bool,
    ENNReal.ofReal_div_of_pos]

/-- A pure return keeps the missing half of the mass as failure. -/
example :
    (parallelOracleRuntime (fun _ : Unit ↦ (0 : ZMod 2))).evalDist₂ .instruments
      (QuantumComp₂.pure (A := QReg.of Bool) true) unequalMixture =
        (1 / 2 : ℝ≥0∞) • Measure.dirac true := by
  rw [QuantumRuntime.evalDist₂, QuantumRuntime.run₂_pure]
  change (SubInstrument.pure true).outcomeMeasure
    (unequalMixture.prod (SubState.basis ())) = _
  rw [SubInstrument.pure, DSubInstrument.outcomeMeasure_ret, SubState.trace_re_prod,
    SubState.trace_basis]
  norm_num [unequalMixture, Matrix.trace, Matrix.diag, Fintype.sum_bool,
    ENNReal.ofReal_div_of_pos]

/-- Arbitrary stateful observations scale with the original mass, without postselection. -/
example {spec : QuantumOracleSpec} (R : QuantumRuntime spec)
    (x : QuantumComp LocalSig.instruments spec (fun _ ↦ Bool) (QReg.of Bool)) :
    R.evalDistMap .instruments x unequalMixture (fun p ↦ p.2) =
      (1 / 2 : ℝ≥0∞) • R.evalDistMap .instruments x unequalMixture.normalize (fun p ↦ p.2) := by
  rw [QuantumRuntime.evalDistMap_eq_mass_smul_normalize]
  rw [mass_unequalMixture]

end VCVioTest.QuantumSubState
