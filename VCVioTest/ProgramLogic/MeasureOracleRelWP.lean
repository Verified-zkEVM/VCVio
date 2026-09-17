/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Relational.Measure.Oracle
public import VCVio.OracleComp.ProbComp.Basic

/-!
# Native relational oracle algebra canaries

The scoped qualitative measure algebra supports the generic relational interface, including
uncountable output types and weighted zero-mass branches. It requires no discrete backend.
-/

public section

open OracleSpec OracleComp
open scoped MeasureProgramLogic.Relational

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF, `DiscreteEvalDistCompatible] do
    if env.contains name then
      throwError "native relational oracle algebra unexpectedly imports {name}"

namespace VCVioTest.ProgramLogic.MeasureOracleRelWP

example (a b : ℝ) (R : ℝ → ℝ → Prop) :
    MAlgRelOrdered.RelWP (pure a : ProbComp ℝ) (pure b : ProbComp ℝ) R ↔ R a b := by
  simp

example (mx my : ProbComp ℝ) (f g : ℝ → ProbComp ℝ) (R : ℝ → ℝ → Prop)
    (h : MAlgRelOrdered.RelWP mx my fun a b ↦ MAlgRelOrdered.RelWP (f a) (g b) R) :
    MAlgRelOrdered.RelWP (mx >>= f) (my >>= g) R :=
  MAlgRelOrdered.relWP_bind_le mx my f g R h

/-- A finite oracle whose true branch is operationally possible but has zero mass. -/
abbrev weightedSpec : OracleSpec (Fin 1) := Fin 1 →ₒ Bool

noncomputable local instance : IsMeasureSpec weightedSpec where
  toMeasure _ := MeasureTheory.Measure.dirac false
  isProbabilityMeasure _ := inferInstance

example : MAlgRelOrdered.RelWP (weightedSpec.query 0 : OracleComp weightedSpec Bool)
    (pure false : OracleComp weightedSpec Bool) (· = ·) := by
  rw [MeasureProgramLogic.Relational.relWP_eq_wp]
  simp only [OracleComp.MeasureRelational.wp, MeasureProgramLogic.RelWP,
    OracleComp.evalDist_liftM_query, evalDist_pure, IsMeasureSpec.toMeasure,
    PFunctor.IsMeasureSpec.toMeasure]
  exact MeasureProgramLogic.couplingPost_refl (MeasureTheory.Measure.dirac false)

example (a b : ℝ) (R : ℝ → ℝ → Prop) :
    MAlgRelOrdered.RelWP (pure a : OracleComp weightedSpec ℝ)
      (pure b : OracleComp weightedSpec ℝ) R ↔ R a b := by
  simp

example (mx my : OracleComp weightedSpec ℝ)
    (f g : ℝ → OracleComp weightedSpec ℝ) (R : ℝ → ℝ → Prop)
    (h : MAlgRelOrdered.RelWP mx my fun a b ↦ MAlgRelOrdered.RelWP (f a) (g b) R) :
    MAlgRelOrdered.RelWP (mx >>= f) (my >>= g) R :=
  MAlgRelOrdered.relWP_bind_le mx my f g R h

end VCVioTest.ProgramLogic.MeasureOracleRelWP
