/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.StateSeparating.MeasureDistEquiv

/-!
# Weighted stateful-handler measure equivalence

A weighted handler can be observationally equivalent to a constant handler while still having
more structurally possible outputs. Equivalence lifts through every adaptive client without
uniformity or positive mass on each operational branch.
-/

public section

open OracleSpec OracleComp QueryImpl.Stateful MeasureTheory

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "native stateful handler API unexpectedly imports {name}"

namespace VCVioTest.StateSeparating.NativeMeasure

abbrev WeightedSpec : OracleSpec (Fin 1) := Fin 1 →ₒ Bool

noncomputable instance : IsMeasureSpec WeightedSpec where
  toMeasure _ := Measure.dirac false
  isProbabilityMeasure _ := inferInstance

def drawHandler : QueryImpl.Stateful WeightedSpec WeightedSpec Unit := fun _ ↦
  StateT.mk fun state ↦ (fun b ↦ (b, state)) <$> WeightedSpec.query 0

def constantHandler : QueryImpl.Stateful WeightedSpec WeightedSpec Unit := fun _ ↦
  StateT.mk fun state ↦ pure (false, state)

theorem handlers_equiv : MeasureDistEquiv drawHandler () constantHandler () := by
  apply MeasureDistEquiv.of_step
  intro operation state outputSpace
  simp only [drawHandler, constantHandler, StateT.run_mk,
    _root_.evalDist_map_of_discrete, evalDist_pure, OracleComp.evalDist_liftM_query]
  simp only [IsMeasureSpec.toMeasure, PFunctor.IsMeasureSpec.toMeasure]
  exact Measure.map_dirac' Measurable.of_discrete false

example (client : OracleComp WeightedSpec Bool) :
    Pr{let b ← drawHandler.run () client}[b = true] =
      Pr{let b ← constantHandler.run () client}[b = true] :=
  handlers_equiv.prEvent_eq client _

example : (true, ()) ∈ support ((drawHandler 0).run ()) := by simp [drawHandler]

example : (true, ()) ∉ support ((constantHandler 0).run ()) := by simp [constantHandler]

example (μ : Measure Bool) [IsProbabilityMeasure μ] : μ {true} + μ {false} = 1 := by simp

example (μ : Measure Bool) [IsProbabilityMeasure μ] : μ {true} + μ {false} = 1 := by grind

end VCVioTest.StateSeparating.NativeMeasure
