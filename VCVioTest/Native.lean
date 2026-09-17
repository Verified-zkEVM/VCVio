/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.Native
public import Mathlib.Tactic.GRewrite

/-!
# Native foundation regressions

Ordinary imports provide executable sampling, operational support, native probability instances,
indexed transformer semantics, and measure program logic without discrete compatibility types.
-/

public section

open MeasureTheory ProbabilityTheory Std.Internal.Do
open scoped ENNReal

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF, `NeverFail, `EvalDistCompatible, `DiscreteEvalDistCompatible] do
    if env.contains name then
      throwError "native entry point unexpectedly imports {name}"

namespace VCVioTest.Native

def sampleVector : ProbComp (Vector (Fin 3) 4) := $ᵗ _

def sampleFunction : ProbComp (Fin 4 → Fin 3) := $ᵗ _

example : Finite (Vector (Fin 3) 4) := inferInstance

example : Nonempty (Fin 4 → Fin 3) := inferInstance

noncomputable example [MeasurableSpace (Vector (Fin 3) 4)] :
    IsProbabilityMeasure 𝒟[sampleVector] := inferInstance

noncomputable example : IsProbabilityMeasure 𝒟[sampleFunction] := inferInstance

example : support sampleVector = Set.univ := by simp [sampleVector]

example : support sampleFunction = Set.univ := by simp [sampleFunction]

example [MeasurableSpace (Vector (Fin 3) 4)] [MeasurableSingletonClass (Vector (Fin 3) 4)] :
    𝒟[sampleVector] = uniformOn Set.univ :=
  SampleableType.evalDist_uniformSample

example (p : Fin 3 → Prop) [DecidablePred p] :
    Pr{let x ← $ᵗ Fin 3}[p x] = (Finset.univ.filter p).card / 3 := by simp

example : (support (ProbComp.uniformRange 2 5 (by decide))).Nonempty :=
  OracleComp.support_nonempty _

section Indexed

example (mx : StateT Bool Id Nat) (f : Nat → Prop) :
    (letI := MonadAttach.toWPMonadDemonic (m := StateT Bool Id);
      wp mx f (Lean.Order.bot : EPost.Nil)) ↔
      ∀ state, f (mx.run state).run.1 := by
  rw [MonadAttach.toWPMonadDemonic_wp,
    MonadAttach.StateT.allOutputs_iff_forall_allOutputsFrom]
  simp [MonadAttach.StateT.AllOutputsFrom, MonadAttach.StateT.supportFrom]

end Indexed

section Weighted

abbrev WeightedSpec : OracleSpec (Fin 1) := Fin 1 →ₒ Bool

noncomputable instance : OracleSpec.IsMeasureSpec WeightedSpec where
  toMeasure _ := Measure.dirac false
  isProbabilityMeasure _ := inferInstance

def guardedDraw : OptionT (OracleComp WeightedSpec) Bool := do
  let b ← WeightedSpec.query 0
  if b then failure else pure b

example : true ∈ support (WeightedSpec.query 0 : OracleComp WeightedSpec Bool) := by
  rw [OracleComp.support_query]
  trivial

noncomputable example : IsProbabilityMeasure 𝒟[guardedDraw] := by
  apply evalDist.isProbabilityMeasure_bind_of_ae
    (mx := OptionT.lift (WeightedSpec.query 0 : OracleComp WeightedSpec Bool))
    (f := fun b ↦ if b then failure else pure b) Measurable.of_discrete
  rw [OptionT.evalDist_lift, OracleComp.evalDist_liftM_query]
  simpa [OracleSpec.IsMeasureSpec.toMeasure, PFunctor.IsMeasureSpec.toMeasure] using
    (inferInstance : IsProbabilityMeasure 𝒟[(pure false : OptionT (OracleComp WeightedSpec) Bool)])

end Weighted
end VCVioTest.Native
