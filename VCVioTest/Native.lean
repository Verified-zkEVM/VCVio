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

section Kernels

def advance : StateT ℝ Id ℝ := fun state ↦ pure (state, state + 1)

def continueFrom (x : ℝ) : StateT ℝ Id ℝ := fun state ↦ pure (x + state, state + 1)

theorem measurable_advance : Measurable fun state ↦ 𝒟[advance state] := by
  simp only [advance, Id.evalDist_eq_dirac, Id.run_pure]
  exact Measure.measurable_dirac.comp (measurable_id.prodMk (measurable_id.add_const 1))

theorem measurable_continueFrom :
    Measurable fun p : ℝ × ℝ ↦ 𝒟[continueFrom p.1 p.2] := by
  simp only [continueFrom, Id.evalDist_eq_dirac, Id.run_pure]
  exact Measure.measurable_dirac.comp
    ((measurable_fst.add measurable_snd).prodMk (measurable_snd.add_const 1))

example :
    StateT.evalDistKernel (advance >>= continueFrom)
        (measurable_evalDist_bind advance (fun p : ℝ × ℝ ↦ continueFrom p.1 p.2)
          measurable_advance measurable_continueFrom) =
      evalDistKernel (fun p : ℝ × ℝ ↦ continueFrom p.1 p.2) measurable_continueFrom ∘ₖ
        StateT.evalDistKernel advance measurable_advance :=
  StateT.evalDistKernel_bind advance continueFrom measurable_advance measurable_continueFrom

example : 𝒟[(advance >>= continueFrom) 0] = Measure.dirac ((1 : ℝ), (2 : ℝ)) := by
  rw [Id.evalDist_eq_dirac]
  congr 1
  simpa [StateT.run, advance, continueFrom, one_add_one_eq_two] using
    congrArg Id.run (StateT.run_bind advance continueFrom 0)

end Kernels

section ReachableEvents

variable {α : Type}

example (gen : ProbComp α) (f : α → ProbComp ℝ) {r : ℝ≥0∞}
    (h : ∀ x ∈ support gen, r ≤ 𝒟[f x] {0}) :
    r ≤ 𝒟[gen >>= f] {0} :=
  OracleComp.le_evalDist_bind_apply_of_support gen f (measurableSet_singleton 0) h

example (gen : ProbComp α) (f g : α → ProbComp ℝ)
    (h : ∀ x ∈ support gen, 𝒟[f x] {0} ≤ 𝒟[g x] {0}) :
    𝒟[gen >>= f] {0} ≤ 𝒟[gen >>= g] {0} :=
  OracleComp.evalDist_bind_apply_mono_of_support gen f g (measurableSet_singleton 0) h

example (mx : OptionT ProbComp ℝ) (h : ∀ x ∈ support mx, x ≤ 5) :
    ∀ᵐ x ∂𝒟[mx], x ≤ 5 :=
  evalDist.ae_of_forall_mem_support mx (fun x ↦ x ≤ 5)
    (measurableSet_le measurable_id measurable_const) h

example (mx : OptionT ProbComp ℝ) (h : ∀ x ∈ support mx, x ≠ 6) :
    𝒟[mx] {6} = 0 :=
  evalDist.apply_eq_zero_of_disjoint_support mx (measurableSet_singleton 6) h

example {σ β : Type} (mx : StateT σ ProbComp ℝ) (my : StateT σ ProbComp β)
    (inv : σ → Prop) (hmx : StateT.OutputIndependent mx inv)
    (hmy : StateT.PreservesInv my inv) :
    ∀ initial, inv initial →
      𝒟[my.run initial >>= fun p ↦ mx.run' p.2] = 𝒟[mx.run' initial] :=
  StateT.outputIndependent_after_preservesInv mx my inv hmx hmy

end ReachableEvents

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
