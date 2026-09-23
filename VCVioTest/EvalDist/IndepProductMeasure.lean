/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.IndepProduct
public import VCVio.EvalDist.Defs.Measure.Deterministic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Independent-product observations and kernels

Event observations and chosen-space real-valued observations work on payloads without a
measurable-space instance. Product kernels preserve the chosen real parameter space. Failed
unobserved factors erase a coordinate's successful mass, while reachable-coordinate elimination
needs only core lawful attachment.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF, `NeverFail, `EvalDistCompatible, `DiscreteEvalDistCompatible] do
    if env.contains name then
      throwError "native independent products unexpectedly import {name}"

namespace VCVioTest.IndepProductMeasure

universe u v

section observations

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}

example (g : Bool → m α) (p : Bool → α → Prop) :
    Pr{let v ← Fintype.mPi g}[∀ i, p i (v i)] = ∏ i, Pr{let x ← g i}[p i x] :=
  prEvent_forall_coord_mPi g p

example (g : Bool → m α) (observe : Bool → α → ℝ) :
    𝒟[(fun v i ↦ observe i (v i)) <$> Fintype.mPi g] =
      Measure.pi fun i ↦ 𝒟[observe i <$> g i] :=
  evalDist_map_coord_mPi g observe

example (g : Bool → m α) (i : Bool) (p : α → Prop)
    (hg : ∀ j, j ≠ i → Pr{
      let _ ← g j}[True] = 1) :
    Pr{let v ← Fintype.mPi g}[p (v i)] = Pr{let x ← g i}[p x] :=
  prEvent_coord_mPi g i p hg

end observations

section reachability

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [MonadAttach m] [LawfulMonadAttach m] {α : Type u}

example (g : Bool → m α) (v : Bool → α) (hv : v ∈ support (Fintype.mPi g)) :
    v false ∈ support (g false) ∧ v true ∈ support (g true) :=
  ⟨mem_support_mPi g v hv false, mem_support_mPi g v hv true⟩

end reachability

section kernels

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

example (g : ℝ → Bool → m ℝ) (hg : ∀ i, Measurable fun r ↦ 𝒟[g r i]) :
    IsSubprobabilityKernel
      (evalDistKernel (fun r ↦ Fintype.mPi (g r)) (measurable_evalDist_mPi g hg)) :=
  inferInstance

example (g : ℝ → Fin 3 → m ℝ) (hg : ∀ i, Measurable fun r ↦ 𝒟[g r i]) :
    Measurable fun r ↦ 𝒟[Fin.mOfFn 3 (g r)] := by fun_prop

example : Measurable fun r : ℝ ↦
    𝒟[Fintype.mPi (fun i : Bool ↦ (pure (if i then r else -r) : Id ℝ))] := by
  apply measurable_evalDist_mPi
  intro i
  cases i <;> simp only [evalDist_pure]
  · exact Measure.measurable_dirac.comp measurable_neg
  · exact Measure.measurable_dirac

end kernels

/-- A successful observed factor has zero marginal when another factor fails. -/
example : Pr{let v ← Fintype.mPi (fun i : Bool ↦
    if i then (none : Option ℝ) else some 7)}[v false = 7] = 0 := by
  rw [prEvent_coord_mPi_eq_mul _ false (fun x : ℝ ↦ x = 7)]
  simp [Finset.erase_insert_of_ne]

/-- Losslessness of the observed factor is unnecessary for an exact marginal. -/
example (mx : Option ℝ) (p : ℝ → Prop) :
    Pr{let v ← Fintype.mPi (fun i : Bool ↦ if i then some 7 else mx)}[p (v false)] =
      Pr{let x ← mx}[p x] := by
  rw [prEvent_coord_mPi_eq_mul]
  simp [Finset.erase_insert_of_ne]

end VCVioTest.IndepProductMeasure
