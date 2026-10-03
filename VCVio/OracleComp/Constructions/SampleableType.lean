/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.EvalDist
public import VCVio.EvalDist.Monad.Map
public import VCVio.EvalDist.Prod
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.EvalDist.MeasureSpec
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import VCVio.EvalDist.Monad.UniformTable
public import ToMathlib.Probability.UniformOn
public import ToMathlib.Data.FinEnum
public import Init.Data.UInt.Lemmas
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Vector

/-!
# Uniform Selection Over a Type

This file defines a typeclass `SampleableType β` for types `β` with a canonical uniform selection
operation, using the `ProbComp` monad.

Unlike `HasUniformSelect`, the class certifies full support and the uniform output measure.
-/

@[expose] public section

universe u v w

open ENNReal MeasureTheory ProbabilityTheory

variable (α : Type) [hα : SampleableType α]

@[simp, grind =]
lemma finSupport_uniformSample [Fintype α] [DecidableEq α] :
    finSupport ($ᵗ α) = Finset.univ := by aesop

section Marginalization

/-- Patch a uniform function table at every point of a list `l`, drawing one fresh uniform value
per list entry. With `l = []` the table is returned unchanged; with `l = d :: ds` the tail is
patched first and the head point `d` is then overwritten with a fresh uniform draw.

This is the iterated form of `Function.update` used by `evalDist_uniformSample_patchList`: the
outermost update is at the head, so the list is consumed head-first. -/
def patchTable {D R : Type} [DecidableEq D] [SampleableType R] :
    List D → (D → R) → ProbComp (D → R)
  | [], g => pure g
  | d :: ds, g => do
      let g' ← patchTable ds g
      let u ← $ᵗ R
      pure (Function.update g' d u)

@[simp] lemma patchTable_nil {D R : Type} [DecidableEq D] [SampleableType R] (g : D → R) :
    patchTable [] g = pure g := rfl

lemma patchTable_cons {D R : Type} [DecidableEq D] [SampleableType R]
    (d : D) (ds : List D) (g : D → R) :
    patchTable (d :: ds) g =
      (do let g' ← patchTable ds g; let u ← $ᵗ R; pure (Function.update g' d u)) := rfl

/-- Patching a uniform table at a finite list of coordinates with independent uniform
draws preserves its output measure. Repeated coordinates are allowed. -/
theorem evalDist_uniformSample_patchList
    {D R : Type} [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [MeasurableSpace R] [MeasurableSingletonClass R]
    [SampleableType R] [SampleableType (D → R)] (l : List D) :
    𝒟[do let g ← $ᵗ (D → R); patchTable l g] = 𝒟[$ᵗ (D → R)] := by
  induction l with
  | nil => simp [patchTable]
  | cons d ds ih =>
      let table : ProbComp (D → R) := do let g ← $ᵗ (D → R); patchTable ds g
      have hstep :
          𝒟[do let g ← $ᵗ (D → R); patchTable (d :: ds) g] =
            𝒟[do let g ← table; let u ← $ᵗ R; pure (Function.update g d u)] := by
        simp [table, patchTable_cons, bind_assoc]
      rw [hstep, evalDist_bind_of_discrete table, ih]
      rw [← evalDist_bind_of_discrete]
      have hswap := evalDist_bind_bind_swap ($ᵗ (D → R)) ($ᵗ R)
        (fun g u => pure (Function.update g d u)) Measurable.of_discrete
      rw [hswap]
      simpa using evalDist_bind_bind_update ($ᵗ R) ($ᵗ (D → R))
        SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample d pure

end Marginalization
