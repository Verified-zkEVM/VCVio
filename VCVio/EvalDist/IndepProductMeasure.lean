/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.IndepProduct
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Independent products denote product measures

`Fin.mOfFn` and `Fintype.mPi` run a family of computations independently and collect the
results as a function. On the measure side their denotation is Mathlib's product measure
`Measure.pi`. The proof does not touch the Giry monad at all: `Measure.pi_eq` characterizes the
product measure by its values on measurable boxes, and on a box the façade bridge
`evalDist_apply` turns the question into the coordinatewise event probability, which
`probEvent_forall_coord_mOfFn`/`probEvent_forall_coord_mPi` already factor. So the statement holds
for every semantics that satisfies `DiscreteEvalDistCompatible`, with no lawfulness assumption.
-/

@[expose] public section

open MeasureTheory

universe u v

section mOfFn

variable {α : Type u} {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF]
  [LawfulMonadLiftT m SPMF] [EvalDistSemantics m] [DiscreteEvalDistCompatible m]
  [MeasurableSpace α]

/-- The independent product of `n` computations denotes the product measure of their
denotations. -/
theorem evalDist_mOfFn (n : ℕ) (g : Fin n → m α) :
    𝒟[Fin.mOfFn n g] = Measure.pi fun i => 𝒟[g i] := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [evalDist_apply _ (MeasurableSet.univ_pi hs)]
  simp only [Set.mem_univ_pi]
  rw [probEvent_forall_coord_mOfFn n g fun i x => x ∈ s i]
  exact Finset.prod_congr rfl fun i _ => (evalDist_apply _ (hs i)).symm

end mOfFn

section mPi

universe v'

variable {α : Type} {m : Type → Type v'} [Monad m] [LawfulMonad m] {ι : Type} [Fintype ι]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [EvalDistSemantics m]
  [DiscreteEvalDistCompatible m] [MeasurableSpace α]

/-- The independent product of a finitely indexed family of computations denotes the product
measure of their denotations. -/
theorem evalDist_mPi (f : ι → m α) : 𝒟[Fintype.mPi f] = Measure.pi fun i => 𝒟[f i] := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [evalDist_apply _ (MeasurableSet.univ_pi hs)]
  simp only [Set.mem_univ_pi]
  rw [probEvent_forall_coord_mPi f fun i x => x ∈ s i]
  exact Finset.prod_congr rfl fun i _ => (evalDist_apply _ (hs i)).symm

end mPi
