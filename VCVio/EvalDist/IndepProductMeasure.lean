/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Defs.Measure.Core
public import ToMathlib.Control.Monad.Fold
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.UniformOn

/-!
# Independent products denote product measures

`Fin.mOfFn` and `Fintype.mPi` run a finite family of computations independently and collect
their results as a function. Their denotation is Mathlib's product measure `Measure.pi`.
The finite-index proof uses the monadic product law `evalDist_pair` and Mathlib's measurable
equivalence between a successor-indexed function and its head/tail pair. Reindexing gives the
arbitrary finite-index form. Coordinate marginals use `Measure.pi_map_eval` and require the
other factors to have full mass.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

section mOfFn

variable {α : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  [MeasurableSpace α]

/-- The independent product of `n` computations denotes the product measure of their
denotations. -/
theorem evalDist_mOfFn (n : ℕ) (g : Fin n → m α) :
    𝒟[Fin.mOfFn n g] = Measure.pi fun i => 𝒟[g i] := by
  induction n with
  | zero =>
      simpa [Fin.mOfFn] using
        (Measure.pi_of_empty (fun i : Fin 0 => 𝒟[g i]) Fin.elim0).symm
  | succ n ih =>
      let e : (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
        MeasurableEquiv.piFinSuccAbove (fun _ => α) 0
      apply (MeasurableEquiv.map_measurableEquiv_injective e)
      calc
        (𝒟[Fin.mOfFn (n + 1) g]).map e =
            𝒟[e <$> Fin.mOfFn (n + 1) g] :=
          (evalDist_map (Fin.mOfFn (n + 1) g) e.measurable).symm
        _ = 𝒟[do
              let a ← g 0
              let rest ← Fin.mOfFn n (fun i => g i.succ)
              return (a, rest)] := by
          congr 1
          simp [Fin.mOfFn, e, monad_norm]
        _ = 𝒟[g 0].prod 𝒟[Fin.mOfFn n (fun i => g i.succ)] :=
          evalDist_pair (g 0) (Fin.mOfFn n fun i => g i.succ)
        _ = 𝒟[g 0].prod (Measure.pi fun i : Fin n => 𝒟[g i.succ]) := by rw [ih]
        _ = (Measure.pi fun i : Fin (n + 1) => 𝒟[g i]).map e := by
          simpa [e] using
            (measurePreserving_piFinSuccAbove
              (fun i : Fin (n + 1) => 𝒟[g i]) 0).map_eq.symm

/-- Independent draws, each uniform on its own set, denote the uniform measure on the
corresponding product set. -/
theorem evalDist_mOfFn_uniformOn_pi [Finite α] [MeasurableSingletonClass α]
    (n : ℕ) (g : Fin n → m α)
    (s : Fin n → Set α) (hg : ∀ i, 𝒟[g i] = uniformOn (s i)) :
    𝒟[Fin.mOfFn n g] = uniformOn (Set.univ.pi s) := by
  rw [evalDist_mOfFn]
  simp_rw [hg]
  exact uniformOn_pi.symm

/-- A constant family with uniform output measure denotes the uniform measure on its tuple
space. -/
theorem evalDist_mOfFn_const_uniform [Finite α] [MeasurableSingletonClass α]
    (n : ℕ) (mx : m α)
    (h : 𝒟[mx] = uniformOn Set.univ) :
    𝒟[Fin.mOfFn n (fun _ => mx)] = uniformOn Set.univ := by
  simpa using evalDist_mOfFn_uniformOn_pi n (fun _ => mx) (fun _ => Set.univ) (fun _ => h)

/-- The success mass of independent draws is the product of their success masses. -/
@[simp]
theorem evalDist_mOfFn_apply_univ (n : ℕ) (g : Fin n → m α) :
    𝒟[Fin.mOfFn n g] Set.univ = ∏ i, 𝒟[g i] Set.univ := by
  rw [evalDist_mOfFn, Measure.pi_univ]

/-- Independent products of lossless computations are lossless. -/
instance evalDist.instIsProbabilityMeasureMOfFn (n : ℕ) (g : Fin n → m α)
    [∀ i, IsProbabilityMeasure 𝒟[g i]] : IsProbabilityMeasure 𝒟[Fin.mOfFn n g] := by
  rw [evalDist_mOfFn]
  infer_instance

/-- Reading off one coordinate of an independent product recovers that factor's denotation
when all factors have full mass. -/
theorem evalDist_map_eval_mOfFn (n : ℕ) (g : Fin n → m α)
    (hg : ∀ i, 𝒟[g i] Set.univ = 1)
    (i : Fin n) : (𝒟[Fin.mOfFn n g]).map (Function.eval i) = 𝒟[g i] := by
  rw [evalDist_mOfFn, Measure.pi_map_eval]
  simp [hg]

end mOfFn

section mPi

universe v'

variable {α : Type} {m : Type → Type v'} [Monad m] [LawfulMonad m] {ι : Type} [Fintype ι]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  [MeasurableSpace α]

/-- The independent product of a finitely indexed family of computations denotes the product
measure of their denotations. -/
theorem evalDist_mPi (f : ι → m α) : 𝒟[Fintype.mPi f] = Measure.pi fun i => 𝒟[f i] := by
  let e := (Fintype.equivFin ι).symm
  have hfun : (⇑(Equiv.arrowCongr e (Equiv.refl α))) =
      (⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => α) e)) := by
    funext w i
    simp [Equiv.arrowCongr, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  rw [Fintype.mPi, hfun]
  rw [evalDist_map _ (MeasurableEquiv.piCongrLeft (fun _ : ι => α) e).measurable,
    evalDist_mOfFn]
  exact Measure.pi_map_piCongrLeft e (fun i => 𝒟[f i])

/-- A finite family, uniform on potentially different sets, denotes the uniform measure on
their product set. -/
theorem evalDist_mPi_uniformOn_pi [Finite α] [MeasurableSingletonClass α] (f : ι → m α)
    (s : ι → Set α) (hf : ∀ i, 𝒟[f i] = uniformOn (s i)) :
    𝒟[Fintype.mPi f] = uniformOn (Set.univ.pi s) := by
  rw [evalDist_mPi]
  simp_rw [hf]
  exact uniformOn_pi.symm

/-- A constant finite family with uniform output measure denotes the uniform measure on its
product space. -/
theorem evalDist_mPi_const_uniform [Finite α] [MeasurableSingletonClass α] (mx : m α)
    (h : 𝒟[mx] = uniformOn Set.univ) :
    𝒟[Fintype.mPi (fun _ : ι => mx)] = uniformOn Set.univ := by
  simpa using evalDist_mPi_uniformOn_pi (fun _ => mx) (fun _ => Set.univ) (fun _ => h)

/-- The success mass of a finite independent family factors over its indices. -/
@[simp]
theorem evalDist_mPi_apply_univ (f : ι → m α) :
    𝒟[Fintype.mPi f] Set.univ = ∏ i, 𝒟[f i] Set.univ := by
  rw [evalDist_mPi, Measure.pi_univ]

/-- A finite independent family inherits probability certificates from its factors. -/
instance evalDist.instIsProbabilityMeasureMPi (f : ι → m α)
    [∀ i, IsProbabilityMeasure 𝒟[f i]] : IsProbabilityMeasure 𝒟[Fintype.mPi f] := by
  rw [evalDist_mPi]
  infer_instance

/-- Reading off one coordinate of a finite independent product recovers that factor's
denotation when every factor has full mass. -/
theorem evalDist_map_eval_mPi (f : ι → m α) (hf : ∀ i, 𝒟[f i] Set.univ = 1) (i : ι) :
    (𝒟[Fintype.mPi f]).map (Function.eval i) = 𝒟[f i] := by
  classical
  rw [evalDist_mPi, Measure.pi_map_eval]
  simp [hf]

/-- Integrating a function of one coordinate only requires its marginal distribution. -/
theorem lintegral_evalDist_mPi_coord (f : ι → m α)
    (hf : ∀ i, 𝒟[f i] Set.univ = 1) (i : ι)
    (g : α → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ v, g (v i) ∂𝒟[Fintype.mPi f]) = ∫⁻ x, g x ∂𝒟[f i] := by
  rw [← lintegral_map hg (measurable_pi_apply i), evalDist_map_eval_mPi f hf i]

end mPi
