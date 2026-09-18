/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Kernel
public import ToMathlib.Control.Monad.Fold
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.UniformOn

/-!
# Independent products denote product measures

`Fin.mOfFn` and `Fintype.mPi` run a finite family of computations independently and collect
their results as a function. Their denotation is Mathlib's product measure `Measure.pi`.
The finite-index proof uses the monadic product law `evalDist_pair` and Mathlib's measurable
equivalence between a successor-indexed function and its head/tail pair. Reindexing gives the
arbitrary finite-index form. Coordinate marginals use `Measure.pi_map_eval` and retain the
other factors’ success masses. Coordinate observations measure only their chosen output
space, and measurable factor families assemble into measurable product families using
Mathlib kernel products.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u v w

section mOfFn

variable {α : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  [MeasurableSpace α]

/-- The independent product of `n` computations denotes the product measure of their
denotations. -/
theorem evalDist_mOfFn (n : ℕ) (g : Fin n → m α) :
    𝒟[Fin.mOfFn n g] = Measure.pi fun i ↦ 𝒟[g i] := by
  induction n with
  | zero =>
      simpa [Fin.mOfFn] using
        (Measure.pi_of_empty (fun i : Fin 0 ↦ 𝒟[g i]) Fin.elim0).symm
  | succ n ih =>
      let e : (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
        MeasurableEquiv.piFinSuccAbove (fun _ ↦ α) 0
      apply (MeasurableEquiv.map_measurableEquiv_injective e)
      calc
        (𝒟[Fin.mOfFn (n + 1) g]).map e =
            𝒟[e <$> Fin.mOfFn (n + 1) g] :=
          (evalDist_map (Fin.mOfFn (n + 1) g) e.measurable).symm
        _ = 𝒟[do
              let a ← g 0
              let rest ← Fin.mOfFn n (fun i ↦ g i.succ)
              return (a, rest)] := by
          congr 1
          simp [Fin.mOfFn, e, monad_norm]
        _ = 𝒟[g 0].prod 𝒟[Fin.mOfFn n (fun i ↦ g i.succ)] :=
          evalDist_pair (g 0) (Fin.mOfFn n fun i ↦ g i.succ)
        _ = 𝒟[g 0].prod (Measure.pi fun i : Fin n ↦ 𝒟[g i.succ]) := by rw [ih]
        _ = (Measure.pi fun i : Fin (n + 1) ↦ 𝒟[g i]).map e := by
          simpa [e] using
            (measurePreserving_piFinSuccAbove
              (fun i : Fin (n + 1) ↦ 𝒟[g i]) 0).map_eq.symm

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
    𝒟[Fin.mOfFn n (fun _ ↦ mx)] = uniformOn Set.univ := by
  simpa using evalDist_mOfFn_uniformOn_pi n (fun _ ↦ mx) (fun _ ↦ Set.univ) (fun _ ↦ h)

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

/-- A coordinate marginal retains the total masses of the other independent factors. -/
theorem evalDist_map_eval_mOfFn_eq_smul (n : ℕ) (g : Fin n → m α) (i : Fin n) :
    (𝒟[Fin.mOfFn n g]).map (Function.eval i) =
      (∏ j ∈ Finset.univ.erase i, 𝒟[g j] Set.univ) • 𝒟[g i] := by
  rw [evalDist_mOfFn, Measure.pi_map_eval]

/-- Reading off one coordinate of an independent product recovers that factor's denotation
when all factors have full mass. -/
theorem evalDist_map_eval_mOfFn (n : ℕ) (g : Fin n → m α)
    (hg : ∀ i, 𝒟[g i] Set.univ = 1)
    (i : Fin n) : (𝒟[Fin.mOfFn n g]).map (Function.eval i) = 𝒟[g i] := by
  rw [evalDist_map_eval_mOfFn_eq_smul]
  simp [hg]

end mOfFn

section mPi

universe v'

variable {α : Type} {m : Type → Type v'} [Monad m] [LawfulMonad m] {ι : Type} [Fintype ι]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  [MeasurableSpace α]

/-- The independent product of a finitely indexed family of computations denotes the product
measure of their denotations. -/
theorem evalDist_mPi (f : ι → m α) : 𝒟[Fintype.mPi f] = Measure.pi fun i ↦ 𝒟[f i] := by
  let e := (Fintype.equivFin ι).symm
  have hfun : (⇑(Equiv.arrowCongr e (Equiv.refl α))) =
      (⇑(MeasurableEquiv.piCongrLeft (fun _ : ι ↦ α) e)) := by
    funext w i
    simp [Equiv.arrowCongr, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  rw [Fintype.mPi, hfun]
  rw [evalDist_map _ (MeasurableEquiv.piCongrLeft (fun _ : ι ↦ α) e).measurable,
    evalDist_mOfFn]
  exact Measure.pi_map_piCongrLeft e (fun i ↦ 𝒟[f i])

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
    𝒟[Fintype.mPi (fun _ : ι ↦ mx)] = uniformOn Set.univ := by
  simpa using evalDist_mPi_uniformOn_pi (fun _ ↦ mx) (fun _ ↦ Set.univ) (fun _ ↦ h)

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

/-- A finite family's coordinate marginal retains every other factor's total mass. -/
theorem evalDist_map_eval_mPi_eq_smul [DecidableEq ι] (f : ι → m α) (i : ι) :
    (𝒟[Fintype.mPi f]).map (Function.eval i) =
      (∏ j ∈ Finset.univ.erase i, 𝒟[f j] Set.univ) • 𝒟[f i] := by
  rw [evalDist_mPi, Measure.pi_map_eval]

/-- Reading off one coordinate of a finite independent product recovers that factor's
denotation when every factor has full mass. -/
theorem evalDist_map_eval_mPi (f : ι → m α) (hf : ∀ i, 𝒟[f i] Set.univ = 1) (i : ι) :
    (𝒟[Fintype.mPi f]).map (Function.eval i) = 𝒟[f i] := by
  classical
  rw [evalDist_map_eval_mPi_eq_smul]
  simp [hf]

/-- Integrating one coordinate retains the other factors' success masses. -/
theorem lintegral_evalDist_mPi_coord_eq_mul [DecidableEq ι] (f : ι → m α) (i : ι)
    (g : α → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ v, g (v i) ∂𝒟[Fintype.mPi f]) =
      (∏ j ∈ Finset.univ.erase i, 𝒟[f j] Set.univ) * ∫⁻ x, g x ∂𝒟[f i] := by
  rw [← lintegral_map hg (measurable_pi_apply i), evalDist_map_eval_mPi_eq_smul,
    lintegral_smul_measure, smul_eq_mul]

/-- Integrating a function of one coordinate only requires its marginal distribution. -/
theorem lintegral_evalDist_mPi_coord (f : ι → m α)
    (hf : ∀ i, 𝒟[f i] Set.univ = 1) (i : ι)
    (g : α → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ v, g (v i) ∂𝒟[Fintype.mPi f]) = ∫⁻ x, g x ∂𝒟[f i] := by
  rw [← lintegral_map hg (measurable_pi_apply i), evalDist_map_eval_mPi f hf i]

end mPi

/-- Coordinate observations of independent draws denote a product measure, with no
measurable space required on the original payloads. -/
theorem evalDist_map_coord_mOfFn {α β : Type u} {m : Type u → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [MeasurableSpace β] (n : ℕ) (g : Fin n → m α) (f : Fin n → α → β) :
    𝒟[(fun v i ↦ f i (v i)) <$> Fin.mOfFn n g] = Measure.pi fun i ↦ 𝒟[f i <$> g i] := by
  rw [Fin.mOfFn_map, evalDist_mOfFn]

/-- Observations of a finite independent family denote the product of the observed factors. -/
theorem evalDist_map_coord_mPi {α β : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [MeasurableSpace β] {ι : Type} [Fintype ι] (g : ι → m α) (f : ι → α → β) :
    𝒟[(fun v i ↦ f i (v i)) <$> Fintype.mPi g] = Measure.pi fun i ↦ 𝒟[f i <$> g i] := by
  rw [Fintype.mPi_map, evalDist_mPi]

/-- A measurable family of factors gives a measurable family of independent products. -/
@[fun_prop]
theorem measurable_evalDist_mOfFn {α : Type u} {ρ : Type w} {m : Type u → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [MeasurableSpace α] [MeasurableSpace ρ]
    (n : ℕ) (g : ρ → Fin n → m α)
    (hg : ∀ i, Measurable fun r ↦ 𝒟[g r i]) :
    Measurable fun r ↦ 𝒟[Fin.mOfFn n (g r)] := by
  induction n with
  | zero =>
      simp only [Fin.mOfFn, evalDist_pure]
      exact measurable_const
  | succ n ih =>
      let κ := evalDistKernel (fun r ↦ g r 0) (hg 0)
      let η := evalDistKernel (fun r ↦ Fin.mOfFn n fun i ↦ g r i.succ)
        (ih (fun r i ↦ g r i.succ) (fun i ↦ hg i.succ))
      have hcons : Measurable (fun z : α × (Fin n → α) ↦
          (Fin.cons z.1 z.2 : Fin (n + 1) → α)) := by
        apply measurable_pi_iff.mpr
        intro i
        exact Fin.cases measurable_fst (fun j ↦ (measurable_pi_apply j).comp measurable_snd) i
      have h (r : ρ) :
          ((κ ×ₖ η).map (fun z : α × (Fin n → α) ↦ (Fin.cons z.1 z.2 : Fin (n + 1) → α))) r =
            𝒟[Fin.mOfFn (n + 1) (g r)] := by
        rw [Kernel.map_apply _ hcons, Kernel.prod_apply]
        simp only [κ, η, evalDistKernel_apply]
        rw [Fin.mOfFn_succ_eq_map_pair, evalDist_map _ hcons, evalDist_pair]
      rw [← funext h]
      exact ((κ ×ₖ η).map (fun z : α × (Fin n → α) ↦
        (Fin.cons z.1 z.2 : Fin (n + 1) → α))).measurable

/-- Measurable factors give a measurable finite independent family. -/
@[fun_prop]
theorem measurable_evalDist_mPi {α : Type} {ρ : Type w} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [MeasurableSpace α] [MeasurableSpace ρ] {ι : Type} [Fintype ι]
    (g : ρ → ι → m α) (hg : ∀ i, Measurable fun r ↦ 𝒟[g r i]) :
    Measurable fun r ↦ 𝒟[Fintype.mPi (g r)] := by
  let e := (Fintype.equivFin ι).symm
  let reindex := MeasurableEquiv.piCongrLeft (fun _ : ι ↦ α) e
  have hfun : (⇑(Equiv.arrowCongr e (Equiv.refl α))) = ⇑reindex := by
    funext w i
    simp [reindex, Equiv.arrowCongr, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  have h (r : ρ) : 𝒟[Fintype.mPi (g r)] =
      (𝒟[Fin.mOfFn (Fintype.card ι) fun k ↦ g r (e k)]).map reindex := by
    rw [Fintype.mPi, hfun, evalDist_map _ reindex.measurable]
  simp_rw [h]
  exact (Measure.measurable_map reindex reindex.measurable).comp
    (measurable_evalDist_mOfFn _ _ fun k ↦ hg (e k))
