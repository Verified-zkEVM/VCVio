/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Defs.Support
public import ToMathlib.MeasureTheory.Measure.Option
public import ToMathlib.MeasureTheory.Measure.Subprobability
public import ToMathlib.Probability.ProbabilityMassFunction.Measure

/-!
# Measure-valued evaluation semantics

This module defines the primary probability boundary for VCVio computations. An
`EvalDistSemantics m` interprets `m α` as a Mathlib `Measure α` with total mass at most one.
Missing mass represents failure or nontermination. In particular, the output distribution itself
does not introduce an `Option` outcome.

Measurable spaces are explicit arguments to the semantics. There is deliberately no blanket
measurable-space instance for finite types: discrete adapters state their countability and
measurability assumptions at the boundary where they are used.

`LawfulEvalDistSemantics` records the Giry `pure` and `bind` laws. The bind law keeps the
measurability of the continuation visible; `evalDist_bind_of_discrete` is the usual cryptographic
specialization.
-/

@[expose] public section

open MeasureTheory

universe u v

/-- A measure-valued subprobability semantics for a type constructor. -/
class EvalDistSemantics (m : Type u → Type v) where
  /-- Interpret a computation as its measure of successful outputs. -/
  denote : {α : Type u} → [MeasurableSpace α] → m α → Measure α
  /-- Successful output mass is at most one. -/
  apply_univ_le_one : ∀ {α : Type u} [MeasurableSpace α] (mx : m α),
    denote mx Set.univ ≤ 1

/-- The measure of successful outputs produced by `mx`. -/
@[reducible, inline]
noncomputable def evalDist {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) : Measure α :=
  EvalDistSemantics.denote mx

/-- Evaluation-measure notation. -/
notation "𝒟[" mx "]" => evalDist mx

/-- The canonical discrete reading of a computation's measure.

This chooses the top measurable space explicitly rather than installing a blanket instance. It is
the semantics used by point/event probability notation, whose traditional API does not carry a
measurable-space parameter. General and continuous developments should use `𝒟[…]` with their
ambient measurable space instead. -/
noncomputable def discreteEvalDist {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} (mx : m α) : @Measure α ⊤ :=
  @EvalDistSemantics.denote m _ α ⊤ mx

@[simp]
theorem discreteEvalDist_apply_univ_le_one {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} (mx : m α) : discreteEvalDist mx Set.univ ≤ 1 := by
  exact @EvalDistSemantics.apply_univ_le_one m _ α ⊤ mx

@[simp]
theorem evalDist_apply_univ_le_one {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) : 𝒟[mx] Set.univ ≤ 1 :=
  EvalDistSemantics.apply_univ_le_one mx

/-- Every computation denotation is a subprobability measure. -/
instance evalDist.instIsSubprobabilityMeasure {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) : IsSubprobabilityMeasure 𝒟[mx] :=
  ⟨evalDist_apply_univ_le_one mx⟩

/-- A measure-valued semantics respects `pure` and measurable `bind` in the Giry monad. -/
class LawfulEvalDistSemantics (m : Type u → Type v) [Monad m]
    [EvalDistSemantics m] : Prop where
  /-- `pure` denotes a Dirac measure. -/
  denote_pure {α : Type u} [MeasurableSpace α] (x : α) :
    𝒟[(pure x : m α)] = Measure.dirac x
  /-- Monadic bind denotes Giry bind whenever its measure-valued continuation is measurable. -/
  denote_bind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      (mx : m α) (f : α → m β) (hf : Measurable fun x => 𝒟[f x]) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x => 𝒟[f x]

@[simp]
theorem evalDist_pure {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α : Type u} [MeasurableSpace α] (x : α) :
    𝒟[(pure x : m α)] = Measure.dirac x :=
  LawfulEvalDistSemantics.denote_pure x

theorem evalDist_bind {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (f : α → m β) (hf : Measurable fun x => 𝒟[f x]) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x => 𝒟[f x] :=
  LawfulEvalDistSemantics.denote_bind mx f hf

/-- On a discrete source type, every measure-valued continuation is measurable. -/
theorem evalDist_bind_of_discrete {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → m β) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x => 𝒟[f x] :=
  evalDist_bind mx f Measurable.of_discrete

/-- Discrete coherence between syntactic support and positive singleton mass.

The characterization is intentionally restricted to discrete output spaces. General measures
can have support points whose singleton mass is zero, so that statement is not a sound continuous
API. -/
class DiscreteEvalDistCompatible (m : Type u → Type v) [MonadLiftT m SetM]
    [EvalDistSemantics m] : Prop where
  /-- Reachable discrete outputs are exactly the positive-mass singleton outcomes. -/
  mem_support_iff_measure_singleton_ne_zero {α : Type u} [MeasurableSpace α]
      [DiscreteMeasurableSpace α] (mx : m α) (x : α) :
    x ∈ support mx ↔ 𝒟[mx] {x} ≠ 0

export DiscreteEvalDistCompatible (mem_support_iff_measure_singleton_ne_zero)

namespace SPMF

variable {α : Type u} [MeasurableSpace α]

/-- Read an `SPMF` as the measure of its successful outputs. This is the explicit compatibility
bridge from the finite executable backend to the primary measure API. -/
noncomputable def toMeasure (p : SPMF α) : Measure α :=
  p.toPMF.toMeasure.dropNone

@[simp]
theorem toMeasure_apply_univ_le_one (p : SPMF α) : p.toMeasure Set.univ ≤ 1 := by
  have hTotal : p.toPMF.toMeasure Set.univ = 1 := measure_univ
  exact (Measure.dropNone_apply_univ_le p.toPMF.toMeasure).trans_eq hTotal

@[simp]
theorem toMeasure_pure (x : α) : (pure x : SPMF α).toMeasure = Measure.dirac x := by
  rw [toMeasure, SPMF.toPMF_pure, PMF.toMeasure_pure, Measure.dropNone_dirac_some]

@[simp]
theorem toMeasure_apply_singleton [MeasurableSingletonClass α] (p : SPMF α) (x : α) :
    p.toMeasure {x} = p x := by
  rw [toMeasure, Measure.dropNone_apply_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (some x))]
  rfl

/-- On a discrete output space, applying the successful-output measure to a set agrees with the
corresponding event in the option-valued probability-mass-function backend. -/
theorem toMeasure_apply [DiscreteMeasurableSpace α] (p : SPMF α) (s : Set α) :
    p.toMeasure s = p.toPMF.toOuterMeasure (some '' s) := by
  rw [toMeasure, Measure.dropNone,
    Measure.bind_apply MeasurableSet.of_discrete Measure.measurable_dropNoneKernel.aemeasurable]
  refine Eq.trans (lintegral_congr (g := Set.indicator (some '' s) 1) ?_) ?_
  · rintro (_ | x)
    · simp
    · by_cases hx : x ∈ s <;> simp [hx]
  · rw [lintegral_indicator_one MeasurableSet.of_discrete]
    exact PMF.toMeasure_apply_eq_toOuterMeasure_apply _ MeasurableSet.of_discrete

/-- The total mass of the successful-output measure is the sum of the `SPMF` point masses. -/
@[simp]
theorem toMeasure_apply_univ [DiscreteMeasurableSpace α] (p : SPMF α) :
    p.toMeasure Set.univ = ∑' x, p x := by
  rw [toMeasure_apply, PMF.toOuterMeasure_apply, tsum_option _ ENNReal.summable]
  simp [SPMF.apply_eq_toPMF_some]

/-- On a discrete output space, the successful-output measure retains the complete `SPMF`.

Failure mass is determined by the successful masses, so dropping the explicit `none` outcome does
not lose information. -/
theorem toMeasure_injective [MeasurableSingletonClass α] :
    Function.Injective (SPMF.toMeasure : SPMF α → Measure α) := by
  intro p q hpq
  apply SPMF.ext
  intro x
  rw [← toMeasure_apply_singleton p x, ← toMeasure_apply_singleton q x, hpq]

/-- The successful-output measure commutes with measurable maps. -/
theorem toMeasure_map {β : Type u} [MeasurableSpace β]
    (p : SPMF α) (f : α → β) (hf : Measurable f) :
    (f <$> p).toMeasure = p.toMeasure.map f := by
  have hOptionMap : Measurable (Option.map f) :=
    Option.measurable_elim measurable_const (Option.measurable_some.comp hf)
  ext s hs
  rw [toMeasure, SPMF.toPMF_map]
  change (p.toPMF.map (Option.map f)).toMeasure.dropNone s = _
  rw [← p.toPMF.toMeasure_map (Option.map f) hOptionMap, toMeasure,
    Measure.map_apply hf hs]
  simp only [Measure.dropNone]
  rw [
    Measure.bind_apply hs Measure.measurable_dropNoneKernel.aemeasurable,
    Measure.bind_apply (hf hs) Measure.measurable_dropNoneKernel.aemeasurable]
  · rw [MeasureTheory.lintegral_map]
    · apply lintegral_congr
      intro value
      cases value with
      | none => simp
      | some x =>
          by_cases hx : f x ∈ s <;>
            simp [Option.map, hs, hf hs, hx]
    · exact (Measure.measurable_coe hs).comp Measure.measurable_dropNoneKernel
    · exact hOptionMap

/-- On countable discrete spaces, successful-output measures commute with `SPMF` bind. -/
theorem toMeasure_bind {β : Type u} [Countable α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] [Countable β] [DiscreteMeasurableSpace β]
    (p : SPMF α) (f : α → SPMF β) :
    (p >>= f).toMeasure = Measure.bind p.toMeasure fun x => (f x).toMeasure := by
  apply Measure.ext_of_singleton
  intro y
  rw [toMeasure_apply_singleton, bind_apply_eq_tsum,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
    MeasureTheory.lintegral_countable']
  simp only [toMeasure_apply_singleton]
  exact tsum_congr fun x => mul_comm _ _

end SPMF

/-- Compatibility semantics for monads that still expose an `SPMF` lift.

The low priority lets a direct measure interpretation, such as the free-monad fold in
`PFunctorMeasure`, win whenever both are available. -/
noncomputable instance (priority := 10) instEvalDistSemanticsOfMonadLiftTSPMF
    {m : Type u → Type v} [MonadLiftT m SPMF] : EvalDistSemantics m where
  denote mx := (liftM mx : SPMF _).toMeasure
  apply_univ_le_one mx := SPMF.toMeasure_apply_univ_le_one (liftM mx : SPMF _)

namespace MeasureTheory.Measure

variable {α : Type u} [MeasurableSpace α]

/-- Convert a countable discrete subprobability measure to the compatibility `SPMF` backend.

The missing mass is first made explicit as `none`; the resulting probability measure can then use
Mathlib's `Measure.toPMF` bridge. -/
noncomputable def toSPMF [Countable α] [DiscreteMeasurableSpace α]
    (μ : Measure α) (hμ : μ Set.univ ≤ 1) : SPMF α := by
  let _ : IsProbabilityMeasure μ.withFailure := μ.withFailure_isProbabilityMeasure hμ
  exact SPMF.mk μ.withFailure.toPMF

@[simp]
theorem toSPMF_apply [Countable α] [DiscreteMeasurableSpace α]
    (μ : Measure α) (hμ : μ Set.univ ≤ 1) (x : α) :
    μ.toSPMF hμ x = μ {x} := by
  rw [toSPMF, SPMF.apply_eq_toPMF_some, SPMF.toPMF_mk, Measure.toPMF_apply,
    Measure.withFailure_apply_some]

@[simp]
theorem toSPMF_apply_none [Countable α] [DiscreteMeasurableSpace α]
    (μ : Measure α) (hμ : μ Set.univ ≤ 1) :
    (μ.toSPMF hμ).run none = 1 - μ Set.univ := by
  let _ : IsProbabilityMeasure μ.withFailure := μ.withFailure_isProbabilityMeasure hμ
  change μ.withFailure.toPMF none = 1 - μ Set.univ
  rw [Measure.toPMF_apply, Measure.withFailure_apply_none]

/-- Converting a discrete subprobability measure to `SPMF` and back preserves the measure. -/
@[simp]
theorem toSPMF_toMeasure [Countable α] [DiscreteMeasurableSpace α]
    (μ : Measure α) (hμ : μ Set.univ ≤ 1) :
    (μ.toSPMF hμ).toMeasure = μ := by
  apply Measure.ext_of_singleton
  intro x
  simp

/-- Converting an `SPMF` to its successful-output measure and back preserves the `SPMF`. -/
@[simp]
theorem _root_.SPMF.toMeasure_toSPMF [Countable α] [DiscreteMeasurableSpace α]
    (p : SPMF α) :
    p.toMeasure.toSPMF (SPMF.toMeasure_apply_univ_le_one p) = p := by
  apply SPMF.ext
  intro x
  simp

end MeasureTheory.Measure
