/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.PFunctorMeasure.Core
public import VCVio.OracleComp.OracleComp
import ToMathlib.Probability.UniformOn

/-!
# Measure-valued oracle specifications

An oracle specification assigns a probability measure to each query's response type.
A uniform specification identifies each chosen response measure with the uniform measure on
its response type; this is a proposition about the chosen measures, and finiteness and
inhabitedness of the response types follow from it rather than being carried as data. These
certificates are explicit: finiteness alone does not select a probabilistic interpretation.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

namespace OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- Combined signatures retain each summand's chosen answer measurable space. -/
instance addRangeMeasurableSpace {ι' : Type*} (spec' : OracleSpec.{_, v} ι')
    [∀ t, MeasurableSpace (spec.Range t)] [∀ t, MeasurableSpace (spec'.Range t)]
    (t : (spec + spec').Domain) : MeasurableSpace ((spec + spec').Range t) :=
  match t with
  | .inl _ => inferInstance
  | .inr _ => inferInstance

/-- Discrete answer spaces are preserved by combining signatures. -/
instance addRangeDiscreteMeasurableSpace {ι' : Type*} (spec' : OracleSpec.{_, v} ι')
    [∀ t, MeasurableSpace (spec.Range t)] [∀ t, MeasurableSpace (spec'.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec'.Range t)]
    (t : (spec + spec').Domain) : DiscreteMeasurableSpace ((spec + spec').Range t) :=
  match t with
  | .inl _ => inferInstance
  | .inr _ => inferInstance

/-- A measure-valued response distribution for each query in an oracle specification. -/
abbrev IsMeasureSpec (spec : OracleSpec.{u, v} ι)
    [∀ t, MeasurableSpace (spec.Range t)] :=
  PFunctor.IsMeasureSpec spec.toPFunctor

namespace IsMeasureSpec

/-- The probability measure assigned to the response of query `t`. -/
abbrev toMeasure [∀ t, MeasurableSpace (spec.Range t)] [IsMeasureSpec spec]
    (t : spec.Domain) : Measure (spec.Range t) :=
  PFunctor.IsMeasureSpec.toMeasure (P := spec.toPFunctor) t

/-- Each response measure is a probability measure. This restates the polynomial-functor
instance at the oracle API, whose response types are `spec.Range t` rather than
`spec.toPFunctor.B t`, so that instance search finds it for oracle goals. -/
instance isProbabilityMeasure_toMeasure [∀ t, MeasurableSpace (spec.Range t)]
    [IsMeasureSpec spec] (t : spec.Domain) : IsProbabilityMeasure (toMeasure t) :=
  PFunctor.IsMeasureSpec.isProbabilityMeasure (P := spec.toPFunctor) t

end IsMeasureSpec

/-- A chosen measure interpretation that samples uniformly from each response type.

This is a proposition about the chosen response measures: each one is the uniform measure on
its response type. It carries no finiteness or inhabitedness data. `uniformOn Set.univ` is a
probability measure exactly on a finite, nonempty type, which
`IsMeasureSpec.isProbabilityMeasure` records, so `IsUniformMeasureSpec.finite_range` and
`IsUniformMeasureSpec.nonempty_range` recover both facts. Statements about cardinalities take
`[Fintype (spec.Range t)]` for the queries they mention. -/
class IsUniformMeasureSpec (spec : OracleSpec.{u, v} ι)
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] extends IsMeasureSpec spec where
  /-- Each query uses the uniform probability measure on its response type. -/
  toMeasure_eq_uniform : ∀ t, toMeasure t = uniformOn Set.univ

attribute [simp] IsUniformMeasureSpec.toMeasure_eq_uniform

/-- The response measure exposed by the oracle API is uniform for a uniform specification. -/
theorem IsMeasureSpec.toMeasure_eq_uniformOn [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [IsUniformMeasureSpec spec]
    (t : spec.Domain) : toMeasure t = uniformOn Set.univ :=
  IsUniformMeasureSpec.toMeasure_eq_uniform t

/-- Select uniform measure semantics for an oracle specification whose response types are
finite and nonempty. -/
@[expose, reducible]
noncomputable def IsUniformMeasureSpec.ofFiniteNonempty
    (spec : OracleSpec.{u, v} ι)
    [∀ t, Finite (spec.Range t)] [∀ t, Nonempty (spec.Range t)]
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] : IsUniformMeasureSpec spec where
  toMeasure _ := uniformOn Set.univ
  isProbabilityMeasure _ := inferInstance
  toMeasure_eq_uniform _ := rfl

/-- Native uniform measure semantics for the finite-range selection oracle. -/
@[reducible]
noncomputable def IsUniformMeasureSpec.unifSpec : IsUniformMeasureSpec _root_.unifSpec :=
  ofFiniteNonempty _

/-- Native uniform measure semantics for the fair-coin oracle. -/
@[reducible]
noncomputable def IsUniformMeasureSpec.coinSpec : IsUniformMeasureSpec _root_.coinSpec :=
  ofFiniteNonempty _

attribute [instance] IsUniformMeasureSpec.unifSpec IsUniformMeasureSpec.coinSpec

namespace IsUniformMeasureSpec

variable [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  [IsUniformMeasureSpec spec]

/-- A uniform response measure is a probability measure only on a finite response type.

Not an instance: for a generic `spec` its conclusion `Finite (spec.Range t)` would be a
candidate for every `Finite _` goal. -/
theorem finite_range (t : spec.Domain) : Finite (spec.Range t) := by
  have h : IsMeasureSpec.toMeasure (spec := spec) t Set.univ ≠ 0 := by
    rw [measure_univ]
    exact one_ne_zero
  rw [IsMeasureSpec.toMeasure_eq_uniformOn t] at h
  exact Set.finite_univ_iff.mp (finite_of_uniformOn_ne_zero h)

/-- A uniform response measure is a probability measure only on a nonempty response type.

Not an instance, for the reason given at `finite_range`. -/
theorem nonempty_range (t : spec.Domain) : Nonempty (spec.Range t) :=
  (IsMeasureSpec.toMeasure (spec := spec) t).nonempty_of_neZero

/-- Every response has positive probability under a uniform response measure. -/
theorem toMeasure_singleton_pos (t : spec.Domain) (u : spec.Range t) :
    0 < IsMeasureSpec.toMeasure (spec := spec) t {u} := by
  have := finite_range t
  rw [IsMeasureSpec.toMeasure_eq_uniformOn t]
  refine pos_iff_ne_zero.mpr fun h => ?_
  rw [uniformOn_eq_zero_iff Set.finite_univ] at h
  simp at h

/-- On a finite response type, each response has probability the inverse cardinality. -/
theorem toMeasure_singleton (t : spec.Domain) [Fintype (spec.Range t)] (u : spec.Range t) :
    IsMeasureSpec.toMeasure (spec := spec) t {u} = (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
  have := nonempty_range t
  rw [IsMeasureSpec.toMeasure_eq_uniformOn t, uniformOn_univ_apply_singleton]

end IsUniformMeasureSpec

/-- Combining uniform specifications preserves each configured answer measure. -/
@[reducible]
noncomputable instance IsUniformMeasureSpec.add {ι' : Type*}
    (spec' : OracleSpec.{_, v} ι')
    [∀ t, MeasurableSpace (spec.Range t)] [∀ t, MeasurableSpace (spec'.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec'.Range t)]
    [IsUniformMeasureSpec spec] [IsUniformMeasureSpec spec'] :
    IsUniformMeasureSpec (spec + spec') where
  toMeasure
    | .inl t => IsMeasureSpec.toMeasure t
    | .inr t => IsMeasureSpec.toMeasure t
  isProbabilityMeasure
    | .inl t => PFunctor.IsMeasureSpec.isProbabilityMeasure (P := spec.toPFunctor) t
    | .inr t => PFunctor.IsMeasureSpec.isProbabilityMeasure (P := spec'.toPFunctor) t
  toMeasure_eq_uniform
    | .inl t => IsMeasureSpec.toMeasure_eq_uniformOn t
    | .inr t => IsMeasureSpec.toMeasure_eq_uniformOn t

end OracleSpec

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- Lifting a primitive query denotes its configured answer measure. -/
@[simp]
theorem evalDist_liftM_query [∀ t, MeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec] (t : spec.Domain) :
    𝒟[(liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))] =
      OracleSpec.IsMeasureSpec.toMeasure t := by
  change 𝒟[(PFunctor.FreeM.lift (P := spec.toPFunctor) t :
    PFunctor.FreeM spec.toPFunctor (spec.Range t))] = _
  exact PFunctor.FreeM.evalDist_lift (P := spec.toPFunctor) t

/-- A single oracle query denotes its configured answer measure. -/
theorem evalDist_query [∀ t, MeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec] (t : spec.Domain) :
    𝒟[(query t : OracleComp spec (spec.Range t))] =
      OracleSpec.IsMeasureSpec.toMeasure t := by
  rw [HasQuery.instOfMonadLift_query]
  exact evalDist_liftM_query t

/-- A query in a uniform measure specification has the uniform response measure. -/
theorem evalDist_query_uniform [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsUniformMeasureSpec spec] (t : spec.Domain) :
    𝒟[(query t : OracleComp spec (spec.Range t))] = uniformOn Set.univ := by
  rw [evalDist_query]
  exact OracleSpec.IsUniformMeasureSpec.toMeasure_eq_uniform t

/-- A program over discrete, lossless oracle responses has total output mass one. -/
theorem evalDist_apply_univ_eq_one [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec] {α : Type v} [MeasurableSpace α]
    (mx : OracleComp spec α) : 𝒟[mx] Set.univ = 1 := by
  change (PFunctor.FreeM.denote mx) Set.univ = 1
  exact (PFunctor.FreeM.isProbabilityMeasure_denote mx).measure_univ

/-- Discarding the result of a lossless oracle computation leaves the continuation's output
measure unchanged. The discarded result type needs no ambient measurable-space instance. -/
@[simp]
theorem evalDist_bind_const [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec] {α β : Type v} [MeasurableSpace β]
    (mx : OracleComp spec α) (my : OracleComp spec β) :
    𝒟[mx >>= fun _ => my] = 𝒟[my] := by
  induction mx using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t next ih =>
    rw [bind_assoc, evalDist_bind_of_discrete]
    simp_rw [ih]
    rw [Measure.bind_const, evalDist_apply_univ_eq_one, one_smul]

/-- A constant output map on a lossless oracle program is a Dirac measure.
No measurable-space instance on the discarded result type is needed. -/
@[simp]
theorem evalDist_map_const [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec] {α β : Type v} [MeasurableSpace β]
    (mx : OracleComp spec α) (b : β) :
    𝒟[(fun _ : α ↦ b) <$> mx] = Measure.dirac b := by
  rw [map_eq_bind_pure_comp]
  simp only [Function.comp_def, evalDist_bind_const, evalDist_pure]

end OracleComp
