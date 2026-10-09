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

/-- A probability measure on the answers to each query of an oracle specification.

Oracle answers carry the discrete measurable structure, so a chosen measure is determined by the
mass of single answers and no measurable-space arguments appear on answer types. Answer types
with another measurable structure are modeled by `PFunctor.IsMeasureSpec` on the underlying
polynomial functor. -/
abbrev IsMeasureSpec (spec : OracleSpec.{u, v} ι) :=
  @PFunctor.IsMeasureSpec spec.toPFunctor fun _ ↦ ⊤

namespace IsMeasureSpec

/-- The probability measure assigned to the answer of query `t`. -/
abbrev toMeasure [IsMeasureSpec spec] (t : spec.Domain) : @Measure (spec.Range t) ⊤ :=
  @PFunctor.IsMeasureSpec.toMeasure spec.toPFunctor (fun _ ↦ ⊤) _ t

/-- Each answer measure is a probability measure. This restates the polynomial-functor instance at
the oracle API, whose answer types are `spec.Range t` rather than `spec.toPFunctor.B t`, so that
instance search finds it for oracle goals. -/
instance isProbabilityMeasure_toMeasure [IsMeasureSpec spec] (t : spec.Domain) :
    @IsProbabilityMeasure (spec.Range t) ⊤ (toMeasure t) :=
  @PFunctor.IsMeasureSpec.isProbabilityMeasure spec.toPFunctor (fun _ ↦ ⊤) _ t

end IsMeasureSpec

/-- Combining specifications combines their answer measures. -/
@[reducible]
noncomputable instance IsMeasureSpec.add {ι' : Type*} (spec' : OracleSpec.{_, v} ι')
    [IsMeasureSpec spec] [IsMeasureSpec spec'] : IsMeasureSpec (spec + spec') :=
  @PFunctor.IsMeasureSpec.mk (spec + spec').toPFunctor (fun _ ↦ ⊤)
    (fun
      | .inl t => IsMeasureSpec.toMeasure t
      | .inr t => IsMeasureSpec.toMeasure t)
    (fun
      | .inl t => IsMeasureSpec.isProbabilityMeasure_toMeasure t
      | .inr t => IsMeasureSpec.isProbabilityMeasure_toMeasure t)

/-- A chosen measure interpretation that samples uniformly from each answer type.

This is a proposition about the chosen answer measures: each one is the uniform measure on its
answer type. It carries no finiteness or inhabitedness data. `uniformOn Set.univ` is a
probability measure exactly on a finite, nonempty type, which
`IsMeasureSpec.isProbabilityMeasure` records, so `IsUniformMeasureSpec.finite_range` and
`IsUniformMeasureSpec.nonempty_range` recover both facts. Statements about cardinalities take
`[Fintype (spec.Range t)]` for the queries they mention. -/
class IsUniformMeasureSpec (spec : OracleSpec.{u, v} ι) extends IsMeasureSpec spec where
  /-- Each query uses the uniform probability measure on its answer type. -/
  toMeasure_eq_uniform : ∀ t, toMeasure t = @uniformOn (spec.Range t) ⊤ Set.univ

attribute [simp] IsUniformMeasureSpec.toMeasure_eq_uniform

/-- The answer measure exposed by the oracle API is uniform for a uniform specification. -/
theorem IsMeasureSpec.toMeasure_eq_uniformOn [IsUniformMeasureSpec spec] (t : spec.Domain) :
    toMeasure t = @uniformOn (spec.Range t) ⊤ Set.univ :=
  IsUniformMeasureSpec.toMeasure_eq_uniform t

/-- Select uniform measure semantics for an oracle specification whose answer types are finite
and nonempty. -/
@[expose, reducible]
noncomputable def IsUniformMeasureSpec.ofFiniteNonempty (spec : OracleSpec.{u, v} ι)
    [∀ t, Finite (spec.Range t)] [∀ t, Nonempty (spec.Range t)] : IsUniformMeasureSpec spec where
  toMeasure _ := @uniformOn _ ⊤ Set.univ
  isProbabilityMeasure t :=
    letI : MeasurableSpace (spec.Range t) := ⊤
    inferInstance
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

variable [IsUniformMeasureSpec spec]

/-- A uniform answer measure is a probability measure only on a finite answer type.

Not an instance: for a generic `spec` its conclusion `Finite (spec.Range t)` would be a
candidate for every `Finite _` goal. -/
theorem finite_range (t : spec.Domain) : Finite (spec.Range t) := by
  let : MeasurableSpace (spec.Range t) := ⊤
  have h : IsMeasureSpec.toMeasure (spec := spec) t Set.univ ≠ 0 := by
    rw [measure_univ]
    exact one_ne_zero
  rw [IsMeasureSpec.toMeasure_eq_uniformOn t] at h
  exact Set.finite_univ_iff.mp (finite_of_uniformOn_ne_zero h)

/-- A uniform answer measure is a probability measure only on a nonempty answer type.

Not an instance, for the reason given at `finite_range`. -/
theorem nonempty_range (t : spec.Domain) : Nonempty (spec.Range t) :=
  letI : MeasurableSpace (spec.Range t) := ⊤
  (IsMeasureSpec.toMeasure (spec := spec) t).nonempty_of_neZero

/-- Every answer has positive probability under a uniform answer measure. -/
theorem toMeasure_singleton_pos (t : spec.Domain) (u : spec.Range t) :
    0 < IsMeasureSpec.toMeasure (spec := spec) t {u} := by
  let : MeasurableSpace (spec.Range t) := ⊤
  have := finite_range t
  rw [IsMeasureSpec.toMeasure_eq_uniformOn t]
  refine pos_iff_ne_zero.mpr fun h => ?_
  rw [uniformOn_eq_zero_iff Set.finite_univ] at h
  simp at h

/-- On a finite answer type, each answer has probability the inverse cardinality. -/
theorem toMeasure_singleton (t : spec.Domain) [Fintype (spec.Range t)] (u : spec.Range t) :
    IsMeasureSpec.toMeasure (spec := spec) t {u} = (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace (spec.Range t) := ⊤
  have := nonempty_range t
  rw [IsMeasureSpec.toMeasure_eq_uniformOn t, uniformOn_univ_apply_singleton]

/-- A uniform answer measure observed in any measurable structure on the answers is the uniform
measure of that structure. -/
theorem trim_toMeasure (t : spec.Domain) {m : MeasurableSpace (spec.Range t)} :
    (IsMeasureSpec.toMeasure (spec := spec) t).trim le_top =
      @uniformOn (spec.Range t) m Set.univ := by
  have := finite_range t
  let : Fintype (spec.Range t) := Fintype.ofFinite _
  ext s hs
  rw [trim_measurableSet_eq _ hs, IsMeasureSpec.toMeasure_eq_uniformOn t,
    @uniformOn_univ _ ⊤ _ s, uniformOn_univ, Measure.count_apply hs,
    @Measure.count_apply _ ⊤ _ MeasurableSpace.measurableSet_top]

end IsUniformMeasureSpec

/-- Combining uniform specifications preserves each configured answer measure. -/
@[reducible]
noncomputable instance IsUniformMeasureSpec.add {ι' : Type*} (spec' : OracleSpec.{_, v} ι')
    [IsUniformMeasureSpec spec] [IsUniformMeasureSpec spec'] :
    IsUniformMeasureSpec (spec + spec') where
  toIsMeasureSpec := IsMeasureSpec.add spec'
  toMeasure_eq_uniform
    | .inl t => IsMeasureSpec.toMeasure_eq_uniformOn (spec := spec) t
    | .inr t => IsMeasureSpec.toMeasure_eq_uniformOn (spec := spec') t

end OracleSpec

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- Oracle computations denote the measure fold of their chosen answer measures. -/
noncomputable instance (priority := 30) instEvalDistSemantics [OracleSpec.IsMeasureSpec spec] :
    EvalDistSemantics (OracleComp spec) :=
  letI : ∀ a, MeasurableSpace (spec.toPFunctor.B a) := fun _ ↦ ⊤
  PFunctor.FreeM.instEvalDistSemanticsFreeM

/-- Oracle computations denote `pure` as a Dirac measure. -/
noncomputable instance (priority := 30) instLawfulPureEvalDistSemantics
    [OracleSpec.IsMeasureSpec spec] : LawfulPureEvalDistSemantics (OracleComp spec) :=
  letI : ∀ a, MeasurableSpace (spec.toPFunctor.B a) := fun _ ↦ ⊤
  PFunctor.FreeM.instLawfulPureEvalDistSemanticsFreeM

/-- Over discrete oracle answers, the measure semantics satisfies the Giry monad laws. -/
noncomputable instance (priority := 30) instLawfulEvalDistSemantics
    [OracleSpec.IsMeasureSpec spec] : LawfulEvalDistSemantics (OracleComp spec) :=
  letI : ∀ a, MeasurableSpace (spec.toPFunctor.B a) := fun _ ↦ ⊤
  letI : ∀ a, DiscreteMeasurableSpace (spec.toPFunctor.B a) := fun _ ↦ inferInstanceAs
    (@DiscreteMeasurableSpace _ ⊤)
  PFunctor.FreeM.instLawfulEvalDistSemanticsFreeM

/-- Lifting a primitive query denotes its configured answer measure, trimmed to the measurable
structure observing the answer. -/
theorem evalDist_liftM_query [OracleSpec.IsMeasureSpec spec] (t : spec.Domain)
    {_ : MeasurableSpace (spec.Range t)} :
    𝒟[(liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))] =
      @Measure.trim _ _ ⊤ (OracleSpec.IsMeasureSpec.toMeasure t) le_top := by
  exact @PFunctor.FreeM.evalDist_lift_of_le spec.toPFunctor (fun _ ↦ ⊤) _ t _ le_top

/-- A single oracle query denotes its configured answer measure, trimmed to the measurable
structure observing the answer. -/
theorem evalDist_query [OracleSpec.IsMeasureSpec spec] (t : spec.Domain)
    {_ : MeasurableSpace (spec.Range t)} :
    𝒟[(query t : OracleComp spec (spec.Range t))] =
      @Measure.trim _ _ ⊤ (OracleSpec.IsMeasureSpec.toMeasure t) le_top := by
  rw [HasQuery.instOfMonadLift_query]
  exact evalDist_liftM_query t

/-- A measurable event of a lifted query has its configured answer probability. -/
@[simp]
theorem evalDist_liftM_query_apply [OracleSpec.IsMeasureSpec spec] (t : spec.Domain)
    {_ : MeasurableSpace (spec.Range t)} {s : Set (spec.Range t)} (hs : MeasurableSet s) :
    𝒟[(liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))] s =
      OracleSpec.IsMeasureSpec.toMeasure t s := by
  rw [evalDist_liftM_query, trim_measurableSet_eq _ hs]

/-- A lifted query in a uniform measure specification has the uniform answer measure in every
measurable structure on its answers. -/
theorem evalDist_liftM_query_uniform [OracleSpec.IsUniformMeasureSpec spec] (t : spec.Domain)
    {_ : MeasurableSpace (spec.Range t)} :
    𝒟[(liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))] = uniformOn Set.univ := by
  rw [evalDist_liftM_query]
  exact OracleSpec.IsUniformMeasureSpec.trim_toMeasure t

/-- A query in a uniform measure specification has the uniform answer measure in every measurable
structure on its answers. -/
theorem evalDist_query_uniform [OracleSpec.IsUniformMeasureSpec spec] (t : spec.Domain)
    {_ : MeasurableSpace (spec.Range t)} :
    𝒟[(query t : OracleComp spec (spec.Range t))] = uniformOn Set.univ := by
  rw [HasQuery.instOfMonadLift_query]
  exact evalDist_liftM_query_uniform t

/-- A uniform-selection query on `Fin (n + 1)` has the uniform answer measure. Stated for the
concrete answer type, so it applies where the answer type appears reduced. -/
@[simp]
theorem evalDist_liftM_unifSpec_query (n : ℕ) {_ : MeasurableSpace (Fin (n + 1))} :
    𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : OracleComp unifSpec (Fin (n + 1)))] =
      uniformOn Set.univ :=
  evalDist_liftM_query_uniform n

/-- A fair-coin query has the uniform answer measure on `Bool`. -/
@[simp]
theorem evalDist_liftM_coinSpec_query {_ : MeasurableSpace Bool} :
    𝒟[(liftM (OracleSpec.query (spec := coinSpec) ()) : OracleComp coinSpec Bool)] =
      uniformOn Set.univ :=
  evalDist_liftM_query_uniform ()

/-- A program over discrete, lossless oracle responses has total output mass one. -/
theorem evalDist_apply_univ_eq_one
    [OracleSpec.IsMeasureSpec spec] {α : Type v} [MeasurableSpace α]
    (mx : OracleComp spec α) : 𝒟[mx] Set.univ = 1 := by
  let : ∀ a, MeasurableSpace (spec.toPFunctor.B a) := fun _ ↦ ⊤
  change (PFunctor.FreeM.denote mx) Set.univ = 1
  exact (PFunctor.FreeM.isProbabilityMeasure_denote mx).measure_univ

/-- Discarding the result of a lossless oracle computation leaves the continuation's output
measure unchanged. The discarded result type needs no ambient measurable-space instance. -/
@[simp]
theorem evalDist_bind_const
    [OracleSpec.IsMeasureSpec spec] {α β : Type v} [MeasurableSpace β]
    (mx : OracleComp spec α) (my : OracleComp spec β) :
    𝒟[mx >>= fun _ => my] = 𝒟[my] := by
  induction mx using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t next ih =>
    let : MeasurableSpace (spec.Range t) := ⊤
    rw [bind_assoc, evalDist_bind_of_discrete]
    simp_rw [ih]
    rw [Measure.bind_const, evalDist_apply_univ_eq_one, one_smul]

/-- A constant output map on a lossless oracle program is a Dirac measure.
No measurable-space instance on the discarded result type is needed. -/
@[simp]
theorem evalDist_map_const
    [OracleSpec.IsMeasureSpec spec] {α β : Type v} [MeasurableSpace β]
    (mx : OracleComp spec α) (b : β) :
    𝒟[(fun _ : α ↦ b) <$> mx] = Measure.dirac b := by
  rw [map_eq_bind_pure_comp]
  simp only [Function.comp_def, evalDist_bind_const, evalDist_pure]

end OracleComp
