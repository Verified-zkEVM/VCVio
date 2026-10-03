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

An oracle specification assigns a probability measure to each query's answer type. A uniform
specification bundles answer measures that are each the uniform measure on its answer type, and
finiteness and inhabitedness of the answer types follow from that rather than being carried as
data. Both are explicit choices: finiteness alone does not select a probabilistic
interpretation.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

namespace OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- A probability measure on the answers to each query of an oracle specification.

Oracle answers carry the discrete measurable structure, so no measurable-space arguments appear
on answer types, and on a countable answer type a chosen measure is determined by the mass of
single answers. Answer types
with another measurable structure are modeled by `PFunctor.AnswerMeasure` on the underlying
polynomial functor. -/
abbrev AnswerMeasure (spec : OracleSpec.{u, v} ι) :=
  @PFunctor.AnswerMeasure spec.toPFunctor fun _ ↦ ⊤

namespace AnswerMeasure

/-- The probability measure assigned to the answer of query `t`. -/
abbrev toMeasure [AnswerMeasure spec] (t : spec.Domain) : @Measure (spec.Range t) ⊤ :=
  @PFunctor.AnswerMeasure.toMeasure spec.toPFunctor (fun _ ↦ ⊤) _ t

/-- Each answer measure is a probability measure. This restates the polynomial-functor instance at
the oracle API, whose answer types are `spec.Range t` rather than `spec.toPFunctor.B t`, so that
instance search finds it for oracle goals. -/
instance isProbabilityMeasure_toMeasure [AnswerMeasure spec] (t : spec.Domain) :
    @IsProbabilityMeasure (spec.Range t) ⊤ (toMeasure t) :=
  @PFunctor.AnswerMeasure.isProbabilityMeasure spec.toPFunctor (fun _ ↦ ⊤) _ t

end AnswerMeasure

/-- Combining specifications combines their answer measures. -/
@[reducible]
noncomputable instance AnswerMeasure.add {ι' : Type*} (spec' : OracleSpec.{_, v} ι')
    [AnswerMeasure spec] [AnswerMeasure spec'] : AnswerMeasure (spec + spec') :=
  @PFunctor.AnswerMeasure.mk (spec + spec').toPFunctor (fun _ ↦ ⊤)
    (fun
      | .inl t => AnswerMeasure.toMeasure t
      | .inr t => AnswerMeasure.toMeasure t)
    (fun
      | .inl t => AnswerMeasure.isProbabilityMeasure_toMeasure t
      | .inr t => AnswerMeasure.isProbabilityMeasure_toMeasure t)

/-- A chosen measure interpretation that samples uniformly from each answer type.

The class bundles the answer measures (it extends `AnswerMeasure spec`) with the fact that each
one is the uniform measure on its answer type, so it is never assumed beside an
`[AnswerMeasure spec]` binder, which would make the two measures unrelated. It carries no
finiteness or inhabitedness data. `uniformOn Set.univ` is a
probability measure exactly on a finite, nonempty type, which
`AnswerMeasure.isProbabilityMeasure` records, so `UniformAnswerMeasure.finite_range` and
`UniformAnswerMeasure.nonempty_range` recover both facts. Statements about cardinalities take
`[Fintype (spec.Range t)]` for the queries they mention. -/
class UniformAnswerMeasure (spec : OracleSpec.{u, v} ι) extends AnswerMeasure spec where
  /-- Each query uses the uniform probability measure on its answer type. -/
  toMeasure_eq_uniform : ∀ t, toMeasure t = @uniformOn (spec.Range t) ⊤ Set.univ

attribute [simp] UniformAnswerMeasure.toMeasure_eq_uniform

/-- The answer measure exposed by the oracle API is uniform for a uniform specification. -/
theorem AnswerMeasure.toMeasure_eq_uniformOn [UniformAnswerMeasure spec] (t : spec.Domain) :
    toMeasure t = @uniformOn (spec.Range t) ⊤ Set.univ :=
  UniformAnswerMeasure.toMeasure_eq_uniform t

/-- Select uniform measure semantics for an oracle specification whose answer types are finite
and nonempty. -/
@[expose, reducible]
noncomputable def UniformAnswerMeasure.ofFiniteNonempty (spec : OracleSpec.{u, v} ι)
    [∀ t, Finite (spec.Range t)] [∀ t, Nonempty (spec.Range t)] : UniformAnswerMeasure spec where
  toMeasure _ := @uniformOn _ ⊤ Set.univ
  isProbabilityMeasure t :=
    letI : MeasurableSpace (spec.Range t) := ⊤
    inferInstance
  toMeasure_eq_uniform _ := rfl

/-- Uniform measure semantics for the finite-range selection oracle. -/
@[reducible]
noncomputable def UniformAnswerMeasure.unifSpec : UniformAnswerMeasure _root_.unifSpec :=
  ofFiniteNonempty _

/-- Uniform measure semantics for the fair-coin oracle. -/
@[reducible]
noncomputable def UniformAnswerMeasure.coinSpec : UniformAnswerMeasure _root_.coinSpec :=
  ofFiniteNonempty _

attribute [instance] UniformAnswerMeasure.unifSpec UniformAnswerMeasure.coinSpec

namespace UniformAnswerMeasure

variable [UniformAnswerMeasure spec]

/-- A uniform answer measure is a probability measure only on a finite answer type.

Not an instance: for a generic `spec` its conclusion `Finite (spec.Range t)` would be a
candidate for every `Finite _` goal. -/
theorem finite_range (t : spec.Domain) : Finite (spec.Range t) := by
  let : MeasurableSpace (spec.Range t) := ⊤
  have h : AnswerMeasure.toMeasure (spec := spec) t Set.univ ≠ 0 := by
    rw [measure_univ]
    exact one_ne_zero
  rw [AnswerMeasure.toMeasure_eq_uniformOn t] at h
  exact Set.finite_univ_iff.mp (finite_of_uniformOn_ne_zero h)

/-- A uniform answer measure is a probability measure only on a nonempty answer type.

Not an instance, for the reason given at `finite_range`. -/
theorem nonempty_range (t : spec.Domain) : Nonempty (spec.Range t) :=
  letI : MeasurableSpace (spec.Range t) := ⊤
  (AnswerMeasure.toMeasure (spec := spec) t).nonempty_of_neZero

/-- Every answer has positive probability under a uniform answer measure. -/
theorem toMeasure_singleton_pos (t : spec.Domain) (u : spec.Range t) :
    0 < AnswerMeasure.toMeasure (spec := spec) t {u} := by
  let : MeasurableSpace (spec.Range t) := ⊤
  have := finite_range t
  rw [AnswerMeasure.toMeasure_eq_uniformOn t]
  refine pos_iff_ne_zero.mpr fun h => ?_
  rw [uniformOn_eq_zero_iff Set.finite_univ] at h
  simp at h

/-- On a finite answer type, each answer has probability the inverse cardinality. -/
theorem toMeasure_singleton (t : spec.Domain) [Fintype (spec.Range t)] (u : spec.Range t) :
    AnswerMeasure.toMeasure (spec := spec) t {u} = (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace (spec.Range t) := ⊤
  have := nonempty_range t
  rw [AnswerMeasure.toMeasure_eq_uniformOn t, uniformOn_univ_apply_singleton]

/-- A uniform answer measure observed in any measurable structure on the answers is the uniform
measure of that structure. -/
theorem trim_toMeasure (t : spec.Domain) {m : MeasurableSpace (spec.Range t)} :
    (AnswerMeasure.toMeasure (spec := spec) t).trim le_top =
      @uniformOn (spec.Range t) m Set.univ := by
  have := finite_range t
  let : Fintype (spec.Range t) := Fintype.ofFinite _
  ext s hs
  rw [trim_measurableSet_eq _ hs, AnswerMeasure.toMeasure_eq_uniformOn t,
    @uniformOn_univ _ ⊤ _ s, uniformOn_univ, Measure.count_apply hs,
    @Measure.count_apply _ ⊤ _ MeasurableSpace.measurableSet_top]

end UniformAnswerMeasure

/-- Combining uniform specifications preserves each configured answer measure. -/
@[reducible]
noncomputable instance UniformAnswerMeasure.add {ι' : Type*} (spec' : OracleSpec.{_, v} ι')
    [UniformAnswerMeasure spec] [UniformAnswerMeasure spec'] :
    UniformAnswerMeasure (spec + spec') where
  toAnswerMeasure := AnswerMeasure.add spec'
  toMeasure_eq_uniform
    | .inl t => AnswerMeasure.toMeasure_eq_uniformOn (spec := spec) t
    | .inr t => AnswerMeasure.toMeasure_eq_uniformOn (spec := spec') t

end OracleSpec

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- Oracle computations denote the measure fold of their chosen answer measures. -/
noncomputable instance (priority := 30) instEvalDistSemantics [OracleSpec.AnswerMeasure spec] :
    EvalDistSemantics (OracleComp spec) :=
  letI : ∀ a, MeasurableSpace (spec.toPFunctor.B a) := fun _ ↦ ⊤
  PFunctor.FreeM.instEvalDistSemanticsFreeM

/-- Oracle computations denote `pure` as a Dirac measure. -/
noncomputable instance (priority := 30) instLawfulPureEvalDistSemantics
    [OracleSpec.AnswerMeasure spec] : LawfulPureEvalDistSemantics (OracleComp spec) :=
  letI : ∀ a, MeasurableSpace (spec.toPFunctor.B a) := fun _ ↦ ⊤
  PFunctor.FreeM.instLawfulPureEvalDistSemanticsFreeM

/-- Over discrete oracle answers, the measure semantics satisfies the Giry monad laws. -/
noncomputable instance (priority := 30) instLawfulEvalDistSemantics
    [OracleSpec.AnswerMeasure spec] : LawfulEvalDistSemantics (OracleComp spec) :=
  letI : ∀ a, MeasurableSpace (spec.toPFunctor.B a) := fun _ ↦ ⊤
  letI : ∀ a, DiscreteMeasurableSpace (spec.toPFunctor.B a) := fun _ ↦ inferInstanceAs
    (@DiscreteMeasurableSpace _ ⊤)
  PFunctor.FreeM.instLawfulEvalDistSemanticsFreeM

/-- Lifting a primitive query denotes its configured answer measure, trimmed to the measurable
structure observing the answer. -/
theorem evalDist_liftM_query [OracleSpec.AnswerMeasure spec] (t : spec.Domain)
    {_ : MeasurableSpace (spec.Range t)} :
    𝒟[(liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))] =
      @Measure.trim _ _ ⊤ (OracleSpec.AnswerMeasure.toMeasure t) le_top := by
  exact @PFunctor.FreeM.evalDist_lift_of_le spec.toPFunctor (fun _ ↦ ⊤) _ t _ le_top

/-- A single oracle query denotes its configured answer measure, trimmed to the measurable
structure observing the answer. -/
theorem evalDist_query [OracleSpec.AnswerMeasure spec] (t : spec.Domain)
    {_ : MeasurableSpace (spec.Range t)} :
    𝒟[(query t : OracleComp spec (spec.Range t))] =
      @Measure.trim _ _ ⊤ (OracleSpec.AnswerMeasure.toMeasure t) le_top := by
  rw [HasQuery.instOfMonadLift_query]
  exact evalDist_liftM_query t

/-- A measurable event of a lifted query has its configured answer probability. -/
@[simp]
theorem evalDist_liftM_query_apply [OracleSpec.AnswerMeasure spec] (t : spec.Domain)
    {_ : MeasurableSpace (spec.Range t)} {s : Set (spec.Range t)} (hs : MeasurableSet s) :
    𝒟[(liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))] s =
      OracleSpec.AnswerMeasure.toMeasure t s := by
  rw [evalDist_liftM_query, trim_measurableSet_eq _ hs]

/-- A lifted query in a uniform measure specification has the uniform answer measure in every
measurable structure on its answers. -/
theorem evalDist_liftM_query_uniform [OracleSpec.UniformAnswerMeasure spec] (t : spec.Domain)
    {_ : MeasurableSpace (spec.Range t)} :
    𝒟[(liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))] = uniformOn Set.univ := by
  rw [evalDist_liftM_query]
  exact OracleSpec.UniformAnswerMeasure.trim_toMeasure t

/-- A query in a uniform measure specification has the uniform answer measure in every measurable
structure on its answers. -/
theorem evalDist_query_uniform [OracleSpec.UniformAnswerMeasure spec] (t : spec.Domain)
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
    [OracleSpec.AnswerMeasure spec] {α : Type v} [MeasurableSpace α]
    (mx : OracleComp spec α) : 𝒟[mx] Set.univ = 1 := by
  let : ∀ a, MeasurableSpace (spec.toPFunctor.B a) := fun _ ↦ ⊤
  change (PFunctor.FreeM.denote mx) Set.univ = 1
  exact (PFunctor.FreeM.isProbabilityMeasure_denote mx).measure_univ

/-- Discarding the result of a lossless oracle computation leaves the continuation's output
measure unchanged. The discarded result type needs no ambient measurable-space instance. -/
@[simp]
theorem evalDist_bind_const
    [OracleSpec.AnswerMeasure spec] {α β : Type v} [MeasurableSpace β]
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
    [OracleSpec.AnswerMeasure spec] {α β : Type v} [MeasurableSpace β]
    (mx : OracleComp spec α) (b : β) :
    𝒟[(fun _ : α ↦ b) <$> mx] = Measure.dirac b := by
  rw [map_eq_bind_pure_comp]
  simp only [Function.comp_def, evalDist_bind_const, evalDist_pure]

end OracleComp
