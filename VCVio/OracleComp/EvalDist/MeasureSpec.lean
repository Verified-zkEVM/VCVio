/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.PFunctorMeasure.Core
public import VCVio.OracleComp.OracleComp

/-!
# Measure-valued oracle specifications

An oracle specification assigns a probability measure to each query's response type.
Uniform specifications additionally carry finite, inhabited response types and identify
the chosen response measures with the uniform measures. These certificates are explicit:
finiteness alone does not select a probabilistic interpretation.
-/

public section

open MeasureTheory ProbabilityTheory

universe u v

namespace OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- A measure-valued response distribution for each query in an oracle specification. -/
abbrev IsMeasureSpec (spec : OracleSpec.{u, v} ι)
    [∀ t, MeasurableSpace (spec.Range t)] :=
  PFunctor.IsMeasureSpec spec.toPFunctor

namespace IsMeasureSpec

/-- The probability measure assigned to the response of query `t`. -/
abbrev toMeasure [∀ t, MeasurableSpace (spec.Range t)] [IsMeasureSpec spec]
    (t : spec.Domain) : Measure (spec.Range t) :=
  PFunctor.IsMeasureSpec.toMeasure (P := spec.toPFunctor) t

end IsMeasureSpec

/-- A chosen measure interpretation that samples uniformly from each finite response type. -/
class IsUniformMeasureSpec (spec : OracleSpec.{u, v} ι)
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] extends IsMeasureSpec spec where
  /-- Every response type is finite. -/
  fintype : spec.Fintype
  /-- Every response type is inhabited. -/
  inhabited : spec.Inhabited
  /-- Each query uses the uniform probability measure on its response type. -/
  toMeasure_eq_uniform : ∀ t, toMeasure t = uniformOn Set.univ

attribute [reducible, instance 100] IsUniformMeasureSpec.fintype IsUniformMeasureSpec.inhabited
attribute [simp] IsUniformMeasureSpec.toMeasure_eq_uniform

/-- Select uniform measure semantics for a finite, inhabited oracle specification. -/
@[reducible]
noncomputable def IsUniformMeasureSpec.ofFintypeInhabited
    (spec : OracleSpec.{u, v} ι)
    [hF : spec.Fintype] [hI : spec.Inhabited]
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] : IsUniformMeasureSpec spec where
  toMeasure _ := uniformOn Set.univ
  isProbabilityMeasure _ := inferInstance
  fintype := hF
  inhabited := hI
  toMeasure_eq_uniform _ := rfl

/-- Native uniform measure semantics for the finite-range selection oracle. -/
@[reducible]
noncomputable def IsUniformMeasureSpec.unifSpec : IsUniformMeasureSpec _root_.unifSpec :=
  ofFintypeInhabited _

/-- Native uniform measure semantics for the fair-coin oracle. -/
@[reducible]
noncomputable def IsUniformMeasureSpec.coinSpec : IsUniformMeasureSpec _root_.coinSpec :=
  ofFintypeInhabited _

attribute [instance] IsUniformMeasureSpec.unifSpec IsUniformMeasureSpec.coinSpec

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
@[simp]
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
  let : MeasurableSpace α := ⊤
  rw [_root_.evalDist_bind_const, evalDist_apply_univ_eq_one, one_smul]

end OracleComp
