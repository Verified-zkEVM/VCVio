/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coercions.SubSpec.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import ToMathlib.MeasureTheory.Measure.UniformTable

/-!
# Measure preservation by oracle-signature inclusions

The local contract equates the translated answer measure with the configured source measure.
It preserves every adaptive computation's chosen output measure. Cartesian inclusions between
uniform measure specifications satisfy that contract by transporting finite uniform measures.
-/

public section

open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped OracleSpec.PrimitiveQuery

universe u v

namespace OracleComp

variable {ι : Type u} {τ : Type v} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  [∀ t, MeasurableSpace (superSpec.Range t)]
  [∀ t, DiscreteMeasurableSpace (superSpec.Range t)] [h : spec ⊂ₒ superSpec]

/-- Equality of translated answer measures preserves every chosen output measure. -/
theorem evalDist_liftComp_of_evalDist [OracleSpec.IsMeasureSpec spec]
    [OracleSpec.IsMeasureSpec superSpec]
    (hMeasure : ∀ t, 𝒟[(liftM (spec.query t) : OracleComp superSpec (spec.Range t))] =
      OracleSpec.IsMeasureSpec.toMeasure t)
    {α : Type} [MeasurableSpace α] (mx : OracleComp spec α) :
    𝒟[liftComp mx superSpec] = 𝒟[mx] := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, evalDist_bind_of_discrete]
    simp_rw [ih]
    rw [hMeasure, evalDist_liftM_query]

/-- Cartesian response translations preserve uniform native answer measures. -/
theorem evalDist_liftM_query_uniform [spec ˡ⊂ₒ superSpec]
    [OracleSpec.IsUniformMeasureSpec spec] [OracleSpec.IsUniformMeasureSpec superSpec]
    (t : spec.Domain) :
    𝒟[(liftM (spec.query t) : OracleComp superSpec (spec.Range t))] =
      OracleSpec.IsMeasureSpec.toMeasure t := by
  rw [liftM_eq_liftM_liftM]
  rw [show (liftM (spec.query t) : OracleQuery superSpec (spec.Range t)) =
      ⟨h.onQuery t, h.onResponse t⟩ from h.liftM_eq_lift _,
    liftM_eq_map_query, evalDist_map _ Measurable.of_discrete, evalDist_liftM_query,
    OracleSpec.IsMeasureSpec.toMeasure_eq_uniformOn,
    OracleSpec.IsMeasureSpec.toMeasure_eq_uniformOn]
  exact uniformOn_univ_map_equiv (Equiv.ofBijective _ (LawfulSubSpec.onResponse_bijective t))

/-- Cartesian inclusions between uniform specifications preserve native denotations. -/
theorem evalDist_liftComp_uniform [spec ˡ⊂ₒ superSpec]
    [OracleSpec.IsUniformMeasureSpec spec] [OracleSpec.IsUniformMeasureSpec superSpec]
    {α : Type} [MeasurableSpace α] (mx : OracleComp spec α) :
    𝒟[liftComp mx superSpec] = 𝒟[mx] :=
  evalDist_liftComp_of_evalDist (fun t ↦ evalDist_liftM_query_uniform t) mx

end OracleComp
