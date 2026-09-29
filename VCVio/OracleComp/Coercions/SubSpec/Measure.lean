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
  [h : spec ⊂ₒ superSpec]

/-- Translated queries equal in distribution to the original ones preserve every output measure. -/
theorem evalDist_liftComp_of_evalDistEq [OracleSpec.IsMeasureSpec spec]
    [OracleSpec.IsMeasureSpec superSpec]
    (hMeasure : ∀ t, (liftM (spec.query t) : OracleComp superSpec (spec.Range t)) =ᵈ
      (liftM (spec.query t) : OracleComp spec (spec.Range t)))
    {α : Type} [MeasurableSpace α] (mx : OracleComp spec α) :
    𝒟[liftComp mx superSpec] = 𝒟[mx] := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    let : MeasurableSpace (spec.Range t) := ⊤
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, evalDist_bind_of_discrete]
    simp_rw [ih]
    rw [(hMeasure t).evalDist_eq]

/-- Cartesian answer translations preserve uniform answer measures: a translated query is
distributed as the original one. -/
theorem evalDistEq_liftM_query_uniform [spec ˡ⊂ₒ superSpec]
    [OracleSpec.IsUniformMeasureSpec spec] [OracleSpec.IsUniformMeasureSpec superSpec]
    (t : spec.Domain) :
    (liftM (spec.query t) : OracleComp superSpec (spec.Range t)) =ᵈ
      (liftM (spec.query t) : OracleComp spec (spec.Range t)) := by
  let : MeasurableSpace (spec.Range t) := ⊤
  let : MeasurableSpace (superSpec.Range (h.onQuery t)) := ⊤
  have := OracleSpec.IsUniformMeasureSpec.finite_range t
  have := OracleSpec.IsUniformMeasureSpec.finite_range (h.onQuery t)
  have hsup : 𝒟[(liftM (spec.query t) : OracleComp superSpec (spec.Range t))] =
      𝒟[(liftM (spec.query t) : OracleComp spec (spec.Range t))] := by
    rw [liftM_eq_liftM_liftM]
    rw [show (liftM (spec.query t) : OracleQuery superSpec (spec.Range t)) =
        ⟨h.onQuery t, h.onResponse t⟩ from h.liftM_eq_lift _, liftM_eq_map_query]
    change 𝒟[h.onResponse t <$>
      (liftM (OracleSpec.query (h.onQuery t)) : OracleComp superSpec _)] = _
    rw [evalDist_map _ Measurable.of_discrete,
      evalDist_liftM_query_uniform (spec := superSpec) (h.onQuery t),
      evalDist_liftM_query_uniform (spec := spec) t]
    exact uniformOn_univ_map_equiv (Equiv.ofBijective _ (LawfulSubSpec.onResponse_bijective t))
  exact EvalDistEq.of_evalDist_eq hsup

/-- Cartesian inclusions between uniform specifications preserve denotations. -/
theorem evalDist_liftComp_uniform [spec ˡ⊂ₒ superSpec]
    [OracleSpec.IsUniformMeasureSpec spec] [OracleSpec.IsUniformMeasureSpec superSpec]
    {α : Type} [MeasurableSpace α] (mx : OracleComp spec α) :
    𝒟[liftComp mx superSpec] = 𝒟[mx] :=
  evalDist_liftComp_of_evalDistEq (fun t ↦ evalDistEq_liftM_query_uniform t) mx

/-- Cartesian inclusions between uniform specifications preserve the distribution of every
computation. -/
theorem evalDistEq_liftComp_uniform [spec ˡ⊂ₒ superSpec]
    [OracleSpec.IsUniformMeasureSpec spec] [OracleSpec.IsUniformMeasureSpec superSpec]
    {α : Type} (mx : OracleComp spec α) : liftComp mx superSpec =ᵈ mx :=
  letI : MeasurableSpace α := ⊤
  EvalDistEq.of_evalDist_eq (evalDist_liftComp_uniform mx)

end OracleComp
