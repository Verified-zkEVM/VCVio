/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Unary.HoareTriple
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.Coercions.SubSpec.Measure
public import ToMathlib.MeasureTheory.Measure.UniformTable

/-!
# Oracle-Aware Unary WP Rules

This file connects the quantitative weakest precondition (`wp`) to `simulateQ`,
providing rules that let program logic proofs pass through oracle simulation boundaries.

## Main results

- `wp_simulateQ_eq`: If an oracle implementation preserves distributions, then `wp` is preserved.
- `wp_liftComp`: Lifting a computation to a larger oracle spec preserves `wp`.
- `wp_simulateQ_run'_eq`: Stateful oracle implementations that preserve distributions
  preserve `wp`.
-/

@[expose] public section

open ENNReal OracleSpec OracleComp MeasureTheory

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.ProgramLogic

variable {ι : Type*} {spec : OracleSpec ι}
variable {α : Type}

section MeasureSpec

variable [OracleSpec.AnswerMeasure spec]

/-- If every oracle query in `impl` has the same evaluation distribution as the original query,
then `wp` of the simulated computation equals `wp` of the original. -/
@[expect_eval] theorem wp_simulateQ_eq
    (impl : QueryImpl spec (OracleComp spec))
    (hImpl : ∀ (t : spec.Domain),
      impl t =ᵈ (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t)))
    (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦simulateQ impl oa⟧ post =
      wp⟦oa⟧ post := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih =>
    let : MeasurableSpace (spec.Range t) := ⊤
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query]
    rw [ExpectationWP.wp_bind, ExpectationWP.wp_bind]
    simp_rw [ih]
    exact wp_congr_evalDist (hImpl t).evalDist_eq _ Measurable.of_discrete

/-- A distribution-preserving signature inclusion preserves quantitative WP. -/
theorem wp_liftComp_of_evalDistEq {ι' : Type*} {superSpec : OracleSpec ι'}
    [OracleSpec.AnswerMeasure superSpec]
    [h : spec ⊂ₒ superSpec]
    (hMeasure : ∀ t, (liftM (spec.query t) : OracleComp superSpec (spec.Range t)) =ᵈ
      (liftM (spec.query t) : OracleComp spec (spec.Range t)))
    (mx : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦liftComp mx superSpec⟧ post = wp⟦mx⟧ post := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    let : MeasurableSpace (spec.Range t) := ⊤
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, ExpectationWP.wp_bind]
    simp_rw [ih]
    rw [wp_eq_lintegral _ _ Measurable.of_discrete, (hMeasure t).evalDist_eq,
      ← wp_eq_lintegral _ _ Measurable.of_discrete]

end MeasureSpec

/-- Cartesian lifting between uniform specifications preserves quantitative WP. -/
@[expect_eval] theorem wp_liftComp [OracleSpec.UniformAnswerMeasure spec]
    {ι' : Type*} {superSpec : OracleSpec ι'}
    [OracleSpec.UniformAnswerMeasure superSpec] [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]
    (mx : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦liftComp mx superSpec⟧ post = wp⟦mx⟧ post :=
  wp_liftComp_of_evalDistEq (fun t ↦ evalDistEq_liftM_query_uniform t) mx post

section MeasureSpec

variable [OracleSpec.AnswerMeasure spec]

/-- A stateful implementation preserving each configured answer measure preserves WP
after its state is discarded. The hidden state needs no measurable-space instance. -/
@[expect_eval] theorem wp_simulateQ_run'_eq {σ : Type}
    (impl : QueryImpl spec (StateT σ (OracleComp spec)))
    (hImpl : ∀ (t : spec.Domain) (s : σ),
      (impl t).run' s =ᵈ (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t)))
    (oa : OracleComp spec α) (s : σ) (post : α → ℝ≥0∞) :
    wp⟦(simulateQ impl oa).run' s⟧ post =
      wp⟦oa⟧ post := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    let : MeasurableSpace (spec.Range t) := ⊤
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run'_bind', ExpectationWP.wp_bind]
    simp_rw [ih]
    calc
      _ = wp⟦(impl t).run' s⟧ (fun u ↦ wp⟦k u⟧ post) := by
        simpa only [StateT.run'_eq, Function.comp_def] using
          (ExpectationWP.wp_map Prod.fst ((impl t).run s) (fun u ↦ wp⟦k u⟧ post)).symm
      _ = _ := by
        rw [wp_eq_lintegral _ _ Measurable.of_discrete, (hImpl t s).evalDist_eq,
          ← wp_eq_lintegral _ _ Measurable.of_discrete]


end MeasureSpec

end OracleComp.ProgramLogic
