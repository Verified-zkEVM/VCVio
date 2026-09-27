/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Routing

/-!
# Input aliasing changes a random-oracle observation

An equality test on distinct Boolean inputs accepts with probability one half. Routing both
inputs to one target cell makes it accept with probability one, for eager and lazy oracles.
A well-typed polynomial lens alone therefore does not certify independent oracle domains.
-/

public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory
open OracleComp.RandomOracleRouting

namespace Examples.RandomOracleRouting

/-- Compare the responses at two distinct source-domain inputs. -/
@[expose]
def equalAnswers : OracleComp (Bool →ₒ Bool) Bool := do
  let left ← (query (spec := Bool →ₒ Bool) false : OracleComp (Bool →ₒ Bool) Bool)
  let right ← (query (spec := Bool →ₒ Bool) true : OracleComp (Bool →ₒ Bool) Bool)
  pure (left == right)

/-- Aliased inputs always read the same target cell. -/
theorem aliased_answers (table : Unit → Bool) :
    evalWithAnswerFn (QueryImpl.ofFn table) (route (fun _ : Bool => ()) equalAnswers) = true := by
  change (table () == table ()) = true
  simp

/-- The unrouted program compares the two source cells. -/
theorem separated_answers (table : Bool → Bool) :
    evalWithAnswerFn (QueryImpl.ofFn table) equalAnswers = (table false == table true) := rfl

/-- A deterministic witness distinguishes aliasing from separate source cells. -/
theorem aliasing_changes_observation :
    evalWithAnswerFn (QueryImpl.ofFn (fun _ : Unit => false))
      (route (fun _ : Bool => ()) equalAnswers) ≠
      evalWithAnswerFn (QueryImpl.ofFn id) equalAnswers := by decide

/-- Two distinct cells of a uniform Boolean table agree with probability one half. -/
theorem separated_probability :
    𝒟[(fun table : Bool → Bool => (table false == table true)) <$> ($ᵗ (Bool → Bool))]
      {true} = (1 : ENNReal) / 2 := by
  rw [evalDist_map_apply_of_discrete _ _ (MeasurableSet.singleton true),
    SampleableType.evalDist_uniformSample]
  have hevent : (fun table : Bool → Bool => (table false == table true)) ⁻¹' {true} =
      {fun _ => false} ∪ {fun _ => true} := by
    ext table
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff, beq_iff_eq]
    constructor
    · intro h
      cases hf : table false with
      | false =>
          left
          funext b
          cases b
          · exact hf
          · exact h.symm.trans hf
      | true =>
          right
          funext b
          cases b
          · exact hf
          · exact h.symm.trans hf
    · rintro (rfl | rfl) <;> rfl
  rw [hevent, measure_union]
  · simp only [uniformOn_univ_apply_singleton, Fintype.card_fun, Fintype.card_bool]
    have h : (4 : NNReal)⁻¹ + (4 : NNReal)⁻¹ = (2 : NNReal)⁻¹ := by norm_num
    norm_num only [Nat.reducePow, Nat.cast_ofNat, one_div]
    have h' := congrArg (fun x : NNReal => (x : ENNReal)) h
    simpa only [ENNReal.coe_add, ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
      ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0), ENNReal.coe_ofNat] using h'
  · simp only [Set.disjoint_singleton]
    intro h
    have := congrFun h false
    contradiction
  · exact MeasurableSet.singleton _

/-- Aliasing makes the equality test accept under every sampled target table. -/
theorem aliased_probability :
    𝒟[(fun table : Unit → Bool =>
      evalWithAnswerFn (QueryImpl.ofFn table) (route (fun _ : Bool => ()) equalAnswers))
      <$> ($ᵗ (Unit → Bool))] {true} = 1 := by
  simp only [aliased_answers]
  rw [evalDist_map_of_discrete, SampleableType.evalDist_uniformSample]
  simp

/-- The initially empty lazy oracle gives the same one-half acceptance probability. -/
theorem separated_lazy_probability :
    𝒟[(simulateQ randomOracle equalAnswers).run' ∅] {true} = (1 : ENNReal) / 2 := by
  erw [evalDist_simulateQ_randomOracle_run'_eq_tableExtending]
  simp only [tableExtending_empty, bind_pure_comp, separated_answers]
  exact separated_probability

/-- The lazy cache preserves the aliased cell across both source queries. -/
theorem aliased_lazy_probability :
    𝒟[(simulateQ randomOracle (route (fun _ : Bool => ()) equalAnswers)).run' ∅] {true} = 1 := by
  erw [evalDist_simulateQ_randomOracle_run'_eq_tableExtending]
  simp only [tableExtending_empty, bind_pure_comp]
  exact aliased_probability

end Examples.RandomOracleRouting
