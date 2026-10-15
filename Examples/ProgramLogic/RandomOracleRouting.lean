/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Routing
import VCVio.ProgramLogic.Tactics.PrVCGen

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
  have hcard : (Finset.univ.filter fun table : Bool → Bool => table false = table true).card = 2 :=
    by decide
  rw [← prEvent_eq_evalDist_singleton]
  prvcgen [OracleComp.Upper.Spec.uniformSample_avg, OracleComp.Lower.Spec.uniformSample_sum]
  all_goals
    simp only [propInd_eq_ite, beq_iff_eq, Finset.sum_boole, hcard, Fintype.card_fun,
      Fintype.card_bool, Nat.cast_ofNat, one_div]
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_div, ENNReal.toReal_inv]

/-- Aliasing makes the equality test accept under every sampled target table. -/
theorem aliased_probability :
    𝒟[(fun table : Unit → Bool =>
      evalWithAnswerFn (QueryImpl.ofFn table) (route (fun _ : Bool => ()) equalAnswers))
      <$> ($ᵗ (Unit → Bool))] {true} = 1 := by
  simp only [aliased_answers]
  rw [← prEvent_eq_evalDist_singleton]
  prvcgen

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
