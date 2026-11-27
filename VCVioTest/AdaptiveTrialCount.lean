/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.CountingOracle.FreshTrials
public import VCVio.OracleComp.QueryTracking.CountingOracle.TrialCharge
import VCVio.OracleComp.Constructions.SampleableType.Measure
import Mathlib.Tactic.NormNum

/-!
# Counting fresh trials up to an adaptive stop

The caller queries a second fresh bit only after the first bit is false.
The probability of using two trials is 1/2, and the expected number of trials is 3/2.
-/

public section

open OracleSpec OracleComp randomOracle.FreshTrials
open scoped ENNReal

namespace VCVioTest.AdaptiveTrialCount

/-- The caller asks a second question only after a rejection at the first fresh bit. -/
@[expose] def untilTrue : OracleComp (Nat →ₒ Bool) Bool := do
  let first ← liftM ((Nat →ₒ Bool).query 0)
  if first then return true else liftM ((Nat →ₒ Bool).query 1)

/-- A second trial is charged on exactly half the paths. -/
theorem second_trial :
    Pr{let z ← (simulateQ (observe 2 {true} (fun _ _ => true)) untilTrue).run (∅, 0, 0)}[
      z.2.2.1 = 2] = (1 : ℝ≥0∞) / 2 := by
  simp only [untilTrue, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    observe, BernoulliMoment.observe, QueryImpl.extendState_apply, randomOracle.run_eq,
    QueryCache.empty_apply, bind_assoc, pure_bind, BernoulliMoment.update]
  rw [prEvent_bind_eq_sum_fintype]
  simp only [Fintype.sum_bool, SampleableType.prEvent_uniformSample_eq_singleton_natCard,
    Nat.card_eq_fintype_card, Fintype.card_bool]
  norm_num [OracleQuery.input_query, simulateQ_pure, StateT.run_pure, prEvent_bind_eq_sum_fintype,
    Fintype.sum_bool, QueryImpl.extendState_apply, randomOracle.run_eq, BernoulliMoment.update,
    -SampleableType.prEvent_uniformSample,
    SampleableType.prEvent_uniformSample_eq_singleton_natCard, Nat.card_eq_fintype_card]
  simp

private theorem halfRate :
    Pr{let y ← $ᵗ Bool}[y ∈ ({true} : Finset Bool)] = ENNReal.ofReal (1 / 2) := by
  rw [prEvent_congr ($ᵗ Bool) _ (fun y => y = true) (fun y => Finset.mem_singleton)]
  rw [SampleableType.prEvent_uniformSample_eq_singleton_natCard]
  norm_num [Nat.card_eq_fintype_card, ENNReal.ofReal_div_of_pos]

/-- The adaptive call makes one fresh trial and makes a second only after a rejection. -/
theorem expected_trial_charge :
    PFunctor.FreeM.wpFold (BernoulliMoment.trialCharge (observe 2 {true} (fun _ _ => true))
      (fun s => s.2.1)) untilTrue.toFreeM (fun _ _ => 0) (∅, 0, 0) = (3 : ℝ≥0∞) / 2 := by
  classical
  have law := countsTrials 2 ({true} : Finset Bool) (fun (_ : Nat) _ => true) (1 / 2) halfRate
  have bridge := law.expected_trials_eq_charge untilTrue (∅, 0, 0)
  simp only [Nat.cast_zero, zero_add] at bridge
  -- Compute the observed count under the random oracle, retaining both replies on a rejection.
  rw [← bridge]
  simp only [untilTrue, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, observe,
    BernoulliMoment.observe, QueryImpl.extendState_apply, randomOracle.run_eq,
    QueryCache.empty_apply, bind_assoc, pure_bind, BernoulliMoment.update, tsum_prEvent_bind_mul]
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton_natCard, Nat.card_eq_fintype_card,
    Fintype.card_bool]
  norm_num [OracleQuery.input_query, prEvent_pure_prop, ite_mul, simulateQ_pure, StateT.run_pure,
    simulateQ_spec_query, QueryImpl.extendState_apply,
    randomOracle.run_eq, BernoulliMoment.update, tsum_prEvent_pure_mul, tsum_prEvent_bind_mul,
    tsum_fintype, Fintype.sum_bool, -SampleableType.prEvent_uniformSample,
    SampleableType.prEvent_uniformSample_eq_singleton_natCard, Nat.card_eq_fintype_card]
  simp only [OracleQuery.input_query, ne_eq, one_ne_zero, not_false_eq_true,
    QueryCache.cacheQuery_of_ne, QueryCache.empty_apply, ↓reduceIte, StateT.run_bind,
    StateT.run_monadLift, monadLift_self, bind_pure_comp, StateT.run_modifyGet, Functor.map_map]
  -- After a false first bit both possible second replies leave the trial count at two.
  let result (a : Bool) : Bool × State Nat Bool :=
    (a, ((∅ : (Nat →ₒ Bool).QueryCache).cacheQuery 0 false).cacheQuery 1 a, 2,
      if a then 1 else 0)
  change 2⁻¹ + 2⁻¹ *
    (∑' z, Pr{let a ← $ᵗ Bool}[result a = z] * (z.2.2.1 : ℝ≥0∞)) = _
  have hmap (z : Bool × State Nat Bool) :
      Pr{let a ← $ᵗ Bool}[result a = z] = Pr{let a ← result <$> ($ᵗ Bool)}[a = z] :=
    (prEvent_map ($ᵗ Bool) result (fun a => a = z)).symm
  simp_rw [hmap]
  rw [tsum_prEvent_map_mul]
  rw [tsum_prEvent_mul_of_const_on_support _ (c := 2) (fun a _ => by simp [result])]
  rw [mul_comm (2 : ℝ≥0∞)⁻¹ 2, ← one_add_mul, div_eq_mul_inv]
  norm_num

end VCVioTest.AdaptiveTrialCount
