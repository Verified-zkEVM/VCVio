/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.CountingOracle.FreshTrials
import VCVio.OracleComp.Constructions.SampleableType.Measure
import Mathlib.Tactic.NormNum

/-!
# Counting fresh trials up to an adaptive stop
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

end VCVioTest.AdaptiveTrialCount
