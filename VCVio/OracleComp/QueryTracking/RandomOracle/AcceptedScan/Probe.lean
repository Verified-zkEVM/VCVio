/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Commute
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Conditional event probabilities after a cache probe

The caller can query a cold address and then discard the answer.
Averaging its event probability over the updated cache gives the probability before the query.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace randomOracle

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- Revealing one fresh reply preserves the mean probability of an event on the caller's result. -/
theorem prEvent_eq_average_cacheQuery {α : Type} (oa : OracleComp spec α)
    (cache : spec.QueryCache) (t : spec.Domain) (cold : cache t = none) (event : α → Prop) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run cache}[event z.1] =
      ∑' y, Pr{let w ← $ᵗ (spec.Range t)}[w = y] *
        Pr{let z ← (simulateQ spec.randomOracle oa).run (cache.cacheQuery t y)}[event z.1] := by
  let f (_ : spec.Range t) (x : α) (_ : spec.QueryCache) : ProbComp Prop := pure (event x)
  have swap := evalDist_run_bind_simulateQ_run_swap t oa cache f
  have eqn := congrArg (fun μ : Measure Prop => μ {True}) swap
  rw [QueryImpl.withCaching_run_none _ cold] at eqn
  simp only [uniformSampleImpl, bind_map_left] at eqn
  change prEvent _ = prEvent _ at eqn
  simp only [f, bind_pure_comp] at eqn
  rw [← prEvent_bind_eq_tsum]
  change prEvent _ = prEvent _
  simp only [prEvent_norm]
  rw [eqn]
  conv_lhs => rw [← bind_pure_comp]
  apply prEvent_bind_congr_of_support
  intro z _
  rw [← bind_pure_comp]
  exact (OracleComp.prEvent_bind_const _ _).symm

/-- A probe that enlarges an event adds exactly the mean mass of its new outcomes. -/
theorem average_growing_event {α : Type} (oa : OracleComp spec α)
    (cache : spec.QueryCache) (t : spec.Domain) (cold : cache t = none)
    (before : α → Prop) (after : spec.Range t → α → Prop)
    (grows : ∀ w z, before z → after w z) :
    (∑' w, Pr{let x ← $ᵗ (spec.Range t)}[x = w] *
      Pr{let z ← (simulateQ spec.randomOracle oa).run (cache.cacheQuery t w)}[after w z.1]) =
      Pr{let z ← (simulateQ spec.randomOracle oa).run cache}[before z.1] +
        ∑' w, Pr{let x ← $ᵗ (spec.Range t)}[x = w] *
          Pr{let z ← (simulateQ spec.randomOracle oa).run (cache.cacheQuery t w)}[
            after w z.1 ∧ ¬before z.1] := by
  rw [prEvent_eq_average_cacheQuery oa cache t cold before, ← tsum_add]
  congr 1
  funext w
  rw [← mul_add]
  congr 1
  have both : (fun z : α × spec.QueryCache => after w z.1 ∧ before z.1) =
      (fun z => before z.1) := by
    ext z
    exact ⟨And.right, fun h => ⟨grows w _ h, h⟩⟩
  exact (prEvent_eq_prEvent_and_add_prEvent_and_not
    ((simulateQ spec.randomOracle oa).run (cache.cacheQuery t w))
    (fun z => after w z.1) (fun z => before z.1)).trans (by rw [both])

end randomOracle
