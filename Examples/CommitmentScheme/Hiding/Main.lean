/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/

module
public import Examples.CommitmentScheme.Hiding.LoggingBounds
public import VCVio.OracleComp.Coercions.SubSpec.Measure
public import VCVio.EvalDist.MeasureTVDist.Bind

/-!
# Hiding for the random-oracle commitment scheme — main theorems

The two packaged hiding bounds, both stating that real and simulated
hiding games are `t / |S|`-close in total variation after the salt is averaged
over `s ← $ᵗ S`.

* `hiding_bound_avg` — per-salt sum, divided by `|S|`. Distance bound:
  `t / |S|`.
* `hiding_bound_finite` — salt sampled inside the experiment via
  `HidingAvgSpec`. Distance bound: `t / |S|`.

`hiding_bound_finite` is the textbook-facing form: sample the salt inside
the experiment, then compare. `hiding_bound_avg` is the underlying
technical form, summing the per-salt distance bounds and dividing by `|S|`.
The packaging step uses `measureETVDist_bind_bind_le_lintegral` to push the
salt sampling through the distance.

The per-salt bound `measureETVDist (real s) (sim s) ≤ t / |S|` is FALSE: a
trivial adversary always querying salt `s` makes the bad event certain. The
averaging over the uniform salt is essential. -/

@[expose] public section

open OracleSpec OracleComp ENNReal MeasureTheory

variable {M S C : Type} [Fintype S] [Finite C] [Inhabited S] [Inhabited C]

attribute [local instance] Fintype.ofFinite

variable [DecidableEq M] [DecidableEq S] [Inhabited M]

/-- **Hiding bound (averaged technical form, Lemma cm-hiding).**

For every `t`-query two-phase hiding adversary `A`, the average total variation
distance between real and simulated hiding games, taken over uniformly random
salt `s ← $ᵗ S`, is at most `t / |S|`:

```
(∑ s, measureETVDist (hidingReal A s) (hidingSim A s)) / |S|  ≤  t / |S|.
```

Proof: per-salt identical-until-bad
(`measureETVDist_hidingReal_hidingSim_le_probBad`) bounds each distance by the
probability of the bad event for that salt. Summing over `s` and applying
`sum_prEvent_hidingBad_le` (which exchanges the per-salt bad sum for the
adversary's total query bound) yields the claim.

The averaging is essential. The per-salt bound `≤ t / |S|` is FALSE in
general: a trivial adversary always querying salt `s` makes the bad event for
`s` certain. The textbook lemma silently averages over the uniform salt, which
`hiding_bound_finite` makes explicit by sampling the salt inside a packaged
`HidingAvgSpec` experiment. -/
theorem hiding_bound_avg [Finite M]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, measureETVDist (hidingReal A s) (hidingSim A s)) / (Fintype.card S : ℝ≥0∞) ≤
      t / (Fintype.card S : ℝ≥0∞) :=
  ENNReal.div_le_div_right ((Finset.sum_le_sum fun s _ =>
    measureETVDist_hidingReal_hidingSim_le_probBad A s).trans (sum_prEvent_hidingBad_le A)) _

/-- **Hiding bound (Lemma cm-hiding, packaged textbook form).**

For every `t`-query two-phase hiding adversary `A`,

```
measureETVDist (hidingMixedReal A) (hidingMixedSim A)  ≤  t / |S|,
```

where `hidingMixedReal` and `hidingMixedSim` sample the salt
`s ← $ᵗ S` *inside* the experiment (via the `HidingAvgSpec` random-salt
oracle) and then run the corresponding per-salt game.

This is the textbook-facing wrapper around `hiding_bound_avg`: it pushes the
salt sampling through `measureETVDist_bind_bind_le_lintegral`, leaving the
per-salt sum that `hiding_bound_avg` already controls. -/
theorem hiding_bound_finite [Finite M]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    measureETVDist (hidingMixedReal (M := M) (S := S) (C := C) A)
      (hidingMixedSim (M := M) (S := S) (C := C) A) ≤
      t / (Fintype.card S : ℝ≥0∞) := by
  let : MeasurableSpace S := ⊤
  refine (measureETVDist_bind_bind_le_lintegral _ _ _ Measurable.of_discrete
    Measurable.of_discrete (fun s => measureETVDist (hidingReal A s) (hidingSim A s))
    (ae_of_all _ fun s => ?_)).trans ?_
  · simp only [measureETVDist, evalDist_liftComp_uniform, le_refl]
  · rw [lintegral_fintype]
    simp only [evalDist_liftM_query_uniform (spec := HidingAvgSpec M S C) (Sum.inl ()),
      ProbabilityTheory.uniformOn_univ_apply_singleton]
    refine le_of_eq_of_le ?_ (hiding_bound_avg A)
    rw [ENNReal.div_eq_inv_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
