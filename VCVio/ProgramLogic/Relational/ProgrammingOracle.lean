/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.ProgrammingOracle
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad

/-!
# Total variation between `withProgramming` and `withCaching`

The headline theorem `measureETVDist_simulateQ_withCaching_withProgramming_le_prEvent_bad` bounds
the total variation distance between the output measure of `withCaching` and the output measure
of `withProgramming policy` by the probability that the bad flag of `withProgramming policy` ever
fires (i.e., the adversary queries a point on which `policy` is defined).

The proof factors through the auxiliary `withCachingTrackingPolicy` (defined alongside
`withProgramming` in `OracleComp/QueryTracking/ProgrammingOracle.lean`):

* On every step from a good input `(cache, false)`, the two implementations give every event the
  same probability on good outputs. On policy-firing steps, both produce only bad outputs (with
  possibly different `(value, cache)` components). This is the agreement consumed by
  `measureETVDist_simulateQ_run_le_prEvent_bad`.
* `withCachingTrackingPolicy_run'_eq'` projects `withCachingTrackingPolicy` to `withCaching`
  on the output marginal, eliminating the auxiliary implementation from the user-facing
  statement.

The bound applies to any base implementation `so : QueryImpl spec (OracleComp spec')`, with the
policy acting on inputs of `spec`; taking `so := uniformSampleImpl` gives the lazy random oracle.

## Programming collision bound

Built directly on top of the headline bound, `programming_collision_bound` is the
"collision-event" repackaging used by Fiat-Shamir-style identical-until-bad reductions: given any
upper bound `B` on `withProgrammingBadProb so policy oa`, the total variation between the
unprogrammed and programmed runs is at most `B`. The convenience wrapper
`programming_collision_bound_qP_qH_β` specializes `B` to the textbook `qP * qH * β` shape so
callers only need to discharge a union-bound hypothesis.
-/

@[expose] public section

open ENNReal OracleSpec OracleComp QueryImpl

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {ι' : Type} {spec' : OracleSpec ι'}
  {α : Type}

/-! ## Bad-input monotonicity wrappers (`σ × Bool` shape) -/

private lemma withProgramming_mono_pair
    (so : QueryImpl spec (OracleComp spec')) (policy : ProgrammingPolicy spec)
    (t : spec.Domain) (p : spec.QueryCache × Bool) (hp : p.2 = true)
    (z) (hz : z ∈ support ((so.withProgramming policy t).run p)) : z.2.2 = true := by
  rcases p with ⟨cache, b⟩
  subst hp
  exact QueryImpl.withProgramming_bad_monotone (so := so) (policy := policy) t cache z hz

private lemma withCachingTrackingPolicy_mono_pair
    (so : QueryImpl spec (OracleComp spec')) (policy : ProgrammingPolicy spec)
    (t : spec.Domain) (p : spec.QueryCache × Bool) (hp : p.2 = true)
    (z) (hz : z ∈ support ((so.withCachingTrackingPolicy policy t).run p)) :
    z.2.2 = true := by
  rcases p with ⟨cache, b⟩
  subst hp
  exact QueryImpl.withCachingTrackingPolicy_bad_monotone (so := so) (policy := policy) t cache z hz

variable [∀ t, MeasurableSpace (spec'.Range t)] [∀ t, DiscreteMeasurableSpace (spec'.Range t)]
  [IsMeasureSpec spec']

/-! ## Per-step agreement on good outputs -/

/-- From a good input, the programmed oracle and its tracking partner give every event the same
probability on good outputs. -/
private lemma prEvent_withProgramming_and_not_bad_eq
    (so : QueryImpl spec (OracleComp spec')) (policy : ProgrammingPolicy spec)
    (t : spec.Domain) (s : spec.QueryCache × Bool) (hs : ¬s.2 = true)
    (q : spec.Range t × (spec.QueryCache × Bool) → Prop) :
    Pr{let z ← (so.withProgramming policy t).run s}[q z ∧ ¬z.2.2 = true] =
      Pr{let z ← (so.withCachingTrackingPolicy policy t).run s}[q z ∧ ¬z.2.2 = true] := by
  rcases s with ⟨cache, b⟩
  obtain rfl : b = false := by simpa using hs
  cases hcache : cache t with
  | some v =>
    have hL : (so.withProgramming policy t).run (cache, false) =
        (pure (v, (cache, false)) :
          OracleComp spec' (spec.Range t × spec.QueryCache × Bool)) := by
      simp [QueryImpl.withProgramming_apply, hcache]
    have hR : (so.withCachingTrackingPolicy policy t).run (cache, false) =
        (pure (v, (cache, false)) :
          OracleComp spec' (spec.Range t × spec.QueryCache × Bool)) := by
      simp [QueryImpl.withCachingTrackingPolicy_apply, hcache]
    rw [hL, hR]
  | none =>
    cases hpol : policy t with
    | none =>
      have hL : (so.withProgramming policy t).run (cache, false) =
          (so t >>= fun u' => pure (u', (cache.cacheQuery t u', false)) :
            OracleComp spec' (spec.Range t × spec.QueryCache × Bool)) := by
        simp [QueryImpl.withProgramming_apply, hcache, hpol, Functor.map_map]
      have hR : (so.withCachingTrackingPolicy policy t).run (cache, false) =
          (so t >>= fun u' => pure (u', (cache.cacheQuery t u', false)) :
            OracleComp spec' (spec.Range t × spec.QueryCache × Bool)) := by
        simp [QueryImpl.withCachingTrackingPolicy_apply, hcache, hpol, Functor.map_map]
      rw [hL, hR]
    | some v =>
      have hL : (so.withProgramming policy t).run (cache, false) =
          (pure (v, (cache.cacheQuery t v, true)) :
            OracleComp spec' (spec.Range t × spec.QueryCache × Bool)) := by
        simp [QueryImpl.withProgramming_apply, hcache, hpol]
      have hR : (so.withCachingTrackingPolicy policy t).run (cache, false) =
          (so t >>= fun u' => pure (u', (cache.cacheQuery t u', true)) :
            OracleComp spec' (spec.Range t × spec.QueryCache × Bool)) := by
        simp [QueryImpl.withCachingTrackingPolicy_apply, hcache, hpol, Functor.map_map]
      rw [hL, hR, prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => h.2 (by
          rw [support_pure, Set.mem_singleton_iff] at hz
          rw [hz]),
        prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => h.2 (by
          obtain ⟨u', -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
          rw [support_pure, Set.mem_singleton_iff] at hz
          rw [hz])]

/-! ## Total variation bounds -/

/-- Joint (state-included) identical-until-bad bound between `withProgramming policy` and its
tracking partner `withCachingTrackingPolicy policy`. The conclusion keeps the final
`(cache, bad)` state, so a state-dependent continuation (e.g. GPV `verify` reading the run's
cache) can be appended on both sides. -/
theorem measureETVDist_withProgramming_withCachingTrackingPolicy_run_le_prEvent_bad
    [MeasurableSpace (α × spec.QueryCache × Bool)]
    (so : QueryImpl spec (OracleComp spec')) (policy : ProgrammingPolicy spec)
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    measureETVDist ((simulateQ (so.withProgramming policy) oa).run (cache, false))
        ((simulateQ (so.withCachingTrackingPolicy policy) oa).run (cache, false)) ≤
      Pr{let z ← (simulateQ (so.withProgramming policy) oa).run (cache, false)}[z.2.2 = true] :=
  measureETVDist_simulateQ_run_le_prEvent_bad _ _ (fun s => s.2 = true)
    (prEvent_withProgramming_and_not_bad_eq so policy) (withProgramming_mono_pair so policy)
    (withCachingTrackingPolicy_mono_pair so policy) oa (cache, false)

/-- The total variation between the output measure of `so.withCaching` and the output measure of
`so.withProgramming policy` is bounded by the probability that the bad flag of
`withProgramming policy` fires (i.e., the adversary queries a programmed point) during the run.

This is the user-facing "identical until bad" bound: programming an oracle is indistinguishable
from the unprogrammed oracle until the adversary queries a programmed point. The bound controls
the answer measure under the unprogrammed oracle by the bad-event probability under the
programmed oracle. -/
theorem measureETVDist_simulateQ_withCaching_withProgramming_le_prEvent_bad [MeasurableSpace α]
    (so : QueryImpl spec (OracleComp spec')) (policy : ProgrammingPolicy spec)
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    measureETVDist ((simulateQ so.withCaching oa).run' cache)
        ((simulateQ (so.withProgramming policy) oa).run' (cache, false)) ≤
      Pr{let z ← (simulateQ (so.withProgramming policy) oa).run (cache, false)}[z.2.2 = true] := by
  rw [← withCachingTrackingPolicy_run'_eq' so policy oa cache false, measureETVDist_comm]
  exact measureETVDist_simulateQ_run'_le_prEvent_bad _ _ (fun s => s.2 = true)
    (prEvent_withProgramming_and_not_bad_eq so policy) (withProgramming_mono_pair so policy)
    (withCachingTrackingPolicy_mono_pair so policy) oa (cache, false)

/-! ## Programming collision bound -/

/-- The probability that the bad flag of `withProgramming policy` fires on input `oa`, started
from an empty cache and `bad := false`. The flag flips on the first cache-miss whose query input
lies in the policy's support; this abbreviation isolates that probability so downstream
union-bound arguments can name it. -/
noncomputable abbrev withProgrammingBadProb
    (so : QueryImpl spec (OracleComp spec'))
    (policy : ProgrammingPolicy spec) (oa : OracleComp spec α) : ℝ≥0∞ :=
  Pr{let z ← (simulateQ (so.withProgramming policy) oa).run (∅, false)}[z.2.2 = true]

/-- **Programming collision bound.**

The total variation between running `oa` under pure caching and under a `policy`-programming
oracle is bounded by any upper bound `B` on the bad-event probability of `withProgramming
policy`.

The canonical `qP * qH * β` Fiat-Shamir slack is recovered by instantiating
`B := (qP : ℝ≥0∞) * qH * β` (see `programming_collision_bound_qP_qH_β`) and discharging `hBad`
via a union bound over the at most `qP` programmed points (each contributing at most `qH * β`
by per-step unpredictability of the queried inputs). For Schnorr with `spec.Domain = M × Commit`,
`β = 1/|G|`, `qP = qS`, and effective `qH = qS + qH`, this matches `collisionSlack qS qH G`. -/
theorem programming_collision_bound [MeasurableSpace α]
    (oa : OracleComp spec α)
    (so : QueryImpl spec (OracleComp spec'))
    (policy : ProgrammingPolicy spec)
    {B : ℝ≥0∞} (hBad : withProgrammingBadProb so policy oa ≤ B) :
    measureETVDist ((simulateQ so.withCaching oa).run' ∅)
        ((simulateQ (so.withProgramming policy) oa).run' (∅, false)) ≤ B :=
  (measureETVDist_simulateQ_withCaching_withProgramming_le_prEvent_bad so policy oa ∅).trans hBad

/-- Convenience repackaging of `programming_collision_bound`: a bad-event bound of the canonical
`qP * qH * β` shape bounds the total variation by the canonical Fiat-Shamir slack. The caller
need only discharge `hBad` (typically by a union bound over at most `qP` programmed points, each
hit with probability `≤ qH * β`). -/
theorem programming_collision_bound_qP_qH_β [MeasurableSpace α]
    (oa : OracleComp spec α) (qH qP : ℕ) (β : ℝ≥0∞)
    (so : QueryImpl spec (OracleComp spec'))
    (policy : ProgrammingPolicy spec)
    (hBad : withProgrammingBadProb so policy oa ≤ (qP : ℝ≥0∞) * qH * β) :
    measureETVDist ((simulateQ so.withCaching oa).run' ∅)
        ((simulateQ (so.withProgramming policy) oa).run' (∅, false)) ≤
      (qP : ℝ≥0∞) * qH * β :=
  programming_collision_bound oa so policy hBad

/-! ## Lazy random-oracle state-threading bridge

The specialization to the lazy random oracle `OracleSpec.randomOracle =
uniformSampleImpl.withCaching`, whose base implementation lives in `ProbComp`. This is the
reusable state-threading infrastructure consumed by the GPV hash-and-sign EUF-CMA reduction: it
replaces the unprogrammed lazy random oracle by a `policy`-programmed one, up to the programming
bad event. -/

omit [∀ t, MeasurableSpace (spec'.Range t)] [∀ t, DiscreteMeasurableSpace (spec'.Range t)]
  [IsMeasureSpec spec'] in
/-- **Random-oracle state-threading bridge.**

For a lazy random oracle over a spec with sampleable ranges, the total variation between the
output measure of the unprogrammed run (`simulateQ spec.randomOracle oa`, started from `cache`)
and the programmed run (`simulateQ (uniformSampleImpl.withProgramming policy) oa`, started from
`(cache, false)`) is bounded by the probability that the programming bad flag fires. -/
theorem measureETVDist_simulateQ_randomOracle_withProgramming_le_prEvent_bad
    [∀ t : spec.Domain, SampleableType (spec.Range t)] [MeasurableSpace α]
    (policy : OracleSpec.ProgrammingPolicy spec)
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    measureETVDist ((simulateQ spec.randomOracle oa).run' cache)
        ((simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) oa).run' (cache, false)) ≤
      Pr{let z ← (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) oa).run
          (cache, false)}[z.2.2 = true] :=
  measureETVDist_simulateQ_withCaching_withProgramming_le_prEvent_bad
    (spec' := unifSpec) uniformSampleImpl policy oa cache

end OracleComp.ProgramLogic.Relational
