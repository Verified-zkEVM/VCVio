/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.QueryTracking.ProgrammingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# TV-distance bound for `withProgramming` vs `withCaching`

The headline theorem `tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad` bounds
the total variation distance between the output distribution of `withCaching` and the output
distribution of `withProgramming policy` by the probability that the bad flag of
`withProgramming policy` ever fires (i.e., the adversary queries a point on which `policy` is
defined).

The proof factors through the auxiliary `withCachingTrackingPolicy` (defined alongside
`withProgramming` in `OracleComp/QueryTracking/ProgrammingOracle.lean`):

* On every step from non-bad input `(cache, false)`, the head distributions of
  `withProgramming policy` and `withCachingTrackingPolicy policy` agree on **non-bad** outputs.
  On policy-firing steps, both implementations produce only bad outputs (with possibly
  different `(value, cache)` components). This is the exact shape consumed by
  `OracleComp.ProgramLogic.Relational.identical_until_bad_with_flag`.
* `withCachingTrackingPolicy_run'_eq` projects `withCachingTrackingPolicy` to `withCaching`
  on the output marginal, eliminating the auxiliary impl from the user-facing statement.

The bound applies to any underlying `so : QueryImpl spec (OracleComp spec)`, with the policy
acting on inputs of `spec`.

## Programming collision bound

Built directly on top of the headline TV-distance bound, `programming_collision_bound` is the
"collision-event" repackaging used by Fiat-Shamir-style identical-until-bad reductions: given
any upper bound `B` on `probEventBadOfWithProgramming so policy oa`, the TV-distance between
the unprogrammed and programmed runs is at most `B.toReal`. The convenience wrapper
`programming_collision_bound_qP_qH_β` specializes `B` to the textbook `qP * qH * β` shape so
callers only need to discharge a union-bound hypothesis. Both live in this `Relational`
namespace because they are TV-distance statements; the underlying `withProgramming` /
`withCaching` definitions and the `HasUnpredictableSample` typeclass remain in
`QueryTracking/`.
-/

open ENNReal OracleSpec OracleComp QueryImpl

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [IsUniformSpec spec]
variable {α : Type}

/-! ## Per-step distributional agreement on non-bad outputs -/

private lemma probOutput_withProgramming_eq_withCachingTrackingPolicy_of_not_bad_output
    (so : QueryImpl spec (OracleComp spec)) (policy : ProgrammingPolicy spec)
    (t : spec.Domain) (cache : spec.QueryCache)
    (u : spec.Range t) (cache' : spec.QueryCache) :
    Pr[= (u, (cache', false)) | (so.withProgramming policy t).run (cache, false)] =
      Pr[= (u, (cache', false)) | (so.withCachingTrackingPolicy policy t).run (cache, false)] := by
  classical
  cases hcache : cache t with
  | some v =>
    simp [QueryImpl.withProgramming_apply, QueryImpl.withCachingTrackingPolicy_apply, hcache]
  | none =>
    cases hpol : policy t with
    | _ =>
      simp [QueryImpl.withProgramming_apply, QueryImpl.withCachingTrackingPolicy_apply,
        hcache, hpol]

/-! ## Bad-input monotonicity wrappers (`σ × Bool` shape) -/

omit [IsUniformSpec spec] in
private lemma withProgramming_mono_pair
    (so : QueryImpl spec (OracleComp spec)) (policy : ProgrammingPolicy spec)
    (t : spec.Domain) (p : spec.QueryCache × Bool) (hp : p.2 = true)
    (z) (hz : z ∈ support ((so.withProgramming policy t).run p)) : z.2.2 = true := by
  rcases p with ⟨cache, b⟩
  subst hp
  exact QueryImpl.withProgramming_bad_monotone (so := so) (policy := policy) t cache z hz

omit [IsUniformSpec spec] in
private lemma withCachingTrackingPolicy_mono_pair
    (so : QueryImpl spec (OracleComp spec)) (policy : ProgrammingPolicy spec)
    (t : spec.Domain) (p : spec.QueryCache × Bool) (hp : p.2 = true)
    (z) (hz : z ∈ support ((so.withCachingTrackingPolicy policy t).run p)) :
    z.2.2 = true := by
  rcases p with ⟨cache, b⟩
  subst hp
  exact QueryImpl.withCachingTrackingPolicy_bad_monotone (so := so) (policy := policy) t cache z hz

/-! ## TV-distance bound -/

/-- TV-distance between the output marginal of `withProgramming policy` and the output marginal
of `withCachingTrackingPolicy policy` is bounded by the probability that the bad flag of
`withProgramming policy` fires during the run. -/
private theorem tvDist_withProgramming_withCachingTrackingPolicy_le_probEvent_bad
    (so : QueryImpl spec (OracleComp spec)) (policy : ProgrammingPolicy spec)
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    tvDist
        ((simulateQ (so.withProgramming policy) oa).run' (cache, false))
        ((simulateQ (so.withCachingTrackingPolicy policy) oa).run' (cache, false))
      ≤ Pr[fun z : α × spec.QueryCache × Bool => z.2.2 = true |
          (simulateQ (so.withProgramming policy) oa).run (cache, false)].toReal := by
  exact identical_until_bad_with_flag
    (impl₁ := so.withProgramming policy)
    (impl₂ := so.withCachingTrackingPolicy policy)
    (oa := oa) (s₀ := cache)
    (probOutput_withProgramming_eq_withCachingTrackingPolicy_of_not_bad_output so policy)
    (withProgramming_mono_pair so policy)
    (withCachingTrackingPolicy_mono_pair so policy)

/-- TV-distance between the output marginal of `so.withCaching` and the output marginal of
`so.withProgramming policy` is bounded by the probability that the bad flag of
`withProgramming policy` fires (i.e., the adversary queries a programmed point) during the run.

This is the user-facing "identical until bad" bound: programming a random oracle is
indistinguishable from the unprogrammed oracle until the adversary queries a programmed point.
The bound is one-sided in the natural way for "ratchet" arguments: it controls the answer
distribution under the unprogrammed oracle by the bad-event probability under the programmed
oracle. -/
theorem tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad
    (so : QueryImpl spec (OracleComp spec)) (policy : ProgrammingPolicy spec)
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    tvDist
        ((simulateQ so.withCaching oa).run' cache)
        ((simulateQ (so.withProgramming policy) oa).run' (cache, false))
      ≤ Pr[fun z : α × spec.QueryCache × Bool => z.2.2 = true |
          (simulateQ (so.withProgramming policy) oa).run (cache, false)].toReal := by
  rw [(withCachingTrackingPolicy_run'_eq' so policy oa cache false).symm, tvDist_comm]
  exact tvDist_withProgramming_withCachingTrackingPolicy_le_probEvent_bad so policy oa cache

/-! ## Programming collision bound -/

/-- The bad-event probability of `withProgramming policy` on input `oa`, started from an empty
cache and `bad := false`. The bad flag flips on the first cache-miss whose query input lies in
the policy's support; this abbreviation isolates that probability so downstream union-bound
arguments can name it. -/
noncomputable abbrev probEventBadOfWithProgramming
    (so : QueryImpl spec (OracleComp spec))
    (policy : ProgrammingPolicy spec) (oa : OracleComp spec α) : ℝ≥0∞ :=
  Pr[fun z : α × spec.QueryCache × Bool => z.2.2 = true |
      (simulateQ (so.withProgramming policy) oa).run (∅, false)]

/-- **Programming collision bound.**

The TV-distance between running `oa` under pure caching and under a `policy`-programming
oracle is bounded by any upper bound `B` on the bad-event probability of
`withProgramming policy` (provided `B < ∞`).

This is the user-facing wrapper around
`tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad`: the heavy lifting (the
identical-until-bad bridge between `withCaching` and `withProgramming`) is the headline
theorem of this file; here we just expose it under the canonical "collision" name and combine
it with a user-supplied bad-event bound `hBad`.

The canonical `qP * qH * β` Fiat-Shamir slack is recovered by instantiating
`B := (qP : ℝ≥0∞) * qH * β` (see `programming_collision_bound_qP_qH_β`) and discharging `hBad`
via a union bound over the at most `qP` programmed points (each contributing at most `qH * β`
by per-step unpredictability of the queried inputs). For Schnorr with `spec.Domain = M × Commit`,
`β = 1/|G|`, `qP = qS`, and effective `qH = qS + qH`, this matches `collisionSlack qS qH G`.

The per-point union bound itself depends on the structure of `oa`'s queries (specifically, an
unpredictability hypothesis on each query's input distribution); it is discharged in the
caller's setting. See `Examples/CommitmentScheme/` and `CryptoFoundations/FiatShamir/Sigma/`
for FS-flavored applications. -/
theorem programming_collision_bound
    (oa : OracleComp spec α)
    (so : QueryImpl spec (OracleComp spec))
    (policy : ProgrammingPolicy spec)
    {B : ℝ≥0∞} (hB_lt_top : B < ∞)
    (hBad : probEventBadOfWithProgramming so policy oa ≤ B) :
    tvDist
        ((simulateQ so.withCaching oa).run' ∅)
        ((simulateQ (so.withProgramming policy) oa).run' (∅, false))
      ≤ B.toReal :=
  (tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad so policy oa ∅).trans
    (ENNReal.toReal_mono hB_lt_top.ne hBad)

/-- Convenience repackaging of `programming_collision_bound`: when the user has a bad-event
bound of the canonical `qP * qH * β` shape, we get the canonical FS slack as the TV-distance
bound. The caller need only discharge `hBad` (typically by a union bound over at most `qP`
programmed points, each hit with probability `≤ qH * β`). -/
theorem programming_collision_bound_qP_qH_β
    (oa : OracleComp spec α) (qH qP : ℕ) (β : ℝ≥0∞) (hβ_lt_top : β < ∞)
    (so : QueryImpl spec (OracleComp spec))
    (policy : ProgrammingPolicy spec)
    (hBad : probEventBadOfWithProgramming so policy oa ≤ (qP : ℝ≥0∞) * qH * β) :
    tvDist
        ((simulateQ so.withCaching oa).run' ∅)
        ((simulateQ (so.withProgramming policy) oa).run' (∅, false))
      ≤ ((qP : ℝ≥0∞) * qH * β).toReal := by
  exact programming_collision_bound oa so policy
    (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.natCast_lt_top _)) hβ_lt_top)
    hBad

/-! ## Heterogeneous inner monad: ProbComp-valued random-oracle bridge

The bridges above fix the inner monad of the wrapped oracle to `OracleComp spec` (the same
spec as the simulated computation). The lazy random oracle `OracleSpec.randomOracle` is instead
`uniformSampleImpl.withCaching`, whose base implementation `uniformSampleImpl` lives in
`ProbComp = OracleComp unifSpec` — a *different* spec from the surface program. The bridge below
re-establishes the identical-until-bad TV-distance bound when the base implementation `so` is
valued in `OracleComp spec'` for an arbitrary uniform `spec'` (taking `spec' = unifSpec` recovers
the random-oracle case). It is driven by the heterogeneous engine
`tvDist_simulateQ_run_le_probEvent_output_bad` and the heterogeneous projection
`withCachingTrackingPolicy_run'_eq'`.

These lemmas are the random-oracle-state-threading component of the GPV hash-and-sign EUF-CMA
reduction (`VCVio/CryptoFoundations/GPVHashAndSign.lean`): they let one replace the unprogrammed
lazy random oracle by a programmed one up to the salt/programming bad event. -/

section HeterogeneousInner

variable {ι' : Type} {spec' : OracleSpec ι'} [IsUniformSpec spec']

omit [IsUniformSpec spec] in
/-- Per-step distributional agreement on non-bad outputs, with the base implementation valued in
`OracleComp spec'` (heterogeneous inner monad). This is the `spec'`-generalization of
`probOutput_withProgramming_eq_withCachingTrackingPolicy_of_not_bad_output`; the proof is
identical (case split on cache hit / policy fire) and uses nothing specific to the inner spec. -/
private lemma probOutput_withProgramming_eq_withCachingTrackingPolicy_of_not_bad_output'
    (so : QueryImpl spec (OracleComp spec')) (policy : ProgrammingPolicy spec)
    (t : spec.Domain) (cache : spec.QueryCache)
    (u : spec.Range t) (cache' : spec.QueryCache) :
    Pr[= (u, (cache', false)) | (so.withProgramming policy t).run (cache, false)] =
      Pr[= (u, (cache', false)) | (so.withCachingTrackingPolicy policy t).run (cache, false)] := by
  classical
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
      have hne : ∀ (w : spec.Range t) (c : spec.QueryCache),
          ((u, (cache', false)) : spec.Range t × spec.QueryCache × Bool) ≠ (w, (c, true)) := by
        intro w c hcontr
        injection hcontr with _ h2
        injection h2 with _ h3
        cases h3
      have hL_run : (so.withProgramming policy t).run (cache, false) =
          (pure (v, (cache.cacheQuery t v, true)) :
            OracleComp spec' (spec.Range t × spec.QueryCache × Bool)) := by
        simp [QueryImpl.withProgramming_apply, hcache, hpol]
      have hR_run : (so.withCachingTrackingPolicy policy t).run (cache, false) =
          (so t >>= fun u' => pure (u', (cache.cacheQuery t u', true)) :
            OracleComp spec' (spec.Range t × spec.QueryCache × Bool)) := by
        simp [QueryImpl.withCachingTrackingPolicy_apply, hcache, hpol, Functor.map_map]
      rw [hL_run, hR_run]
      rw [probOutput_pure, if_neg (hne v _)]
      rw [probOutput_bind_eq_tsum]
      symm
      refine ENNReal.tsum_eq_zero.mpr (fun u' => ?_)
      rw [probOutput_pure, if_neg (hne u' _), mul_zero]

omit [IsUniformSpec spec] in
/-- Joint (state-included) identical-until-bad TV-distance bound between `withProgramming policy`
and its tracking partner `withCachingTrackingPolicy policy`, with the base implementation valued
in `OracleComp spec'`. The conclusion keeps the final `(cache, bad)` state, so a state-dependent
continuation (e.g. GPV `verify` reading the run's cache) can be appended on both sides. -/
theorem tvDist_withProgramming_withCachingTrackingPolicy_run_le_probEvent_bad'
    (so : QueryImpl spec (OracleComp spec')) (policy : ProgrammingPolicy spec)
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    tvDist
        ((simulateQ (so.withProgramming policy) oa).run (cache, false))
        ((simulateQ (so.withCachingTrackingPolicy policy) oa).run (cache, false))
      ≤ Pr[fun z : α × spec.QueryCache × Bool => z.2.2 = true |
          (simulateQ (so.withProgramming policy) oa).run (cache, false)].toReal := by
  refine tvDist_simulateQ_run_le_probEvent_output_bad
    (impl₁ := so.withProgramming policy)
    (impl₂ := so.withCachingTrackingPolicy policy)
    (oa := oa) (s₀ := cache)
    (fun t s u s' =>
      probOutput_withProgramming_eq_withCachingTrackingPolicy_of_not_bad_output'
        so policy t s u s') ?_ ?_
  · intro t p hp z hz
    rcases p with ⟨c, b⟩; cases (show b = true from hp)
    exact QueryImpl.withProgramming_bad_monotone (so := so) (policy := policy) t c z hz
  · intro t p hp z hz
    rcases p with ⟨c, b⟩; cases (show b = true from hp)
    exact QueryImpl.withCachingTrackingPolicy_bad_monotone (so := so) (policy := policy) t c z hz

omit [IsUniformSpec spec] in
/-- **Heterogeneous identical-until-bad bridge (output marginal).**

The TV-distance between the output marginal of `so.withCaching` and the output marginal of
`so.withProgramming policy` is bounded by the probability that the bad flag of
`withProgramming policy` fires during the run, for any base implementation `so` valued in
`OracleComp spec'` with `spec'` uniform.

This is the `spec'`-generalization of
`tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad`; specializing `so` to
`uniformSampleImpl` (so `spec' = unifSpec`) gives the lazy-random-oracle bridge
`tvDist_simulateQ_randomOracle_withProgramming_le_probEvent_bad`. -/
theorem tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad'
    (so : QueryImpl spec (OracleComp spec')) (policy : ProgrammingPolicy spec)
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    tvDist
        ((simulateQ so.withCaching oa).run' cache)
        ((simulateQ (so.withProgramming policy) oa).run' (cache, false))
      ≤ Pr[fun z : α × spec.QueryCache × Bool => z.2.2 = true |
          (simulateQ (so.withProgramming policy) oa).run (cache, false)].toReal := by
  classical
  set sim₁ := (simulateQ (so.withProgramming policy) oa).run (cache, false) with hs1
  set sim₂ := (simulateQ (so.withCachingTrackingPolicy policy) oa).run (cache, false) with hs2
  have h_joint :
      tvDist sim₁ sim₂ ≤
        Pr[fun z : α × spec.QueryCache × Bool => z.2.2 = true | sim₁].toReal :=
    tvDist_withProgramming_withCachingTrackingPolicy_run_le_probEvent_bad' so policy oa cache
  have h_map :
      tvDist ((simulateQ (so.withProgramming policy) oa).run' (cache, false))
          ((simulateQ (so.withCachingTrackingPolicy policy) oa).run' (cache, false))
        ≤ tvDist sim₁ sim₂ := by
    simpa [hs1, hs2, StateT.run'] using
      (tvDist_map_le (m := OracleComp spec') (α := α × spec.QueryCache × Bool) (β := α)
        Prod.fst sim₁ sim₂)
  have h_proj :
      (simulateQ (so.withCachingTrackingPolicy policy) oa).run' (cache, false) =
        (simulateQ so.withCaching oa).run' cache :=
    withCachingTrackingPolicy_run'_eq' so policy oa cache false
  rw [tvDist_comm, ← h_proj]
  exact le_trans h_map h_joint

end HeterogeneousInner

/-! ## Lazy random-oracle state-threading bridge

The specialization of the heterogeneous bridge to the lazy random oracle
`OracleSpec.randomOracle = uniformSampleImpl.withCaching`. This is the reusable state-threading
infrastructure consumed by the GPV hash-and-sign EUF-CMA reduction: it replaces the unprogrammed
lazy random oracle by a `policy`-programmed one, up to the programming bad event. -/

/-- **Random-oracle state-threading bridge.**

For a lazy random oracle over a spec with sampleable ranges, the TV-distance between the output
marginal of the unprogrammed run (`simulateQ spec.randomOracle oa`, started from `cache`) and the
programmed run (`simulateQ (uniformSampleImpl.withProgramming policy) oa`, started from
`(cache, false)`) is bounded by the probability that the programming bad flag fires.

This instantiates `tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad'` at
`so := uniformSampleImpl` (so the inner monad is `ProbComp = OracleComp unifSpec`), using
`OracleSpec.randomOracle = uniformSampleImpl.withCaching` definitionally. -/
theorem tvDist_simulateQ_randomOracle_withProgramming_le_probEvent_bad
    {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ t : spec.Domain, SampleableType (spec.Range t)] [IsUniformSpec spec] {α : Type}
    (policy : OracleSpec.ProgrammingPolicy spec)
    (oa : OracleComp spec α) (cache : spec.QueryCache) :
    tvDist
        ((simulateQ spec.randomOracle oa).run' cache)
        ((simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) oa).run' (cache, false))
      ≤ Pr[fun z : α × spec.QueryCache × Bool => z.2.2 = true |
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) oa).run
            (cache, false)].toReal :=
  tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad'
    (spec' := unifSpec) uniformSampleImpl policy oa cache

end OracleComp.ProgramLogic.Relational
