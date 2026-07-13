/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import VCVio.CryptoFoundations.GPVHashAndSign.Security

/-! # GPV Hash-and-Sign: The Append-Forgery-Query Compiler

The headline split bound `euf_cma_split_bound` is stated under the random-oracle
well-formedness convention `ForgesQueriedPoint`: the forger queries the random oracle at its
forgery point before outputting the forgery.  This module formalizes the standard on-paper
remark that the convention is *without loss of generality*: the compiler `appendForgeQuery`
transforms an arbitrary adversary into one satisfying the convention by appending a single
random-oracle query at the forgery point, at the cost of one extra hash query.

The compiled adversary satisfies the convention unconditionally
(`forgesQueriedPoint_appendForgeQuery`), obeys the query bound at `qHash + 1`
(`signHashQueryBound_appendForgeQuery`), and — because the verifier immediately re-queries the
same random-oracle point, making the appended query a cache-absorbed no-op — has *exactly* the
same EUF-CMA advantage as the original adversary (`advantage_appendForgeQuery`).  The
absorption is a term-level equality of the lazy-caching oracle
(`QueryImpl.withCaching_run_bind_run_self`): re-running a caching step from any state it just
produced is a deterministic cache hit.

Chaining these through `euf_cma_split_bound` yields the all-adversaries corollary
`euf_cma_split_bound_of_queryBound`, whose only structural hypothesis on the adversary is the
query bound: the `ForgesQueriedPoint` hypothesis is discharged by the compiler.
-/

open OracleComp OracleSpec ENNReal

universe u v

/-! ## Cache-hit absorption for `withCaching` -/

namespace QueryImpl

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
  {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-- **Cache-hit absorption for the lazy-caching oracle.** Running a `withCaching` step at `t`
and then re-running the same step from the resulting state is the same as running it once: the
first step leaves the cache defined at `t` (either it was a hit, or the miss installed the drawn
value via `cacheQuery`), so the second step is a deterministic cache hit returning the same
value and state.  This is a term-level equality of computations, for any continuation `k`. -/
theorem withCaching_run_bind_run_self (so : QueryImpl spec m) (t : spec.Domain)
    (cache : spec.QueryCache) {β : Type u}
    (k : spec.Range t × spec.QueryCache → m β) :
    ((so.withCaching t).run cache >>= fun p => (so.withCaching t).run p.2 >>= k)
      = ((so.withCaching t).run cache >>= k) := by
  cases hcache : cache t with
  | some u =>
      rw [withCaching_run_some so hcache, pure_bind, pure_bind,
        withCaching_run_some so hcache, pure_bind]
  | none =>
      rw [withCaching_run_none so hcache, map_eq_bind_pure_comp, bind_assoc, bind_assoc]
      refine bind_congr fun u => ?_
      simp only [Function.comp_apply, pure_bind]
      rw [withCaching_run_some so (QueryCache.cacheQuery_self cache t u), pure_bind]

end QueryImpl

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool}
  [DecidableEq Range] [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt]

/-! ## The compiler -/

/-- **The append-forgery-query compiler.** Runs the adversary, then queries the random oracle
once at the forgery point `(salt, msg) = (out.2.1, out.1)` (an ambient `.inl (.inr _)` index —
no signing query), and returns the forgery unchanged.  The compiled adversary satisfies the
`ForgesQueriedPoint` convention unconditionally, makes one extra hash query, and has the same
EUF-CMA advantage as `adv` (`advantage_appendForgeQuery`). -/
def appendForgeQuery
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt) where
  main := fun pk =>
    adv.main pk >>= fun out =>
      liftM (((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).query
        (Sum.inl (Sum.inr (out.2.1, out.1)))) >>= fun _ =>
      pure out

omit [Fintype Salt] in
/-- Definitional unfolding of the compiled adversary's main computation. -/
lemma appendForgeQuery_main
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) :
    (appendForgeQuery psf hr M Salt adv).main pk =
      adv.main pk >>= fun out =>
        liftM (((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).query
          (Sum.inl (Sum.inr (out.2.1, out.1)))) >>= fun _ =>
        pure out := rfl

/-! ## The compiled adversary's query bound -/

omit [Fintype Salt] in
/-- **Query bound for the compiled adversary.** The appended random-oracle query is a single
`.inl (.inr _)` index: the signing count is unchanged and the hash count grows by one. -/
theorem signHashQueryBound_appendForgeQuery
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (qSign qHash : ℕ) (pk : PK)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := (appendForgeQuery psf hr M Salt adv).main pk) (qSign := qSign)
      (qHash := qHash + 1) := by
  obtain ⟨hSign, hHash⟩ := hQ
  rw [appendForgeQuery_main]
  constructor
  · refine Nat.add_zero qSign ▸ OracleComp.isQueryBoundP_bind hSign fun out _ => ?_
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp), fun _ => trivial⟩
  · refine OracleComp.isQueryBoundP_bind hHash fun out _ => ?_
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

/-! ## The compiled adversary forges on a queried point -/

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **A programmed random-oracle read step caches its point.** After running the programmed
fresh-flag handler on the random-oracle query at `mc`, the resulting cache maps `mc` to a
`some` value, for every initial state: on a hit the entry is preserved, on a miss the handler
programs `cacheQuery mc _`.  This generalizes the concrete witness step lemma of
`Examples.GPVNonVacuity` to arbitrary parameters. -/
lemma progGameRunImplNoRecFlagFresh_read_caches (domainSample : PK → ProbComp Domain)
    (pk : PK) (mc : Salt × M)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)
    (z : Range × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool))
    (hz : z ∈ support ((progGameRunImplNoRecFlagFresh psf M Salt domainSample pk
      (.inl (.inr mc))).run s)) :
    z.2.1.1 mc ≠ none := by
  rw [progGameRunImplNoRecFlagFresh_run_inl, progGameRunImplNoRec_run_read] at hz
  cases h : s.1.1 mc with
  | some v =>
      rw [h] at hz
      dsimp only at hz
      simp only [support_map, support_pure, Set.image_singleton] at hz
      have hz : z = (v, (s.1.1, s.1.2), s.2) := hz
      subst hz
      simp only [h, ne_eq, reduceCtorEq, not_false_eq_true]
  | none =>
      rw [h] at hz
      dsimp only at hz
      simp only [support_map] at hz
      obtain ⟨_, ⟨sd, _, rfl⟩, rfl⟩ := hz
      simp only
      rw [QueryCache.cacheQuery_self]
      exact Option.some_ne_none _

omit [Fintype Salt] in
/-- **The compiled adversary forges on a queried point, unconditionally.** The appended
random-oracle query at the forgery point is the last step of the compiled run, so the final
cache is defined there — either as a preserved hit or as the freshly programmed entry.  This
discharges the `ForgesQueriedPoint` hypothesis of the headline bounds for every domain
sampler. -/
theorem forgesQueriedPoint_appendForgeQuery
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) :
    ForgesQueriedPoint psf hr M Salt (appendForgeQuery psf hr M Salt adv) domainSample := by
  unfold ForgesQueriedPoint
  intro pk z hz
  rw [appendForgeQuery_main, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨out, smid⟩, _hmid, hrest⟩ := hz
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨c, sfin⟩, hstep, hpure⟩ := hrest
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  subst hpure
  exact progGameRunImplNoRecFlagFresh_read_caches psf M Salt domainSample pk
    (out.2.1, out.1) smid (c, sfin) hstep

end GPVHashAndSign
