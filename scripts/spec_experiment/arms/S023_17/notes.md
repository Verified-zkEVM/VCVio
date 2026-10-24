# S023_17 embedTrapIdxSigImpl_fresh_idx_cache_eq_general — arm A

- Minutes: ~7
- Result: 16 lines / 4849 HB (original 76 / 2544). Accepted via the line gate
  (16 ≤ 0.6×76, HB ≤ 5×); HB is 1.9× the original (the `grind` calls).
- Tried: `simp_all [QueryCache.cacheQuery_of_ne]` in every branch (works, 23 lines, but
  16.8k HB — over the 5× gate); `by_cases hk : k = mc` + `simp_all` (fails: `simp_all` does not
  substitute `k := mc` before `cacheQuery_self`; `rcases eq_or_ne k mc with rfl | hk` fixes it);
  `(support_map _ _).le hz` directly on the unrewritten `hz` (fails: the step `run` is only
  propositionally a `<$>`, needs the `_run_inl_inl` rewrite first).
- What shortened it: the existing generic `OracleComp.simulateQ_run_preservesInv` (induction over
  the computation, from `SimSemantics/StateT/PreservesInv`) replaces the hand-rolled induction and
  the `simulateQ_bind/StateT.run_bind/mem_support_bind_iff` peeling; per-query step obligations
  are then: rewrite with the file's `_run_*` lemma, `simp only` the support of
  `pure`/`<$>`/`>>=` into existentials, and `grind` (the `cacheQuery_self/of_ne` lemmas are
  already `grind =`), which handles the `if`/`Function.update`-style index table and the
  `Finset.insert` freshness case.
- Missing:
  - `QueryImpl.PreservesInv` combinators for sum handlers at the `simulateQ_run_preservesInv`
    level (`PreservesInv.add` exists but only for `StateT σ ProbComp` handlers built with `+`;
    here the handler is a `let`-bound `+` so the per-index split had to be done by `rintro`).
  - Support-of-step lemmas (`support_run_<handler>_<branch>` / `mem_support_..._iff`) generated
    alongside the `_run_*` equations — every branch spends a line turning the run equation into
    an existential; a `handler_support` simp set (support of pure/map/bind/match on cache) would
    let one `simp only [impl_run_*, handler_support] at hz; grind` cover all branches.
  - A cheaper decision procedure than `grind` for "state update via `cacheQuery`/pointwise `if`
    preserves a ∀-key invariant" (a `cacheQuery`-aware `ext`/case-split lemma:
    `(c.cacheQuery t u) k = if k = t then some u else c k`) would cut HB.

## B
- Minutes: ~4. 10 lines / 6961 HB (A 16 / 4849; O 76 / 2544). Accepted via the line gate
  (≤ 0.6× lines, ≤ 5× HB).
- Library used: `simulateQ_nf` on each step hypothesis, applied to the *definition*
  `embedTrapIdxSigImpl` (sum dispatch, `StateT` run of `get`/`set`/lifts, monad laws, support
  iffs), so the file's `_run_inl_inl/_inl_inr/_inr` equations are no longer needed; one
  `split at hz` for the cache-hit match, then `grind`. The whole step is a single
  `rintro … <;> simp only [impl, simulateQ_nf] at hz <;> (try split at hz <;> …) <;> grind`.
- Kept the existing `OracleComp.simulateQ_run_preservesInv` for the whole-run part: the library's
  `inv_of_mem_support_simulateQ_run` is equivalent but takes `Inv` implicitly, which cannot be
  inferred here (it would need writing out the 2-line invariant).
- Not ported to A: the non-library version (default `simp [impl, add_apply_*]`) works but costs
  15.4k HB (> 5× gate).
- Missing/not firing: `simulateQ_nf` does not reduce `match (cache t) with …` on a
  `QueryCache` lookup without a `split`; a "simp normal form for cached-lookup handlers" rule
  (`match c t with | some v => pure v | none => …` + `support` of it) would remove the `split`.
