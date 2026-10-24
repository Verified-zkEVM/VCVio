# S023_15 log_length_le_of_mem_support_counting_simulate_run_logging — arm A

- Minutes: ~12
- Result: 18 lines / 14749 HB (original 70 / 9598). Accepted via the line gate
  (18 ≤ 0.6×70 and HB ≤ 5×); HB is 1.54× the original, so not under the 1.5× gate on its own.
  Most HB are the default-`simp` calls on `hz`/`hb` (the `simp only` lists from `simp?` are
  15+ lemmas each and would add ~8 lines).
- Tried: closing the arithmetic with `Finset.sum_update_of_mem` +
  `Finset.sum_eq_add_sum_sdiff_singleton_of_mem` + `omega` (fails: the two `∑ x ∈ univ \ {t}`
  atoms carry different `Fintype`/`DecidableEq` instances — one elaborated at
  `(CMOracle M S C).Domain`, one at `M × S` — so `omega` sees two atoms; same for a
  `Finset.single_le_sum` fact); `omega` after `simp at h hz0 ⊢` (same instance problem).
- What shortened it: same induction skeleton, but (1) destructure `z` first so the image witness
  can be `rfl`-substituted, (2) let default `simp` turn
  `simulate (f <$> ob) 0` membership into an existential over the `runAdd` support (replacing the
  hand-proved `hmap` equation), (3) the existing `ToMathlib` lemma `sum_update_pred`
  (`∑ update qc t (qc t - 1) = ∑ qc - 1`) replaces the 12-line `hsum` derivation, and (4) finish
  by a defeq `trans_lt` (`(a :: l).length ≤ n` is `l.length < n`) with `Finset.sum_pos'`,
  avoiding all the `hz1/hzlog/hzqc/hcons` bookkeeping.
- Missing:
  - `countingOracle.simulate_map : simulate (f <$> oa) qc = Prod.map f id <$> simulate oa qc`
    (`@[simp]`), so `hz` could be rewritten with `simp only`/`rw` instead of full `simp`.
  - A per-path "log length = total count" lemma for the composed logging/counting run:
    `z ∈ support (countingOracle.simulate (simulateQ loggingOracle oa).run qc) →
      z.1.2.length + ∑ qc = ∑ z.2` (or more generally: for two `withCost`-style
    instrumentations of the same run, the two accumulated costs are related by the per-query
    cost relation). This would make the theorem a one-line corollary.
  - `mem_support_simulate_queryBind_iff` in a `QueryCount`-sum form
    (`∑ z.2 = ∑ qc' + 1` with `qc'` the decremented count) to avoid the `Function.update`
    arithmetic altogether.

## B
- Minutes: ~6. 13 lines / 9087 HB (A 18 / 14749; O 70 / 9598). Accepted (now also under the
  1.5× HB gate, and below the original's HB).
- Library used: `simulateQ_nf` (nested `simulateQ` runs, `WriterT.run_bind`, monad laws, and
  the support layer `mem_support_bind_iff`/`support_map`/`Set.mem_image`/`Prod.mk.injEq`),
  T2 `loggingOracle.run_apply` and `countingOracle.run_apply`.
- How: unfold `countingOracle.simulate`/`AddWriterT.runAdd` once, before the induction, so
  hypothesis and IH are in `WriterT.run` form; in the query case one
  `simp only [simulateQ_nf, loggingOracle.run_apply, countingOracle.run_apply] at hz` produces
  the existential chain directly, with the count of the step as
  `ofAdd (QueryCount.single t) * w` — additive, so the A-arm's `Function.update`/`sum_update_pred`
  arithmetic disappears (`simp [Finset.sum_add_distrib, QueryCount.single]; omega`).
- Not ported to A: the non-library equivalent (default `simp` on the same goal) gets stuck at
  `(loggingOracle t).run` under the counting simulation and already costs ~17k HB.
- Missing/not firing: a `simulateQ_nf` rule for `AddWriterT.runAdd` /
  `countingOracle.simulate` (had to unfold by hand); an `@[simp]`
  `∑ i, QueryCount.single t i = 1`; and the direct whole-run fact
  `z ∈ support (simulateQ countingOracle (simulateQ loggingOracle oa).run).run →
    z.1.2.length = ∑ i, toAdd z.2 i` (would make this a one-liner).
