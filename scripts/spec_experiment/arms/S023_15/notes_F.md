# S023_15 `log_length_le_of_mem_support_counting_simulate_run_logging` (arm F)

- Minutes: ~3.
- Final: 11 lines / 6516 HB (original 70 / 9598). ok=true.
- Proof: induction on `oa`. `pure`: `simp_all [countingOracle.simulate, AddWriterT.runAdd]`.
  `query_bind`: `simp only [countingOracle.simulate, AddWriterT.runAdd, simulateQ_nf] at hz ih`
  turns both into existentials over the counted logged run, then `obtain ⟨u, -, w, hw, rfl⟩ := hz`
  and `simpa [Finset.sum_add_distrib, QueryCount.single, Nat.lt_one_add_iff] using ih u ⟨w, hw, rfl⟩`.
- Library that helped: `simulateQ_nf` with its T2 members `loggingOracle.run_apply` and
  `countingOracle.run_apply` (both used; visible in the `@usage` report). It replaced
  `run_simulateQ_loggingOracle_query_bind`, `countingOracle.mem_support_simulate_queryBind_iff`, the
  15-line `hmap`, and the `hz1/hzlog/hzqc` projections. `QueryCount.single` arithmetic replaced the
  `hsum`/`hpredsucc`/`hsumpos` bookkeeping. About 55 lines saved in total, most of them by the simp set.
- Expected but did not fit: the whole-run WriterT principles (`inv_of_mem_support_simulateQ_writerT_run`,
  `prop_of_mem_support_simulateQ_writerT_run`). The property relates the inner run's output (the log
  length) to the outer writer log (the count). The counted program is itself a logging run, so a
  per-query step of the counting handler cannot see the log. `mem_of_mem_support_run_simulateQ_withCost`
  only gives membership in a submonoid. `countingOracle.simulate` and `AddWriterT.runAdd` are not in
  `simulateQ_nf` and had to be named.
- Missing generic lemma: a whole-run rule for nested writer handlers, so the induction disappears:
  `R 1 1 → (∀ a b c d, R a b → R c d → R (a*c) (b*d)) →
   (∀ t, ∀ z ∈ support (simulateQ impl₂ (impl₁ t).run).run, R z.1.2 z.2) →
   ∀ z ∈ support (simulateQ impl₂ (simulateQ impl₁ oa).run).run, R z.1.2 z.2`
  for `impl₁ : QueryImpl spec (WriterT ω₁ (OracleComp spec))` and `impl₂ : QueryImpl spec (WriterT ω₂ (OracleComp spec))`.
  Here `R log cnt := log.length = ∑ i, toAdd cnt i`. Adding `countingOracle.simulate` and
  `AddWriterT.runAdd` unfolding to `simulateQ_nf` would also help.
