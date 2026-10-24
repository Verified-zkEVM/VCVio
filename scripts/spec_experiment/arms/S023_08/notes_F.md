# S023_08 `simulateQ_prfReal_unlinkToMultiplePRFReaderImpl_run` (arm F)

- Minutes: ~2.
- Final: 12 lines / 1149 HB (original 57 / 857; HB ratio 1.34). ok=true.
- Proof: a single `simp [unlinkToMultiplePRFReaderImpl, unlinkReaderQueryImpl, simulateQ_list_mapM,
  unlinkReaderAccepts, tagAccepts, multiplePattern, TagReaderPRFs.multiplePRFScheme]`.
  The existing `@[simp] simulateQ_prfRealQueryImpl_functionQuery` and core `List.mapM_pure` collapse
  the mapM of PRF queries. `exists_const` (with `NeZero`) disposes of the session index.
- Library: `simulateQ_nf` also works in the same simp call (1178 HB, same line count), and
  `simp only [unlinkToMultiplePRFReaderImpl, unlinkReaderQueryImpl, simulateQ_nf, simulateQ_list_mapM,
  PRFScheme.simulateQ_prfRealQueryImpl_functionQuery, List.mapM_pure]` followed by
  `simp [unlinkReaderAccepts, tagAccepts, multiplePattern, TagReaderPRFs.multiplePRFScheme]`
  takes 938 HB at one more line. The library is not needed, though: the default simp set already
  does it. The original's length came from `change`/`erw` workarounds, a hand induction for `mapM`,
  and a 15-line hand proof of the acceptance iff.
- Library gap: `simulateQ_list_mapM` is not a member of `simulateQ_nf` (it had to be named). A
  `simulateQ`-of-`List.mapM` rule belongs in the set.
- Missing lemma: none needed.
