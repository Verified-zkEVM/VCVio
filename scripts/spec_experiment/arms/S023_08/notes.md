# S023_08 simulateQ_prfReal_unlinkToMultiplePRFReaderImpl_run — arm A

- Minutes: ~5
- Original: 57 lines / 857 HB (local `impl`, `hquery` per-query fact, `hmapM` by induction over
  the tag list, `hAccept` decide-equality by a two-direction `rintro` proof, then `change` + two
  `simp only`).
- A: 12 lines / ~1150 HB, 146 tokens (vs 552): a single
  `simp [unlinkToMultiplePRFReaderImpl, unlinkReaderQueryImpl, unlinkReaderAccepts, tagAccepts,
  multiplePattern, simulateQ_list_mapM, TagReaderPRFs.multiplePRFScheme]`.
- What shortened it: existing simp lemmas cover everything — `simulateQ_list_mapM` (simulateQ
  through `List.mapM`), the `@[simp]` `simulateQ_prfRealQueryImpl_functionQuery`, core
  `List.mapM_pure`, and `exists_const` (with `NeZero` ⇒ `Nonempty (Fin n)`) for the
  `∃ sid : Fin n` in the acceptance predicate. The `hmapM` induction and the manual `hAccept`
  iff were redundant.
- Missing: `simulateQ_list_mapM` is not `@[simp]`; had it been (and had the reader/tag impls and
  `multiplePRFScheme` simp-unfolding equations), the call would be `simp [unlink…Impl,
  unlinkReaderQueryImpl]`. A handler-level spec `simulateQ (prfRealQueryImpl prf k)
  (l.mapM fun x => functionQuery (g x)) = pure (l.map (prf.eval k ∘ g))` would also do it.

## B
- Minutes: ~2. B.lean = A.lean + import. 12 lines / 1150 HB (A: 12 / 1147).
- Library lemmas used: none. A is already one `simp` call; `simulateQ_nf` contains the
  bind/map/StateT run laws that simp uses here but not `simulateQ_list_mapM`, which is the lemma
  that matters. Missing: `simulateQ_list_mapM` (and `List.mapM` of `simulateQ` of pure-valued
  queries) in `simulateQ_nf`; a T2 spec for `PRFScheme.prfRealQueryImpl` (a stateless handler
  answering `functionQuery d` by `pure (eval k d)`) would be the natural handler spec.
