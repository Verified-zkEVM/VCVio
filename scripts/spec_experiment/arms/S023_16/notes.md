# S023_16 evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending — arm A

- Minutes: ~7
- Original: 230 lines / 5306 HB.
- A: 52 lines / ~3.8k HB (no helpers).
- Same skeleton (induction on the adversary generalizing the state; tag-with-slot, tag-exhausted,
  reader), but every explicitly restated intermediate computation is gone:
  - both sides are normalised in place by one `simp only [handler run lemmas,
    unlinkOracleSpec_range_inl/inr, bind_assoc, pure_bind]`. Key trick: `bind_assoc` silently
    fails (motive not type-correct) until the `rfl`-lemma `unlinkOracleSpec_range_inl`
    rewrites the dependent oracle range `(UnlinkOracleSpec …).Range (Sum.inl tag)` to
    `Option (TagTranscript …)`; the original worked around this with ~60 lines of `have h… : <full
    statement> := by simp only [bind_assoc, pure_bind]` and `change`;
  - eager-table absorption lemmas are applied as `refine Eq.trans ?_ (lemma … cont)` so only the
    continuation `cont` has to be written (holes inside it, e.g. the post-state, are solved by
    unification); IH via `(ih _ _ r.2 _).trans ?_` (the IH's LHS matches only up to defeq, so `rw
    [ih]` fails);
  - choosing the reader continuation with `unlinkReaderAccepts` (rather than `decide (∃ d ∈ cells.map
    g', …)`) makes the final RHS match syntactically, and the per-table side condition is one
    `simp [idealCacheMapM_support …, unlinkReaderAccepts, tagAccepts, multiplePattern]` (the
    original's 12-line `hAccept`);
  - pure case: `simp [hTable]`; exhausted-slot case: one `simpa … using ih none s c _`.
- Missing (would have shortened further):
  - a generic "lazy-RO handler ≡ eager table handler" theorem for `StateT` handlers that consult a
    `QueryCache` only through `idealCacheStep`/`idealCacheMapM` and are otherwise deterministic in
    the table (this lemma, its un-instrumented twin `…multipleIdealQueryImpl_run'…`, and the single
    variant are all instances: 3+ copies of the same induction);
  - a `MonadLift (StateT σ₁ m) (StateT (σ₁ × σ₂) m)` / "extra passive state component" lemma: the
    instrumented handler differs from the ideal one only by a deterministic advance of a second
    state component, so the result should follow from the un-instrumented one;
  - `@[simp]` (or `dsimp`) normalisation of `OracleSpec.Range` of sum specs so `bind_assoc` fires.

## B
- Minutes: ~2. B.lean = A.lean + import. 52 lines / 3994 HB (A: 52 / 3820).
- Library lemmas used: none.
- Looked for: `simulateQ_nf` for the head step, but A's one line
  `simp only [multipleBad_run_query_bind', multipleBadTable_run_query_bind', map_bind]` is shared
  by all three query cases, and the file's handler lemmas are stated on `impl q s` rather than
  `(impl q).run s`. Tested: with `simp only [simulateQ_nf]` in its place, none of the per-case
  handler lemmas (`multipleBadQueryImpl_tag_run`, `multipleIdealQueryImpl_tag_run_of_lt`,
  `multipleBadTableHandler`, …) fire any more (unused-argument warnings, then `rw` failures).
  Reverted.
  The eager/lazy random-oracle facts in T2 `RandomOracle` are about `randomOracle`'s own runs
  (`run'_of_eq_none`, `prEvent_run'_eq_of_eq_none`), not about a composed handler that consults a
  cache through `idealCacheStep`; the bisimulation rules (`evalDistEq_simulateQ_run_of_impl_…`,
  `evalDistEq_map_run_simulateQ_of_query_map_evalDistEq`) compare two handlers with the same
  state shape per query, whereas here the two sides differ by an outer `$ᵗ table` draw.
  Missing: a lazy-vs-eager theorem "`(simulateQ (lazy c-handler) oa).run (s, c) =ᵈ
  ($ᵗ g >>= fun g => (simulateQ (table-handler (tableExtending c g)) oa).run s)` from per-query
  `=ᵈ` of the steps".
