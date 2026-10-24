# S023_16 `evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending` (arm F)

- Minutes: ~9.
- Final: 45 lines / 6133 HB (original 230 / 5306; HB ratio 1.16; 18 of the 45 lines are the statement).
  ok=true. An intermediate version with `simp only` normalizations was 50 lines / 3796 HB.
- Proof: induction on the adversary as in the original, with every hand-written normalisation `have`
  replaced:
  * per query case, `simp [multipleBadQueryImpl_tag_run, multipleIdealQueryImpl_tag_run_of_lt …,
    multipleBadTableHandler, multipleTableHandler_tag_run_of_lt …]` (and the reader analogues) put
    both sides in bind normal form. `unlinkOracleSpec_range_inl/inr` is needed for `bind_assoc` to
    fire, which plain `simp` includes;
  * tag case: one `rw [evalDist_bind_bind_swap …]`, then a single
    `refine evalDist_bind_congr _ _ _ fun n => (evalDist_bind_congr_of_support _ _ _ fun r hr =>
    (ih _ _ _ _).trans ?_).trans (evalDist_idealCacheStep_bind_uniformTable_comp … cont)`, with
    the remaining cell consistency closed by `simp only [tableExtending, idealCacheStep_cache_self …]`;
  * reader case: the same shape with `evalDist_idealCacheMapM_bind_uniformTable_comp`. The
    acceptance iff (15 lines originally) is closed by `simp [idealCacheMapM_support …,
    unlinkReaderAccepts, tagAccepts, multiplePattern]`;
  * the exhausted-slot case is one `simpa … using ih none s c sB`; the `pure` case is `simp [hTable]`.
- Friction: `rw [ih]` fails (motive type mismatch between `Range (Sum.inl tag)` and
  `Option (TagTranscript …)` after simp), so `(ih _ _ _ _).trans` is used instead. The `cont`
  arguments of the absorption lemmas must be written out, since higher-order unification cannot
  infer them, and that costs about 8 lines.
- Library that helped: none. Expected but did not fit: T1 Bisim (`evalDistEq_simulateQ_run_of_impl_evalDistEq_on_inv`,
  `evalDistEq_map_run_simulateQ_of_query_map_evalDistEq`, `relTriple_*`). They need a per-step
  distributional equality along an invariant or a deterministic state projection. The lazy-cache
  versus eager-table coupling only holds after integrating the table, so neither applies. The T2
  RandomOracle/Seeded specs are about `randomOracle`/`seededOracle`, not this file's `idealCacheStep`.
- Missing generic lemma: an eager/lazy bisimulation for a stateful handler that reads a random
  table. It would reduce this theorem and its siblings in `Table.lean` to per-query steps. Shape, with
  the bad component inside `σ`:
  `(L : QueryImpl spec (StateT (σ × (D →ₒ R).QueryCache) ProbComp)) (E : (D → R) → QueryImpl spec (StateT σ ProbComp))
   (hstep : ∀ t s c (cont : (D → R) → spec.Range t × σ → ProbComp β),
     𝒟[L t (s, c) >>= fun p => $ᵗ (D → R) >>= fun g => cont (tableExtending p.2.2 g) (p.1, p.2.1)] =
     𝒟[$ᵗ (D → R) >>= fun g => E (tableExtending c g) t s >>= cont (tableExtending c g)]) :
   𝒟[(fun z => (z.1, z.2.1)) <$> (simulateQ L oa).run (s, c)] =
     𝒟[$ᵗ (D → R) >>= fun g => (simulateQ (E (tableExtending c g)) oa).run s]`.
