# S023_18 dcAux_tag_slotZero — arm A

- Minutes: ~18
- Original: 488 lines / 40588 HB (statement is 80 lines; proof ~408).
- A: 138 lines / ~8.5k HB (incl. a 6-line reusable helper, 600 HB, not counted by the harness);
  proof body ~52 lines. Accepted under both gates.
- Same mathematical route (head step equal on both worlds at slot zero; move the nonce draw
  outermost; no-disagreement split over the nonce; cache hit → IH at `c`; cache miss → resample
  the cell, IH at `c.cacheQuery cell u`), but no intermediate computation is ever restated:
  - head step: `simp only [run_query_bind' lemmas, map_bind]` then a second
    `simp only [handler unfolds, …_of_sessionsUsed_zero, …tag_run_of_lt, hsid,
    unlinkOracleSpec_range_inl, bind_assoc, pure_bind]` (two passes: unfolding the handler in
    the same pass pre-empts the `run_query_bind'` lemmas, since simp rewrites subterms first);
  - binder commutation: convert `prEvent` to `𝒟[·] {True}` and `rw` with
    `evalDist_bind_bind_bind_rotate ($ᵗ _) ($ᵗ _) ($ᵗ Nonce) _ .of_discrete` (twice) and
    `evalDist_bind_bind_swap` — replaces three ~25-line `have h…_comm` statements;
  - cell resampling: one `have hU f := evalDist_bind_bind_update …` and `rw [← hU, ← hU, ← hU]`,
    then `simp only [cell read, ← tableExtending_update_of_none, ← tableExtending_cacheQuery]`
    — replaces three ~30-line `h…_marg` statements;
  - IH via `(ih … _ _ _ …).trans_eq (by rw [add_assoc, add_assoc])` with states/caches inferred;
    the ε-slack `qRInit·qT ≤ qRInit·(qT+1)` is handled once up front by
    `le_trans ?_ (add_le_add_left (add_le_add_right (b := ?m) ?_ _) _)` + `gcongr; omega`;
  - invariants by `simpa`/`obtain ⟨rfl, rfl⟩; simp` instead of hand-built `cacheQuery_of_ne` chains.
- Pitfalls hit: `simp_all` in the invariant goals costs ~70k HB (it rewrites the huge `ih`);
  `ih` must first be normalised with `simp only [map_bind] at ih` to match the goal's form;
  `refine (lemma …).trans ?_` cannot leave `ε`/reference computations to be inferred later.
- Missing (would have shortened further):
  - an event-bound lemma in *normalised* (`map` pushed inside) form:
    `(∀ x ∈ support mx, prEvent (my x) ≤ prEvent (oc x) + prEvent (ob x) + ε) →
    prEvent (mx >>= my) ≤ prEvent (mx >>= oc) + prEvent (mx >>= ob) + ε` (written here as a
    reusable helper; every VCVio disagreement lemma is stated with `Pr{let y ← mx >>= f}[q y]`,
    which never matches after `simp [map_bind]`). Same for the `prEvent` versions of
    `evalDist_bind_bind_swap/rotate` and `evalDist_bind_bind_update` (`prEvent` congruence under
    `𝒟`-equalities without the `𝒟 {True}` round trip);
  - a simp-friendly "uniform table absorbs a cache miss" lemma:
    `c t = none → Pr[… $ᵗ g … tableExtending c g …] = Pr[… $ᵗ u; $ᵗ g … tableExtending
    (c.cacheQuery t u) g …]` as a single rewrite;
  - handler facts as `@[simp]` lemmas for `multipleBadTableHandlerFine` on tag queries
    (the slot-zero step equals the single-table step) so the head step is one `simp`;
  - `multipleBadAdvance_responses` simp lemmas (`… .responses (t, m) = if (t, m) = (tag, n) then
    … else sB.responses (t, m)`) — the invariant proofs.

## B
- Minutes: ~3. B.lean = A.lean + import. 138 lines / 9156 HB (A re-measured with helper HB
  counted: 138 / 9132).
- Library lemmas used: none.
- Looked for: a replacement for the 6-line helper `prEvent_bind_le_add_add`
  (`(∀ x ∈ support mx, prEvent (my x) ≤ prEvent (oc x) + prEvent (ob x) + ε) →
  prEvent (mx >>= my) ≤ prEvent (mx >>= oc) + prEvent (mx >>= ob) + ε`). T1 `ProbBounds` has the
  `prEvent (mx >>= g)` (normalised) form, but only as a union bound with a sup
  (`prEvent_bind_le_add_iSup`) or for StateT runs (`prEvent_run_bind_le_add_of_support`); neither
  keeps continuation-dependent reference events averaged over `mx`, which is what the coupling
  needs. `prEvent_uniformSample_bind_eq` could re-derive the helper for the two uniform prefixes
  but is longer. `evalDistEq_run_liftM_bind_swap` is a StateT-run swap, not the plain `ProbComp`
  rotate of three draws used here.
- `simulateQ_nf` for the head step: same situation as S023_16, where it was tested (A's single
  line already uses the file's `run_query_bind'` lemmas, and the handler lemmas are stated on
  `impl q s`, so they stop firing on `simulateQ_nf`'s `(impl t).run s` output).

## C
- Minutes: ~5. C.lean = B.lean with imports `VCVio.ProgramLogic.Library
  VCVio.ProgramLogic.Library.Derive …T3.PRFTagReader.{Table, MultipleToHybridSetup,
  MultipleToHybridEagerSetup}`. 138 lines / 9156 HB (B: 138 / 9156). No T3 lemma or derived
  equation used.
- Looked at: `derive_handler_specs? multipleBadTableHandlerFine` gives `run_inl` =
  `multipleTableHandler g (.inl q) s.1 >>= fun r => pure (r.1, r.2, multipleBadAdvance q s.2 r.1)`,
  which is what A gets from unfolding the definition; the slot-zero step equation
  (`multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero`) is semantic
  and not derivable. T3's `multipleBadAdvance_bad_mono` is about the flags; the invariant proofs
  need the `responses` field.
- Missing: `@[simp]` `multipleBadAdvance_responses` (`(multipleBadAdvance tag sB (some tr)).responses
  (t, m) = if (t, m) = (tag, tr.nonce) then some … else sB.responses (t, m)`), and the
  distribution-level facts listed under B (normalised-form event bound through a bind, prEvent
  rotate/swap/cell-resampling).
