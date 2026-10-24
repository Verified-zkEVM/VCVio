# S023_02 chainInCache_of_mem_support_verifyOpening — arm A

- Minutes: ~6
- Original: 20 lines / 309 HB (unfold; rw bind/run_bind/mem_support_bind_iff; obtain; simp only
  on the final `pure`; obtain; `have` for `beq`; subst; exact the putative-root lemma).
- A: 13 lines / 308 HB, 153 tokens (vs 188).
- What shortened it: treat the trailing `return r == root` as a `map` (`bind_pure_comp`,
  `simulateQ_map`, `StateT.run_map`, `support_map`, `Set.mem_image`) instead of a bind with a pure
  continuation; `Prod.ext_iff` + `beq_iff_eq` let one `obtain ⟨_, h, rfl, rfl⟩` substitute both the
  root and the final cache.
- Tried: plain `simp [verifyOpening]` (1.8k HB, and rewrites `∈ support` into `CanReturn`, breaking
  the hand-off); `-MonadAttach.mem_support` fixes the shape but stays at 1.8k HB (outside gate).
- Missing:
  - `mem_support_simulateQ_run_map : (b, s') ∈ support ((simulateQ impl (f <$> oa)).run s) ↔
    ∃ a, (a, s') ∈ support ((simulateQ impl oa).run s) ∧ f a = b` (state-preserving map through a
    stateful handler run) — would collapse the 5-lemma map chain.
  - A support-level spec for `verifyOpening` directly (`(true, c') ∈ support … ↔ ∃ c'', (root, c')
    ∈ support (getPutativeRoot run)`) — this theorem is essentially that spec.

## B
- Minutes: ~4. 12 lines / 324 HB (A: 13 / 308).
- Library used: the `simulateQ_nf` simp set: `simp only [verifyOpening, simulateQ_nf, Bool.true_eq,
  beq_iff_eq] at hmem` replaces A's two-line hand-picked list (`bind_pure_comp, simulateQ_map,
  StateT.run_map, support_map, Set.mem_image, Prod.ext_iff`). The harness's `library` field is
  empty because the set's members are core lemmas tagged in `T1/RunNF`; the contribution is the
  attribute.
- Remaining friction: `simulateQ_nf` leaves the final `return (r == root)` step as
  `true = (x.1 == root)`; `Bool.true_eq` + `beq_iff_eq` are still needed (a `simulateQ_nf` member
  orienting `true = b` / `(a == b) = true` would make it `simp only [verifyOpening, simulateQ_nf]`).
  No `cachingOracle` support spec applies, since the run is of the opaque `getPutativeRootAddressedM`
  (handled by the file's own lemma).
