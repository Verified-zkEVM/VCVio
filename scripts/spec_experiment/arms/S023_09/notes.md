# S023_09 embedTrapFreshIdxImpl_run_inr — arm A

- Minutes: ~9
- Result: 14 lines / 1872 HB (original 16 / 1340). Accepted (HB ≤ 1.5× = 2010).
  Extra import `VCVio.ProgramLogic.Tactics.Handler` (for the `handler_nf` simp set).
- Tried: full `simp [embedTrapFreshIdxImpl, …]` (3.5k–4k HB, over gate); leave-one-out pruning of
  the original 15-lemma `simp only` list (every lemma but `add_apply_inr` is needed: 14 lemmas,
  3 lines); `handler_nf` + monad laws in one `simp only` (883–963 HB but 2 lines, 15 total);
  `…; simp only [monad_norm, bind_pure_comp]; rfl` (990 HB, 118 chars → 2 lines);
  `simp [handler_nf, embedTrapFreshIdxImpl, map_eq_bind_pure_comp, Function.comp_def]` loops.
- What shortened it: PolyFun's `handler_nf` simp set replaces the five `StateT.run_*` lemmas;
  the monad-law cleanup (`monadLift_self`, `pure ∘ f`, assoc) is then left to default `simp`.
- Missing:
  - A per-handler "run-shape" generator: `@[simp]`/`handler_simp` equations for
    `(impl₁ + impl₂) (.inr t) = impl₂ t` that fire *before* the definition is unfolded, i.e.
    a `QueryImpl.add_apply_inr` already in `handler_nf` (it is needed separately here).
  - `handler_nf` should include the monad-law normal form (`bind_assoc`, `pure_bind`,
    `monadLift_self`, `bind_pure_comp`/`map_eq_bind_pure_comp` in one orientation), so
    `simp only [impl, handler_nf]` closes "one-step unfolding" lemmas of a StateT handler
    directly (this pattern — `_run_inl_inl/_inl_inr/_inr` for each handler — recurs dozens of
    times in GPVHashAndSign).
  - Ideally a derive-handler-equations command generating these per-branch `run` equations.

## B
- Minutes: ~3. 14 lines / 1328 HB (A 14 / 1872; O 16 / 1340). Accepted.
- Library used: the `simulateQ_nf` simp set (sum dispatch `QueryImpl.add_apply_inr`,
  `StateT.run_*`, `monadLift_self`, monad laws) — the proof is
  `simp only [embedTrapFreshIdxImpl, simulateQ_nf, bind_pure_comp]` (one line, as in A, but
  −29% HB vs A because it replaces default `simp`). `bind_pure_comp` (core) is still needed:
  `simulateQ_nf` orients `x >>= fun a => pure (f a)` away from the `f <$> x` shape that the
  handler's stated run equation uses.
- Missing/not firing: a `simulateQ_nf` member producing the `<$>` form at the tail
  (`bind_pure_comp`), or a documented convention for which side `run` equations take.
- Not ported to A: needs the library simp set (A's best non-library variants were
  `handler_nf`+default `simp` (1872 HB) or a 2-line `simp only` list (883 HB)).

## C
- Minutes: ~5. 16 lines / 287 HB (B 14 / 1328). Accepted (HB gate), but 2 lines longer than B.
- Used: `derive_handler_specs embedTrapFreshIdxImpl` (one helper line); the proof is
  `simp only [embedTrapFreshIdxImpl.run_inr, bind_pure_comp]`. The derived `run_inr` is exactly
  the hand-written equation up to `bind_pure_comp` (derived RHS ends in `>>= fun x => pure …`,
  the stated one in `<$>`).
- Measurement caveats: (1) the `derive_handler_specs` command is not counted by the harness's
  heartbeats (`#count_heartbeats` is only put before declarations); measured separately it
  costs 1676 HB (so ≈1963 HB in total, ≈ A). (2) +1 line `omit [DecidableEq Range]
  [Fintype Salt] in`: the file's own `omit … in` before the docstring is consumed by the first
  helper command, so it has to be repeated before the theorem (without it, the theorem picks up
  unused instance arguments and later uses break).
- T3 `GPVHashAndSign/TrapCount`: importing it fails (it imports this theorem's module); inlining
  it is a **placement failure** — its support lemmas for `embedTrapFreshIdxImpl` are proved with
  `embedTrapFreshIdxImpl_run_inr`, i.e. the theorem being proved. Its contents (support iffs,
  `wp` specs) are downstream of this run equation anyway.
- Missing: a deriver option to state the run equation in the `<$>`-tail form (or generate it
  under a user-chosen name), so it could *replace* hand-written `_run_*` lemmas instead of
  duplicating them.
