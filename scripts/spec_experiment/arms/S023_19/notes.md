# S023_19 dcAux_reader_step — arm A (partial re-proof)

- Minutes: ~20 (well inside the 150-min timebox; stopped at diminishing returns)
- Result: 252 lines / 19901 HB (original 554 / 24820). Accepted (HB ≤ 1.5×; lines ≤ 0.6×).
  ~75 of the 252 lines are the (unchanged) statement; the proof body went from ~480 to ~177.
- What shortened it (structure kept, mechanics replaced):
  1. The four 33-line `hLHS_irr`/`hBAD_irr` blocks (true/false × output/bad event) became one
     generic `hirr` (∀ reply, observation `f`, event `E` invariant under resetting `cacheBad`),
     proved once from `simulateQ_multipleBadTableHandlerFine_cacheBad_irrelevant` +
     `prEvent_bind_congr` + `prEvent_map`, applied with `Iff.rfl` side conditions. Also hoisted
     the `ih` application before the `m` case split (reply `ofBool m`).
  2. Head reader-query collapse: the three restated `hM_eq`/`hRHS_eq`/`hBAD_eq` equalities
     (~40 lines) became one `simp only [multipleBadTableFine_run_query_bind',
     singleTable_run'_query_bind', hMstep, hSstep]`, with `hMstep`/`hSstep` stated in
     "step `>>= f` = `f (reply, state)`" form (a plain `pure` form does not work: the `pure` is
     elaborated with `FreeM.instPure`, so the generic `pure_bind` never matches).
  3. Lazification: the two `hM_lazify`/`hRHS_lazify` equations are no longer stated; the `have`
     takes the type inferred from `evalDist_idealCacheMapM_bind_uniformTable_comp … (fun T => …)`
     (beta-reduced by `inferType`), after inlining the `mAcc`/`sAcc` `set`s so no let-unfolding
     is needed.
  4. Final ℝ≥0∞ bookkeeping (≈45 lines of `set`s and a `calc`) → split the `(qR'+1)` cast,
     one reassociation `show`, and `gcongr`, with the asymmetric-discard bound proved directly as
     the `gcongr` side goal (no restated `hDiscard`/`hEmass`), `g` inferred via
     `.trans (add_le_add le_rfl ?_)`.
  5. Many small facts (`hc₀Inv`, `hc₀cached`, `hcellConst`, `hRespInv'`, `htE`, `hmConst`,
     `hsTrue`, `hqRle'`, budget split, Bool split) as one/two-line terms or `simp` calls.
- Tried and failed: `rw`/`simp only` with `hirr` (fails: the `Pr{…}` elaborator picks the monad
  by `whnfR` of the first draw's type, so `hirr`'s `Pr` is over `FreeM unifSpec.toPFunctor`
  while the goal's is over `ProbComp`; `erw` needed); `grind` for the slot-positive/slot-0
  acceptance iff (fails); `simp only [... , pure_bind]` for the head step (instance mismatch).
- Missing:
  - A Pr-level (event-level) form of the `cacheBad` irrelevance — generically:
    "if `π` commutes the two runs (`π <$> run s = π <$> run s'`) and the event factors through
    `π`, then `Pr[E | mx >>= fun x => run x s] = Pr[E | mx >>= fun x => run x s']`"
    (`prEvent_bind_congr` + `prEvent_map` + `prEvent_congr`, ~25 lines here).
  - Handler step lemmas in "`step s >>= f = f (out, s')`" form (or a `pure_bind` that matches
    `FreeM.instPure`), i.e. a uniform `handler_nf` normal form for deterministic reader steps.
  - A rewrite-friendly lazification lemma (`Pr`-level, with the continuation inferred by
    `kabstract` instead of spelled out), e.g. a `conv`-style or `generalize`-based
    `lazify_cells` tactic for `tableExtending c g`.
  - `Pr{…}` elaboration that normalizes the monad (`ProbComp` vs its unfolding) so that `rw`
    with event-generic lemmas works without `erw`.

## B
- Minutes: ~4. B = A + import: 252 lines / 19885 HB (A 252 / 19901).
- Tried: `simulateQ_nf` to discharge the head reader-step equations `hMstep`/`hSstep`
  (`simp only [multipleBadTableHandlerFine, multipleTableHandler_reader_run_slotZeroSubTable,
  simulateQ_nf]`) — fails: the reader-run lemmas state the step as `pure (…)` elaborated with
  `PFunctor.FreeM.instPure`, and `simulateQ_nf`'s `pure_bind` does not match that instance path,
  leaving `pure x >>= f` (A closes it with `rfl`). Also considered `simulateQ_nf` for the head
  query collapse (it would rewrite `run'` to `Prod.fst <$> …` and push maps into binds, breaking
  the later syntactic lazification/`hirr` rewrites) and T1/Bisim's projection bisimulations
  (distribution-level; the needed fact is Pr-level under a two-draw prefix).
- Missing: `pure_bind`/`map_pure` variants in `simulateQ_nf` that fire on `FreeM.instPure`;
  a Pr-level state-projection/irrelevance rule under a common prefix
  (`(∀ s s', π <$> run s = π <$> run s') → E factors through π →
    Pr[E | mx >>= fun x => f <$> run x s] = Pr[E | mx >>= fun x => f <$> run x s']`); a
  discard rule in T1/ProbBounds comparing two continuations of one draw that agree off a bad set
  (`Pr[q | mx >>= f] ≤ Pr[q | mx >>= g] + Pr[bad | mx]`).

## C
- Minutes: ~10. C = B + imports of `Derive` and T3 `PRFTagReader/{Table,
  MultipleToHybridSetup, MultipleToHybridEagerSetup}` (they import cleanly): 252 lines /
  19881 HB (B 252 / 19885).
- Tried: `derive_handler_specs multipleBadTableHandlerFine` (and dry runs for
  `multipleTableHandler`, `singleTableHandler`) to drop the hand-stated head-step lemmas
  `hMstep`/`hSstep` and collapse the reader query by `simp only [… query_bind' …,
  multipleBadTableHandlerFine.apply_inr, multipleTableHandler_reader_run_slotZeroSubTable,
  singleTableHandler_reader_run, pure_bind]`. The derived `apply_inr` unfolds correctly, but the
  collapse stops at `pure (reply, s) >>= fun r => …`: the bind there is
  `PFunctor.FreeM.instBind` and the `pure` `PFunctor.FreeM.instPure` (the direct cslib instances
  that elaboration picks at type `ProbComp`), and `pure_bind`/`simulateQ_nf`, stated over
  `Monad.toBind`/`Monad.toApplicative`, does not unify with them (`?inst` cannot be solved from
  `Monad.toBind ?inst =?= FreeM.instBind`). A pure-bind example with only `instPure` explicit
  does simp; it is the direct `instBind` that blocks. So `hMstep`/`hSstep` (stated in
  `>>= f = f …` form and closed by `rfl`) stay. The derived lemmas for the table handlers stop at
  `unlinkReaderQueryImpl`, so they would not replace `*_reader_run` either.
- T3 PRFTagReader specs are support/`wp`/`MonotoneState` facts; this proof needs equalities in
  distribution / Pr-level facts (lazification, `cacheBad` irrelevance, discard), so none apply.
- Missing: `pure_bind`/`bind_assoc`/`map_bind` variants (or a simproc) for the direct
  `FreeM.instBind`/`instPure` instances in `simulateQ_nf` (this is the root cause of the B and C
  failures here); deriving through named sub-handlers (`unlinkReaderQueryImpl`) to the
  deterministic reader reply; the Pr-level irrelevance/discard rules listed in B.
