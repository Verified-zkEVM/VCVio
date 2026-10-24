# S023_11 gpv_measureTVDist_orig_verify_le_collisionBound — arm A

- Minutes: ~6
- Result: 27 lines / 720 HB (original 39 / 1123). Accepted. Header is 22 of the 27 lines.
- Tried: keeping the ENNReal chain with one shared `collisionBound ≠ ⊤` fact (30 lines, 948 HB);
  `..` for the step lemmas (fails: it also fills the per-query `t s hs q` arguments, so the
  partial application is not a function any more); `exact` vs `<|`-chained term (the chained
  term elaborates against the expected type: ~800 HB vs ~7000 HB when the `.trans` heads are
  elaborated without it).
- What shortened it: do the chain in ℝ with `toReal_mono (prEvent_ne_top _)` instead of in ℝ≥0∞,
  so the toReal-valued `gpv_orig_flag_le_collisionBound` is used directly and the
  `collisionBound ≠ ⊤` side condition (proved twice in the original) disappears; all explicit
  parameters of the step lemmas inferred by unification (`_`).
- Missing:
  - An until-bad lemma stated directly for `measureTVDist` (real-valued), i.e.
    `measureTVDist ((simulateQ impl₁ oa).run s) ((simulateQ impl₂ oa).run s) ≤
      (Pr[bad z.2 | (simulateQ impl₁ oa).run s]).toReal`, so no `measureETVDist`/`toReal` bridge.
  - A "bad-event continuation" lemma: if `kont` cannot change the bad flag (per-query
    `IsQueryBoundP` on bad-moving queries + handler step preserves flag), then
    `Pr[bad | sim (oa >>= kont)] ≤ Pr[bad | sim oa]` generically (here
    `prEvent_flag_bind_no_sign_le` is a file-specific instance of it).
  - Handler-level "bad mono" facts derivable automatically (a `handler_step`-style tactic for
    `∀ z ∈ support ((impl t).run s), bad z.2`), would remove the two `_bad_mono` helper lemmas
    elsewhere in the file (not counted here).

## B
- Minutes: ~2. B = A + import: 27 lines / 721 HB (A 27 / 720).
- Looked at T1/Bisim identical-until-bad forms: `prEvent_simulateQ_run'_le_add_prEvent_bad`,
  `abs_toReal_prEvent_simulateQ_run'_sub_le` — both are `run'`/event forms. The goal is a
  `measureTVDist` of full runs (`.run`, state kept, verify continuation reads the cache), so
  they do not apply. Missing:
  `measureTVDist ((simulateQ i₁ oa).run s) ((simulateQ i₂ oa).run s) ≤
    (Pr[bad z.2 | (simulateQ i₁ oa).run s]).toReal` (real, full-run until-bad), and a
  "bad flag unchanged by a continuation with no bad-moving queries" lemma (`IsQueryBoundP … 0`
  on the queries that can raise the flag ⇒ `Pr[bad | sim (oa >>= k)] ≤ Pr[bad | sim oa]`).

## C
- Minutes: ~3. C = B + `Derive` import: 27 lines / 721 HB (B 27 / 721).
- T3 `GPVHashAndSign/FlagHandlers`: importing fails (imports this theorem's module); inlining is a
  **placement failure**: the module's `wp`/support lemmas use `gpvRealImplFlagFresh_run_inl`,
  `progGameRunImplNoRecFlagFresh_run_inl`, … which are declared after this theorem
  (line 828) in `FlagHandlers.lean`. (The theorem itself still elaborated in that test.)
- Even placed, nothing applies: the proof is a term chain through the until-bad TV lemma and
  file lemmas; the T3 `MonotoneState` instances (`flag never lowered`) restate the
  `*_bad_mono` facts the proof already passes by name, and are not shorter at the call site.
- Missing (as in B): a full-run real-valued until-bad lemma and a flag-preserving-continuation
  lemma.
