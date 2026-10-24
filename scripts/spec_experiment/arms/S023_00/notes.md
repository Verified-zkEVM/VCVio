# S023_00 contextFork_propertyTransfer — arm A

- Minutes: ~8
- Original: 26 lines / 1227 HB (obtain from `contextFork_success`, two `let` logs, a `have` for the
  first lookup via `located.path_eq ▸ …`, `refine` with three `simpa` side goals).
- A: 14 lines / 1015 HB, 249 tokens (vs 329). Proof body is 3 lines.
- What shortened it:
  - destructure `located` as `⟨o, c, rfl⟩` so `path_eq` substitutes the path (no `▸` transport) and
    `rfl` the two output equations;
  - leave the logs as metavariables: `hP` applied to `replayPathResult_mem_support_replayFirstRun`
    unifies `(x, log)` with `pathLogResult = (output, trace)` definitionally, so no `simpa
    [replayPathResult]` is needed; one local `have k p := …` serves both branches (every path is
    supported, `mem_support_replayFirstPath`);
  - the inequality is `simpa [getQueryValue?_completion_path_eq_answer o] using hne` (the occurrence
    must be given explicitly, otherwise simp does not fire on `second.path`).
- Tried: `grind [getQueryValue?_completion_path_eq_answer]` for the last goal (works, 1.5k HB).
- Missing:
  - a combined "supported-path ⇒ supported first-run result" lemma with the path-support side
    condition discharged: `∀ path, (output main path, trace main path) ∈ support (replayFirstRun
    main)` (this is `k` above; 1 line saved here).
  - a version of `contextFork_success` that returns the `Located` already split
    (`occurrence`, `completion`) and the outputs substituted, i.e. stated with
    `x₁ = output main c.path` eliminated.

## B
- Minutes: ~2. B.lean = A.lean + import. 14 lines / 1018 HB (A: 14 / 1015).
- Library lemmas used: none. The goal is about PolyFun fork paths and `withQueryLog` first runs,
  not a `simulateQ` handler run; T2 `Logging` covers `loggingOracle` runs
  (`mem_support_of_mem_support_run_simulateQ_loggingOracle`), but the needed fact is the
  path-level `replayPathResult_mem_support_replayFirstRun`, already a 1-line `have`.
