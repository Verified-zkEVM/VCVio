# Compile time of the core-WP program logic

**Status:** measurement record, 2026-10-02. Base: `main` at `f5119c64` (Lean and Mathlib
`v4.34.0`). Head: #821 at `720116af` (`v4.35.0-rc3`, after the follow-up checkpoints 1–7: the
readings, `prvcgen`, `prrw`, the pilots, the tests and the gallery). The question is whether the
program logic made the library slower to build, and where the time goes.

## Method

**Sequential single-module replays.** Each module is elaborated alone, one at a time on one
machine (an Apple Silicon laptop, 14 cores) with nothing else running, by
`/usr/bin/time -p lake env lean -Dprofiler=true -Dprofiler.threshold=100000 <file>` against a
completed build of its tree. The measure is CPU time (`user + sys`): a module's elaboration is
mostly single-threaded, so CPU time is stable across runs where wall time is not. The base replay
covers the 944 modules of both trees' libraries and the packages they compile (`PolyFun`,
`ProofWidgets`, `ToCslib`); the head replay covers the same 944 plus the 61 modules the head adds.
Two modules fail when elaborated alone in both trees and are counted with their partial times.

**Why not CI's timing report.** CI times each module as `Built <module> (<time>)` lines of a
parallel `lake build`, which is wall-clock under the load of the whole build on a shared runner.
On this pull request one CI comparison put `V:LatticeCrypto/MLKEM/Concrete/Encoding.lean` at
19 s → 33 s and the total at −45 %; the replays measure +14 % and −13.6 %. Per-module CI times
move by tens of percent between runs, so they point at a module to profile but do not decide
whether it regressed.

**Comparison.** Both replays are written as module tables in the format of
`V:scripts/module_times.py` and compared by `V:scripts/compare_module_times.py` at its defaults
(a module is over budget when it grows by more than 5 s and more than 50 %, the total when it
grows by more than 5 %), with `--gate`. The gate passes.

## Results

| Measure (944 modules in both trees) | Base | Head | Change |
|---|---:|---:|---:|
| CPU time | 2189 s | 1892 s | −13.6 % |
| tactic execution | 71 s | 49 s | −30 % |
| `simp` | 86 s | 62 s | −28 % |
| typeclass inference | 88 s | 65 s | −27 % |
| elaboration | 40 s | 35 s | −12 % |
| type checking | 27 s | 29 s | +6 % |
| `grind` | 11 s | 1 s | −90 % |
| interpretation | 415 s | 415 s | 0 % |

The median head-to-base ratio of a module's CPU time, over modules of at least 0.5 s, is 0.88 for
the 524 modules the head did not change and 0.86 for the 420 it did. Most of the gain is the
toolchain and Mathlib bump, which speeds up untouched modules as much; the modules the program
logic rewrote are no slower than that, and slightly faster.

No module grows by more than 1.1 s. The largest growths are small modules of the probability
layer that now carry the event notation and PolyFun's exact weakest preconditions, each by under
a second, mostly in interpretation: `V:VCVio/EvalDist/ProbabilityBounds.lean` (2.7 s → 3.5 s),
`V:VCVio/Interaction/UC/ReactiveSecurity.lean` (2.2 s → 2.9 s), PolyFun's
`P:PolyFun/Control/Do/Spec.lean` (1.2 s → 1.8 s, the transformer rules it absorbed) and
`V:VCVio/EvalDist/ProbabilityNotation.lean` (2.0 s → 2.6 s). The one larger growth outside them,
`V:LatticeCrypto/MLKEM/Concrete/Encoding.lean` (7.6 s → 8.7 s), is in a module the head does not
change and is mostly type checking.

The 61 modules the head adds cost 116 s of CPU time in all, against the 297 s saved on the modules
in both trees. The most expensive is the `prvcgen` test file `V:VCVioTest/ProgramLogic/PrVCGen.lean`
at 3.3 s; the reading tests, the gallery files and the new rule files are each between 1.9 s and
2.6 s, most of which is importing.

## Where the time goes

**Imports and interpretation dominate.** In the modules under `VCVio/`, importing takes 387 s of
wall time and interpretation 239 s of CPU time, more than typeclass inference, `simp`, tactic
execution and elaboration together (105 s). Interpretation is the execution of tactic and
elaborator code that is not compiled into Lean itself. It is unchanged between the trees (415 s
in both), so it predates this work; which interpreted code dominates it is not established here,
and a `-Dtrace.profiler=true` profile of a typical module is the next measurement.

**The heaviest single proofs predate the program logic.** They are
`experiment_eq` in `V:Examples/OneTimePad/Separated/Execution.lean:33`, whose `simp only` unfolds
a twenty-nine-step reactive network (7.0 s of `simp` at head, 8.0 s at base); the floating-point
certificates of `V:Extern/Falcon/FPR/Add.lean` (7.6 s of interpretation); and the encoding lemmas
of `V:LatticeCrypto/MLKEM/Concrete/Encoding.lean` (2.7 s of type checking). A declaration-level
profile at the checkpoint-0 head (`-Dprofiler.threshold=200` over the probability notation tests,
`V:VCVioTest/ProbabilityTactics.lean`, the `simulateQ` up-to-bad rules and the `prvcgen` tests)
found the event notation's elaborator and `prvcgen` under a second in every declaration; the only
second-scale step there was `simp [coinPadded]` at `V:VCVioTest/ProbabilityTactics.lean:327`
(1.3 s).

## Gating

CI's timing report gains a *Modules Over Budget* section from `V:scripts/compare_module_times.py`,
rendered by `V:scripts/build_timing_report.sh`, but it does not fail a run: with per-module noise
of tens of percent between runners, a failing per-module gate on CI's wall-clock times would trip
on modules that did not change, as `MLKEM/Concrete/Encoding.lean` would have. The script's
`--gate` is for comparable measurements, such as the two replays here.

## Reproducing

```bash
# In a built checkout of each tree, over a list of modules (one per line):
while read -r mod; do
  { /usr/bin/time -p lake env lean -Dprofiler=true -Dprofiler.threshold=100000 \
      "${mod//.//}.lean"; } > "replay/$mod.txt" 2>&1
done < modules.txt
# Collect `user + sys` per module into a table of module_times.py's format, then:
python3 scripts/compare_module_times.py base.json head.json --gate
```
