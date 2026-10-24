# Checkpoint: Foxglove ⇄ VCVio and the program-logic investigation

> Status: index of the work from 2026-10-22 to 2026-10-24, for anyone picking it up.
> Everything here is a spike. Nothing is meant to merge as is, and nothing is posted upstream
> without Devon's OK.

## Where the work is

### VCVio

All four branches stack, bottom to top. They are local to Devon's machine (worktree
`~/Documents/LeanCrypto/VCVio-spike`); see "Remote copies" below.

| Branch | Head | On top of | What |
|---|---|---|---|
| `chore/repin-polyfun-main` | `e6cceebae` | `main` (then) | Re-pins PolyFun and drops the declarations it owns. Merged upstream as #911 (squash `b9f70da16`). Kept as the base of the stack. |
| `spike/foxglove-bridge` | `adb6d5d43` | the re-pin | VCVio requires Foxglove (from the `dtumad/Foxglove` fork, branch `experimental/vcvio-free`). Non-default library `VCVioFoxglove`: interpretation, adequacy, expectations, specs, independence, `vcgen` routes, examples. Results log: `VCVioFoxglove/README.md`. |
| `spike/route-classifier` | `c12a882e3` | the bridge | A syntactic route key for program-logic goals, a `vcgen` front end sending explicit core triples to core `vcgen`, a census of the library, six core-first probes. Report: `docs/reading/program-logic-routing.md`, sections 1–5. |
| `spike/spec-library` | tip of this branch | the classifier | A ~430-declaration spec library (`VCVio/ProgramLogic/Library/`), the `derive_handler_specs` command, and the measured experiment (`scripts/spec_experiment/`). Report: section 6 of the routing report. This file. |

### Foxglove (fork `dtumad/Foxglove`)

| Branch | Head | On top of | What |
|---|---|---|---|
| `experimental/v4.35-bump` | `d3c00ab` | `main` | Bump to Lean v4.35.0. Draft PR NethermindEth/Foxglove#2. |
| `experimental/vcvio-measure-bridge` | `bef60aa` | the bump | Foxglove's semantics of `OracleComp` agrees with VCVio's. Draft PR NethermindEth/Foxglove#3. |
| `experimental/vcvio-measure-adequacy` | `97b963b` | the bridge | Adequacy: Foxglove laws are VCVio distributions. Draft PR NethermindEth/Foxglove#4. |
| `experimental/vcvio-free` | `3bd934b` | the bump | The dependency reversal: Foxglove without VCVio (requires cslib directly). `Split`, a VCVio-free `Adequacy` (`lawPMF`), `Rules/Derived`, `Rules/Independence`, the `⦃X, Q⦄` notation scoped. VCVio's `spike/foxglove-bridge` pins this commit. Draft PR dtumad/Foxglove#1 (within the fork). |
| `spike/wpv-lax-v435` | `e3308c9` | the adequacy branch | The value-level `wp` is a lax WP on convex postconditions. Draft PR dtumad/Foxglove#2 (within the fork). |

Local only and superseded: `dtumad/vcvio-bridge`, `dtumad/vcvio-adequacy` and `spike/wpv-lax`
(versions before the v4.35 bump); `dtumad/v4.35-repin` is `experimental/v4.35-bump`.

## The findings, in one place

1. **Dependency direction.** VCVio can require Foxglove, with Foxglove free of VCVio
   (`experimental/vcvio-free`); the bridge lives in VCVio's `VCVioFoxglove` library, and
   `scripts/check-foxglove-isolation.sh` keeps the rest of VCVio from importing it. For closed
   programs Foxglove adds proof rules, not expressiveness: the fair-bit lemma goes 27 → 1 line,
   DLog ⇒ CDH and the one-time pad gain nothing. `WP_SAMP` needs `[Countable α]`.
2. **Routing** (report sections 1–2). A route key reading only head constants (~85µs per goal)
   routes 47% of the census lines to a program logic. The `vcgen` front end fixes 8 errors and
   cuts `seededOracle_triple` from 4,176 to 813 heartbeats. The probes estimated 15–32% fewer
   routed lines.
3. **v4.36** (report section 3). A Foxglove-style `∗` rides core frames, blocked only by the
   unexposed `WP.Frames` side goal; core `vcgen` stops at `+`/`∑`; `+jp` is nightly-only.
   PolyFun and VCVio built on v4.36.0-rc1 with small patches (see "Lost" below).
4. **A large spec library does not pay** (report section 6). On a stratified random sample of
   20 routed theorems, re-proving with today's tools saves 44.0% of the frame's lines (75% of
   proof bodies); the T1+T2 library adds +1.2 points (90% CI +0.4 to +2.2); T3 and the deriver
   add nothing; the library costs more lines than it saves. What did help: the `simulateQ_nf`
   simp set, the handler `run_apply` lemmas, and the deriver for one-step equations (168 of 169
   scheme handlers covered).
5. **Upstream issues found.** iris-lean's global `notation "⊤"` (`Iris/Std/Classes.lean:22`)
   makes Mathlib's `⊤` ambiguous. Core: expose `WP.Frames`; a lattice-operation extension
   point; call-site spec arguments depending on earlier binders; `+jp` with resource
   preconditions; eta-reduced StateT preconditions break `vcgen`. VCVio: monad laws do not fire
   on cslib's direct `FreeM.instPure`/`instBind`; `rvcstep` and `rvcgen` defects (report
   section 2).

## Recommended next steps

From section 6 of the report, in order of measured payoff:
1. Re-prove the routed proofs with today's tools (about 10k lines).
2. Keep `simulateQ_nf` (with the missing members) and the handler `run_apply` lemmas; drop the
   rest of the spec library.
3. Fix the normal-form defects (`FreeM.instPure`, re-typed sum-spec answers, `impl q s` vs
   `.run` lemma shapes).
4. Adopt `derive_handler_specs` for one-step equations.
5. Add the few distribution-level lemmas the pilot asked for (union bound through maps,
   coupling bound through bind, discard rule, identical-until-bad for full runs, lazy versus
   eager random oracles).
6. Foxglove: open the bridge PR (the VCVio switch) stacked on a cleaned-up v4.35 update; raise
   the iris-lean `⊤` notation upstream; send the core requests.

## Reproducing

- **Library:** `lake build VCVio.ProgramLogic.Library` (T1+T2), the tier-3 modules under
  `VCVio/ProgramLogic/Library/T3/`, and `VCVio.ProgramLogic.Library.Derive`. Tests are in
  `VCVioTest/ProgramLogic/Library/`.
- **Experiment:** `scripts/spec_experiment/`.
  - `sample_routes.py` draws the sample (pilot: seed 20261023, `pilot.csv`).
  - `arm.py <ID> <ARM>` splices `arms/<ID>/<ARM>.lean` into a copy of the original file and
    records lines, tokens, heartbeats and library usage in `results.jsonl`.
  - `estimate.py --arms A,B` gives the estimates. It reads the census if present, else the
    committed `frame_strata.json`.
  - `arms/<ID>/notes*.md` record what each re-prover tried and what was missing.
- **Census:** `lake env lean scripts/RouteCensus.lean` writes `.lake/route-census.csv` (needs
  `VCVio`, `Examples`, `LatticeCrypto`, `HashSig`, `VCVioFoxglove` and `Foxglove` built).
- **Report:** `docs/reading/program-logic-routing.md`, and the same as a page in
  `docs/reading/program-logic-routing.html`.

## Lost

The v4.36 probes and patches lived in a session scratchpad that was cleared:
`v436/coreprobe` (core frames, `+jp`), `v436/mathprobe` (quantitative goals on Mathlib rc1),
`polyfun-rc1.diff` and `vcvio-rc1.diff`. Their findings are in section 3 of the report; the
port must be redone (mostly Mathlib's `Set` becoming a structure, PolyFun's `wpTrans` field
split, `epost` → `eposts`, `throws` as a keyword, test changes for `vcgen` splits, the
VCVioWidgets `Html` clash, an ML-DSA `decide` recursion depth; watch the `mkAppM
``wp_consequence_le`` calls in `Backward.lean`).

## Remote copies

- Foxglove: the five branches above are on `dtumad/Foxglove`. Draft PRs within the fork:
  https://github.com/dtumad/Foxglove/pull/1 (dependency reversal) and
  https://github.com/dtumad/Foxglove/pull/2 (lax WP). Upstream drafts:
  https://github.com/NethermindEth/Foxglove/pull/2, /3, /4.
- VCVio: not yet pushed; there is no `dtumad/VCVio` fork.
