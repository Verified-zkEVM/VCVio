# One program logic for VCVio: cheap routing over core `Std.WP`, VCVio and Foxglove

> Status: investigation record, 2026-10-23, on the local branch `spike/route-classifier`.
>
> - **Base:** VCVio `main` `f3df0ac18`, plus the PolyFun re-pin (#911) and the Foxglove bridge spike.
> - **Toolchains:** Lean `v4.35.0`, with probes on `v4.36.0-rc1` and `nightly-2026-10-23`.
> - **Code:**
>   - `VCVio/ProgramLogic/Tactics/Common/Route.lean`, `Tactics/Route.lean`;
>   - `scripts/RouteCensus.lean`;
>   - `VCVioTest/ProgramLogic/Route.lean`, `VCVioTest/ProgramLogic/Probes/`.

## Question

What is the most useful program logic VCVio can have, reusing core `Std.WP`/`vcgen` and the Foxglove separation logic as far as possible? Three sub-questions:
1. How do we pick, cheaply, which logic should handle a goal?
2. What will core give us on the v4.36 line?
3. How far can automation go at its best?

## Answer in brief

**`vcgen` stays the one entry point, behind a syntactic route key.** Each logic does what only it can do.

| Layer | What it handles |
|---|---|
| **Core `vcgen`** | the monadic skeleton: `pure`, `bind`, `if`/`match`, transformer layers, ∧/∃ splits, invariants and measures, exceptions, and (shown here) separation-logic frames |
| **VCVio** | averaging and quantitative steps (core stops at the first `+`, `*`, `∑` or `∑'`); the event readings (necessary, possible, lower, upper); relational logic; handler and bisimulation rules; oracle specs |
| **PolyFun** | exact WP laws and the `ExactWPMonad.dual` upper reading; a budget reading would serve query bounds |
| **Foxglove** | independence and conditioning, for the goals whose crux they are; its `∗` can ride core's frames |

**The route key.** It reads only head constants, at about 85µs per goal. With it:
- explicit core triples go to core `vcgen`;
- event goals go to their reading, following the reverted `prvcgen`'s table;
- relational goals go to `rvcgen`;
- equations between handler-run programs go to bisimulation rules;
- query bounds go to a budget reading;
- pair events also try Foxglove.

**Measured payoff.** Per family it ranges from about 0% to about 70% fewer lines. Over the routed part of the library, the estimate is 15–32% fewer lines, which is 7–15% of all proof lines. Heartbeats move 0.3–4.7×, depending on the family.

## 1. Routing

`Route.classify` reads a goal into a `RouteKey`:

| Field | What it records |
|---|---|
| judgment head | core or VCVio triple, `⊑ wp`, relational judgments, `=ᵈ`, query/cost bounds, Foxglove entailments, `=`/`≤`/`<`/`≠`; an equation at a monad type counts as an equation of programs |
| side kinds of a relation | event, measure, `wp`, expectation (`∑'`/`∫⁻`), coupling, total-variation distance, 0, 1, arithmetic |
| carrier | of a triple: ℝ≥0∞, `Prob`, Prop, order dual, state-passing |
| interpretation | the reading behind the triple's `WP` instance: core's generic instance applied to a reading, or a user's instance definition, followed two levels deep |
| monad and computation heads | — |
| premise bits | support membership, triples, query bounds |

**What it never does:** `find?`, `isDefEq`, or a speculative step. So it fixes the misroutes of the `find?`-based classifiers: a triple sitting in a premise, and `Prop`/`Prob` carriers treated as ℝ≥0∞.

**Cost** (census, 4,285 statements): p50 85µs, p99 270µs.

**Front end.** In front of `vcgen`, an explicit core triple with a known reading goes to core `vcgen` with its default configuration; every other goal falls through unchanged.
- **Misroutes fixed** (tests run with VCVio's tactics imported): `VCVioTest/ProgramLogic/CoreVCGen.lean` goes from 7 errors to 0, and `CoreWP.lean` from 1 to 0.
- **Speed:** `HandlerSpecs.seededOracle_triple` runs at core speed again, 4,176 → 813 heartbeats. VCVio's driver had been 5× core's there.
- **Overhead:** none measurable. Over 226 declarations in nine `vcgen`-heavy files, heartbeats are unchanged.
- **Diagnostics:** `vcvio.route.trace` and `route?` report a goal's route; `#guard_route` pins routes in tests.

**Census** (`scripts/RouteCensus.lean`). The scope is CryptoFoundations, Examples, LatticeCrypto, HashSig, Foxglove and the bridge: 4,285 theorems, 63.1k lines. 1,383 theorems (32%) route to a program logic, and they hold 30.0k lines (47%).

| Route | Decls | Lines |
|---|---|---|
| upper (`Pr ≤ ε`, `= 0`, `wp ≤`) | 92 | 5,683 |
| relational (game-hop equations, `=ᵈ`, couplings) | 128 | 5,308 |
| necessary (`= 1`, support premises) | 156 | 4,714 |
| program algebra (other program equations) | 356 | 4,471 |
| query and cost bounds | 155 | 2,452 |
| handler (equations through `simulateQ`) | 171 | 2,200 |
| Foxglove (Foxglove's own logic) | 181 | 2,198 |
| lower and upper (`Pr = c`) | 100 | 1,765 |
| up-to-bad (total variation) | 21 | 812 |
| lower / possible / core lower | 23 | 355 |
| Foxglove candidates among the above (pair events) | 49 | 2,782 |

What remains unrouted is mostly mathematics: encodings, lattice and polynomial algebra, data structures.

**What real proofs use today.** The 14 program-logic calls outside the showcase files are all `rvcgen`, `rvcstep` or `vcstep`. None is a bare `vcgen`.

**ArkLib** was not censused: its build is from an older toolchain. The earlier survey stands in: 454 `Pr{…}`, 43% of them single-draw counting; round-by-round proofs bound a fresh draw after fixing a prefix.

## 2. Probes: core-first re-proofs, one per family

Line counts include any new helper lemmas. Heartbeats are from `#count_heartbeats`, with the original proof copied into the same file.

| Probe | Route | Lines, old → new | Heartbeats, old → new |
|---|---|---|---|
| P1 Merkle batch-root support invariant (`BatchExtractability.lean:198`) | necessary + core `vcgen` | 93 → 37–44 (13–20 proof lines, plus a reusable triple) | 1,934 → 6.8–9.1k |
| P1′ its `verifyOpening` corollary | the same | 11 → 6 | 377 → 882 |
| P2 PRF-tag swap invariant (`Swap.lean:168`) | handler equation via a new bisimulation rule | 174 → 122 | 3,457 → 3,088 |
| P5a ElGamal sample reordering (`Basic.lean:117`) | relational | 14 → 13–15 | 2,002 → 2.6–3.9k |
| P5b ElGamal half lemma (`Basic.lean:153`) | relational with a same-type bijection | 122 → 35 | 20,022 → 5,947 |
| P4 three query bounds (Merkle, two HashSig) | budget reading + core `vcgen` (≈70 lines of infrastructure) | 11/9/29 → 7/5/27 | 444/2,716/4,566 → 1,501/1,016/13,059 |
| P3 a bad-event bound (`prEvent_cache_has_value_le_of_unique_preimage`) | upper reading + `simulateQ_triple_ranked` | 108 → 48 (and a hypothesis turned out unnecessary) | 5,200 → 9,792 |
| P6 a single fresh draw | upper reading | 4 → 5 (plus ≈45 lines of reading) | 1,646 → 969 |
| Fair-bit lemma (`evalDist_decide_eq_uniformBool_half`, earlier spike) | Foxglove independence | 27 → 1 (`vcgen`) or 5 by hand | 1,021 → 5,379 or 1,096 |

**Reading the probes:**
- **Invariant proofs:** core `vcgen` cuts them to one call per case. Each verification condition left is exactly the mathematical content, here cache logic. The cost moves into the first-order closer: `grind` is about 65% of P1's heartbeats.
- **Bijection game hops:** these gain the most. The trick is to choose the intermediate game so the coupling is a bijection on one type. Pure reordering hops gain almost nothing.
- **Upper bounds:** per-query union-bound inductions halve. Proofs that compose phase lemmas don't shrink until those lemmas are restated as potential triples indexed by the state. The P3 target, `prEvent_runCommitmentsThen_logged_le`, is one of these.
- **Query bounds:** modest gains. Most existing proofs are already short structural compositions.

**Missing pieces the probes found** (the library additions with measured payoff):
- **Handler specs:**
  - WP-form `@[spec high]` handler specs for the caching, seeded, logging and caching-logging oracles. The ghost-state forms leave unassignable metavariables.
  - Structural `simulateQ` specs (bind, pure, a query in `StateT`).
  - A whole-simulation monotone frame `⦃fun c ↦ ∀ a c', c ≤ c' → post a c'⦄ simulateQ cachingOracle oa ⦃post⦄`, for opaque adversary runs.
  - A bridge `support_of_triple_wp`.
- **Reducibility:** reducible wrapper definitions, or one-step equation lemmas (P1). Spec matching does not unfold wrappers.
- **Relational rules:**
  - the bisimulation equation `simulateQ_run_eq_of_impl_eq_on_inv`, proved in P2 in 7 lines;
  - a cross-type bijection coupling `relTriple_uniformSample_bij_cross`.
- **Bound readings:**
  - the upper reading, restored from `49f365a74` with small renames, together with `simulateQ_triple_ranked` and a `StateT` readback simp set (P3);
  - a budget reading for query bounds (P4).
- **Tactic defects:**
  - `rvcstep` crashes on a loose bound variable;
  - an untyped `using` hint is misread as a cut relation;
  - a `pure` leaf with a non-`EqRel` relation fails instead of leaving `R a b`;
  - `rvcgen` hits maximum recursion depth;
  - swaps have no side or depth selector;
  - the `vcstep?` planner spends 92k heartbeats on a congruence that can never close (P5).
- **Core bug:** an eta-reduced `StateT` precondition makes core `vcgen` fail ("failed to apply `Lean.Order.le_of_forall_le`") (P1). `vcvio.route.trace` now reports core's error when the front end falls back.

## 3. Upstream: what core gives on v4.36, and what it will not

**Frames carry a Foxglove-style `∗`** (`v436/coreprobe`, on v4.35.0, v4.36.0-rc1 and the 10-23 nightly).
- **Setup:** an opaque assertion type (upper sets), its own monad head, `withFrameClosure`, specs with concrete posts, and a roughly 75-line `@[frameproc]` that proves its own split condition.
- **Result:** with these, `⦃own 3⦄ (tick; tick; tick) ⦃⊤⦄` closes by plain `vcgen`. No `LatticeOp` entry is needed.
- **The one blocker:** the frame rule's `WP.Frames` side goal is not exposed in `FrameGoal`. The probe had to find it by searching the metavariable context.
- **Pitfall:** a schematic exception postcondition makes a spec count as conjunctive, so it skips the frameproc.

**`+jp`.** It works only on the nightly, where 64 verification conditions collapse to 1. It shares a jump only when the precondition there is `⊤`, so with resource preconditions nothing is shared. On v4.35 and rc1 it errors.

**Quantitative goals** (rc1 + Mathlib rc1, a `PMF` ℝ≥0∞ reading). Core `vcgen` handles `pure`/`bind`/`if`, meet/∧ splits and fixed-post specs. It stops at the first `+`, `*`, `∑` or `∑'`, which is every averaging step, and its lattice-operation table is closed. Equational `wp` laws (the `ExactWPMonad` shape) close what it leaves. So averaging stays VCVio's.

**Bump readiness.** Both PolyFun `ecac686` and VCVio build on v4.36.0-rc1 with small patches (`v436/polyfun-rc1.diff`, `v436/vcvio-rc1.diff`).
- **Most of the breakage is Mathlib's:** `Set` is now a structure.
- **The `Std.WP` changes:**
  - PolyFun `ExactWP.lean`'s `WP.wpTrans` is now a separate field, not definitionally `trans`;
  - binders were renamed `epost` → `eposts`, with no alias;
  - `throws` is now a keyword;
  - `vcgen` now splits ∧ and respects the goal's instance, which changes the leftover goals in a few tests.
- **Other breakage:** `VCVioWidgets` clashes with the new core `Lean.Html`.
- **A hidden risk:** `Tactics/Common/Backward.lean:290,431` build a deprecated name with `mkAppM`. That only fails at tactic run time, once the alias is removed.

**Requests to make upstream:**
1. Expose the `WP.Frames` side goal to frameprocs, or discharge it with `frames_of_frameClosure`.
2. An extension point for lattice operations or steps, so a library can step through `+`/`∑`.
3. Spec arguments at a call site that may depend on earlier binders (P6).
4. `+jp` sharing with resource-carrying preconditions.
5. The eta-reduced precondition bug.

## 4. How far can automation go

**At its best**, a goal whose leaves all have specifications closes in one call:
- the fair-bit lemma;
- the laws of uniform queries;
- Foxglove's Schwartz–Zippel, read as a VCVio `Pr` statement through definitional compilation.

**Below that, in tiers:**

| Tier | Families | What is left to the user | Measured |
|---|---|---|---|
| Invariants | handler, support | one `vcgen` per case, plus a first-order closer | ≈50% fewer lines, 3.5–4.7× heartbeats with `grind` |
| Bijection game hops | relational | a bijection hint, plus algebra | ≈70% fewer lines, 3× cheaper |
| Reordering hops | relational | swap guidance | ≈0–10% |
| Per-query bad-event bounds | upper | a potential | ≈55% fewer lines, 1.9× heartbeats |
| Query bounds | query/cost | arithmetic | 7–45% |
| Composition of phase bounds | upper | restating phases as potential triples | not measured |
| Forking and other nonlinear 2-safety | — | out of scope | — |

**Weighted over the census**, the estimate is 15–32% of the routed lines, about 4.5k–9.5k lines:

| Family | Estimated saving |
|---|---|
| necessary (4.7k lines) | 1.4–2.6k |
| upper (5.7k) | 1.1–2.8k |
| relational (5.3k) | 0.8–1.3k |
| handler (2.2k) | 0.7–1.0k |
| query bounds (2.5k) | 0.25–1.0k |
| Foxglove candidates (2.8k) | 0.3–0.8k |
| program algebra and the unprobed families | ≈0 |

This is consistent with #821's per-proof pilots (35–75%) once averaged across families.

## 5. Roadmap

1. **Land the route key, the diagnostics and the core-triple front end.** It is small, has no measured overhead, and fixes misroutes.
2. **Add the library rules with measured payoff** (section 2), then extend dispatch:
   - event goals to the readings;
   - handler equations to the bisimulation rule;
   - query bounds to the budget reading.
3. **Fix the relational tactic defects** listed in section 2.
4. **v4.36:** apply the rc1 patches when the release lands, and adopt `+jp` once it is in a release.
5. **Foxglove:**
   - Open the bridge PR (the VCVio switch), stacked on a cleaned-up v4.35 update, including Foxglove's notation scoping and the `Countable` generalization.
   - Then try Foxglove's `∗` on core frames: an opaque `FProp`-like carrier and a frameproc.
   - Raise iris-lean's global `⊤` notation upstream.
6. **Send the core requests** in section 3.
