# VCVioFoxglove (spike): VCVio requires Foxglove

This is a local spike, not for merge as is. The dependency is reversed: Foxglove no longer requires VCVio (Foxglove branch `experimental/vcvio-free`), and VCVio's root `require`s Foxglove. The bridge to VCVio's semantics lives here, in a library that is not a default target.

`scripts/check-foxglove-isolation.sh` keeps every other library free of Foxglove and iris-lean.

## Contents

| Module | What |
|---|---|
| `Interp` | `BernoulliImpl` compiles `OracleComp` to coins by `simulateQ`. `LawfulBernoulliImpl` holds when each query has its answer measure; `unifSpec`, `coinSpec` and sums are lawful. `evalDist_interp : 𝒟[interp oa] = 𝒟[oa]`. |
| `Adequacy` | `wp_hasDistribution_iff` and its measure and `Pr{…}` forms: Foxglove laws are exactly VCVio's distributions. |
| `Expectation` | Foxglove laws compute VCVio's `Std.WP` expectation reading. |
| `Specs` | Leaf laws of `$ᵗ α`, `unifSpec.query`, and a program's own tape law. |
| `Independence` | For pair-valued programs, `(fst ∘ X) ~ μ ∗ (snd ∘ X) ~ ν` gives the product measure, products of events, and a guessing bound. |
| `Tactic` | Foxglove routes for VCVio's own `vcgen` (below). |
| `Examples/UniformBit` | `evalDist_decide_eq_uniformBool_half`, by independence. |

The test library `VCVioFoxgloveTest` holds:
- the closure and instance canaries;
- the goal corpus;
- the root test and Schwartz–Zippel as VCVio statements.

## One tactic: `vcgen`

There is no new tactic name. `VCVioFoxglove.Tactic` adds an elaborator for VCVio's `vcgen` syntax kind. Lean tries a kind's elaborators in turn, so this one runs first, and gives way (`throwUnsupportedSyntax`) to VCVio's `vcgen`, and through it to core's, on every goal it does not handle.

- **Foxglove goals** (`⊢ wp oa ⦃X, …⦄`) are decomposed by Foxglove's rules, applied as lemmas: leaf laws, a sample with an independent sampler, independent post-processing. Whatever is left goes to VCVio's `vcgen`.
- **VCVio event goals** that independence decides go through Foxglove all-or-nothing: unless the routes alone close the goal, the state is restored. These goals are:
  - a decided event of two draws;
  - a guess of a uniform draw;
  - a conjunction of independent events;
  - a product output measure.
- **Other goals** fail a syntactic pre-check and skip the routes.

## Spike log (2026-10-23)

**Showcase.**

| Target | Before | After |
|---|---|---|
| `evalDist_decide_eq_uniformBool_half` | 27 proof lines (1,021 heartbeats) | 5 lines by hand (1,096), or 1 line `vcgen` (5,379) |
| Root test, VCVio `Pr` statement | — | 2 lines from Foxglove's coin-program theorem (`interp_rootTest` is `rfl`) |
| Schwartz–Zippel, VCVio `Pr` statement | — | about 8 lines, the same way |

VCVio's `vcgen`/`vcstep` alone leave an integral on the fair-bit lemma.

**Corpus.** 16 goals, each closed by a bare `vcgen`: leaf laws, independence, events, delegated goals, and negatives on a dependent pair. The negatives' Foxglove attempt is rolled back.

**Subsumption.** Twelve files use `vcgen`/`vcstep`, each recompiled with this module imported:
- 9 are unchanged;
- `CoreVCGen` and `CoreWP` fail the same way with only `VCVio.ProgramLogic.Tactics` imported, because they test core `vcgen`;
- `ProbabilityTactics` fails because of iris-lean's global `⊤` notation (below).

**Heartbeats.** Over 148 declarations: total 1.064×, median 1.006, p90 1.14. The worst case, 5.3×, is VCVio's `vcgen` replacing core's on `seededOracle_triple`; the routes add about 0 there.

**Build gates.**

| Gate | Result |
|---|---|
| B1 cold cost | iris-lean 170 modules, 329 s summed; Foxglove 25 modules, 78 s; bridge 4 modules, 6 s; 1:56 wall on 14 cores |
| B2 full CI wall time | not measured (local only) |
| B3 downstream fetch | about 1.8 MB (iris-lean) + 4.4 MB (Foxglove) of git objects |
| B4 import floor | +0.2–0.3 s |
| B5 closure | the canary passes |
| B6 per proof | passes for the hand-written fair-bit proof; the one-line `vcgen` version is about 5× |
| B7 per module | under 2 s, zero warnings |

**Findings.**
1. **Foxglove's postcondition notation.** Unscoped, `⦃X, Q⦄` captured core's `⦃P⦄ x ⦃Q⦄` triple notation in every file importing Foxglove. It is now scoped (Foxglove `3bd934b`).
2. **iris-lean's `⊤`.** `Iris/Std/Classes.lean:22` declares a global `notation "⊤" => top`, which makes Mathlib's `⊤` ambiguous without an expected type. This is upstream.
3. **`WP_SAMP` needs `Countable`.** It requires `[Countable α]` on the result type, so laws of programs returning arbitrary adversary states are out of reach. Coin programs are finite trees, so a finite-support proof should remove the requirement.
4. **The convex fragment as a core `Std.WP` instance was not built.** For closed programs it proves only support facts, and the natural sampling specification `⦃𝒞⟨μ⟩ v; Q v⦄` is unsound.
5. **For closed programs, independence is a product-law equation.** Foxglove contributes proof rules, not expressiveness:
   - `wp_bind_sep_bind` is proved by law algebra;
   - DLog ⇒ CDH and the one-time-pad lemma gain nothing;
   - ElGamal's gain is the fair-bit lemma it already uses.
