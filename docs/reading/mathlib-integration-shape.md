# Mathlib Integration Shape: Short and Long Term

> Status: design guidance, checked on 2026-10-03 against Lean and Mathlib `v4.35.0-rc3`. The usage
> counts in *Adoption decides bridge-versus-adopt* were taken on 2026-08-22, at `v4.33.0`, on the
> discrete surface that the measure migration retired.
>
> Scoping companion to
> [`denotational-probability-semantics.md`](denotational-probability-semantics.md). That document
> settles *what the semantic objects are*; this one asks what VCVio's probability statements should
> **look like** so that Mathlib's library applies to them, and so that the parts worth contributing
> are shaped to be contributable.

## Two directions, often confused

- **Inbound**: Mathlib's lemmas apply to our objects without a translation step. This is what makes
  `IndepFun`, monotone convergence, Tonelli, `rnDeriv`, and Ionescu–Tulcea usable at all.
- **Outbound**: the parts of our probability work that are not crypto-specific are stated in a form
  Mathlib could accept. The current design phase deliberately opens no upstream PRs, but shaping
  now is what makes that cheap later.

Inbound is the one with near-term payoff; outbound is nearly free if inbound is done in Mathlib's
vocabulary rather than a private one.

## What "Mathlib-shaped" concretely means

Checked against the pinned tree rather than assumed:

| Concept | Mathlib's form | Notes |
|---|---|---|
| Probability of an event | `μ s` | **There is no event-probability notation in Mathlib.** `Mathlib/Probability/Notation.lean` defines expectation, conditional expectation, `rnDeriv`, and `ℙ`, but events are plain measure application. |
| Expectation, real-valued | `P[X]`, `𝔼[X]` — both `∫ x, X x ∂P` | Bochner. Carries integrability side conditions. |
| Expectation, `ℝ≥0∞` | `∫⁻ x, f x ∂μ` | No notation; no integrability conditions. This is the right default for probabilities. |
| Conditional expectation / probability | `𝔼[X \| m]`, `P⟦s \| m⟧`, `condExp`, `cond` | |
| Independence | `IndepFun`, `iIndepFun` (plain and kernel forms) | |
| Sequencing | `Measure.bind`, notation `κ ∘ₘ μ`; `Kernel.comp`, `∘ₖ` | |
| Discrete distributions | `Measure.sum (fun x => w x • Measure.dirac x)` | The idiom named by the deprecation messages of mathlib4#42821, an open pull request that deprecates `PMF`. |
| Reaching a `tsum` | `lintegral_countable'`, `Measure.sum_apply` | `∫⁻ f ∂μ = ∑' a, f a * μ {a}` for countable, singleton-measurable `α`. |
| Divergences | `klDiv`, `Measure.rnDeriv`, `llr` | No Rényi and no total variation between measures. |

The last row is the load-bearing exception: total variation and Rényi are genuinely absent upstream,
so they stay ours — but stating them measure-first is what would make them contributable.

## Where VCVio stands against that

| VCVio | Mathlib-shaped counterpart | Status |
|---|---|---|
| `𝒟[mx]` | `Measure α` | **is** a Mathlib measure: the successful-output measure, whose missing mass is failure |
| `Pr{let y ← mx}[y = x]` | `𝒟[mx] {x}` | bridged: `prEvent_eq_evalDist_singleton`, under measurable singletons |
| `Pr{let x ← mx}[p x]` | `𝒟[mx] {x \| p x}` | bridged: `prEvent_eq_evalDist` for a measurable `p`; `prEvent_eq_evalDist_map` gives `𝒟[p <$> mx] {True}` with no measurable space on the outputs |
| `prFail mx` | `1 - 𝒟[mx] Set.univ`, or the mass at `none` of `evalDistWithFailure mx` | bridged: `prFail_eq_one_sub_evalDist_univ`, `evalDistWithFailure_none_eq_prFail` |
| `wp⟦mx⟧ g`, `𝔼{let x ← mx}[g x]` | `∫⁻ x, g x ∂𝒟[mx]` | bridged: `ExpectationWP.wp_eq_lintegral` for a measurable `g`; `ExpectationWP.wp_eq_lintegral_map` integrates the image measure `𝒟[g <$> mx]` and needs no measurable space on the outputs |
| `Fin.mOfFn`, `Fintype.mPi` (`EvalDist/IndepProductMeasure.lean`) | `Measure.pi`; `IndepFun` / `iIndepFun` w.r.t. the denotation | product measure: `evalDist_mOfFn`, `evalDist_mPi`; `IndepFun` is unused |
| `etvDist`, `tvDist` (`EvalDist/EvalDistTV.lean`) | a measure-level total variation | absent upstream; local `Measure.etvDist` and `Measure.tvDist` |
| `Divergence/Renyi.lean` | via `Measure.rnDeriv`, as `klDiv` is | absent upstream; local `InformationTheory.renyiDiv`, defined through `Measure.rnDeriv` |

An event is not literally a measure application. `Pr{…}[…]` is the expectation of the event's
indicator, core's `wp` under the measure interpretation `ExpectationWP`, so the program logic and
`vcgen` apply to it directly; the measure application is one rewrite away, and that rewrite needs
no measurable structure on the outputs. The remaining gap against the table of Mathlib's forms is
independence: independent products denote `Measure.pi`, but no statement is phrased with
`IndepFun`.

## Adoption decides bridge-versus-adopt

A surface that is barely used downstream does not need a compatibility bridge — it can simply
*become* the Mathlib object, with notation, a coercion, or a lift preserving the ergonomics. A
surface with a thousand call sites cannot. So the first question for each piece is not "what is the
Mathlib equivalent" but "how much is standing on it".

On 2026-08-22, across `VCVio/`, `ToMathlib/`, `Examples/`, `LatticeCrypto/`, `HashSig/` and
`VCVioTest/`, counting uses outside each definition's own file, the discrete surface measured as
follows. The verdicts are those of that day.

| Surface | Uses | Files outside its own | Verdict |
|---|---:|---:|---|
| `probOutput` (retired) | 1712 | 130 | **Bridge.** Keep the notation; move what it means underneath. |
| `probEvent` (retired) | 1425 | 98 | **Bridge**, but its *definition* can move off `PMF.toOuterMeasure` invisibly. |
| `tvDist` (the discrete one, retired) | 760 | 26 | **Bridge.** Far more adopted than it looks from the file count. |
| `probFailure` (retired) | 379 | 75 | **Bridge.** |
| `mOfFn` | 176 | 7 | Borderline — cost the `IndepFun` route before deciding. |
| `renyiDiv` | 79 | 2 | **Adopt directly.** Restate over `Measure.rnDeriv`, as `klDiv` is. |
| `expectedValue` (retired) | 69 | 3 | **Adopt directly.** Make it `∫⁻`, not a bridge to it. |
| `Fintype.mPi` | 15 | **0** | **Adopt directly, free.** Nothing outside its own file uses it. |

Two of these went against expectation, which is the argument for measuring rather than eyeballing:
`tvDist` was one of the most-depended-on surfaces in the layer despite living in a single file, and
`Fintype.mPi` had no downstream users at all.

The migration kept no bridge: every discrete statement in the table was restated on its measure
counterpart. Downstream code converts mechanically. The codemod
`scripts/migrate-native-probability.py` rewrites the discrete event notation `Pr[…]`, outputs and
failure included, into the notation of the previous section, and the
[migration guide](../agents/probability-migration.md) covers the rest. A codemod changes the
arithmetic of bridge-versus-adopt: a surface with many call sites but a regular shape can be
adopted directly.

## Short-term shape

The four short-term items proposed on 2026-08-22 are settled, the first two in a different form
than first proposed:

1. **Expectation is `∫⁻`.** An expectation is core `wp` under the measure interpretation,
   `wp⟦mx⟧ g`, and `ExpectationWP.wp_eq_lintegral` equates it with `∫⁻ x, g x ∂𝒟[mx]` for a
   measurable `g`. The interpretation exists for every monad with lawful measure semantics, so the
   trap the proposal recorded does not arise: redefining the retired `expectedValue` as an integral
   against the free-monad denotation would have narrowed it from every monad with a discrete
   semantics to free monads over a measure specification.
2. **Events need no outer measure.** The proposal kept the retired `probEvent` on an outer measure,
   because an event over a type without a measurable structure cannot be a `Measure` application.
   `prEvent_eq_evalDist_map` meets the same constraint differently: it pushes the predicate forward
   to `Prop`, whose measurable space Mathlib provides, and reads the event as `𝒟[p <$> mx] {True}`.
3. **The bridge set is closed.** `prEvent_eq_evalDist`, `prEvent_eq_evalDist_singleton` and
   `prFail_eq_one_sub_evalDist_univ` state events, outputs and failure as measure applications.
4. **Name measure-layer lemmas as Mathlib would.** `_apply`, `_apply_singleton`, `lintegral_`,
   `map_`, `bind_`, `_ae`. This stays the rule: cheap when a lemma is written, expensive to
   retrofit across a grown surface.

## Long-term shape

1. **`Pr{…}[…]` stays as surface notation over the measure semantics.** Users keep the
   crypto-legible notation, and Mathlib sees `μ s` after one rewrite (`prEvent_eq_evalDist_map`).
   The notation is the expectation of an indicator rather than a definitional skin over measure
   application, so the program logic and `vcgen` read it as a weakest precondition.
2. **Expectation is `∫⁻`**, with sums available as discrete corollaries rather than the primary
   form. Realized: `ExpectationWP.wp_eq_lintegral`.
3. **Independence is `IndepFun` on the denotation**, retiring the hand-rolled product lemmas and
   giving Bluebell's separating conjunction a definition instead of a construction. Open:
   independent products denote `Measure.pi`, but nothing is stated with `IndepFun`.
4. **Distances are stated measure-first** — total variation and Rényi over `Measure`, with discrete
   pointwise formulas as corollaries. This is the outbound-shaped part. Realized:
   `Measure.etvDist` and `InformationTheory.renyiDiv`; `etvDist` compares two computations event
   by event.
5. **Kernels carry anything state- or environment-indexed**, so `∘ₖ` composition and Mathlib's
   disintegration and trajectory machinery apply directly. The reader and state semantics are
   kernels (`readerTKernel`, `stateTKernel`); traces and termination remain open.

## The normalization question, answered

The obvious reading of "migrate normalization" is to flip the `tsum`-shaped simp set to
`lintegral`. The evidence does not support that, and it is worth saying why.

**Finite cryptographic goals genuinely want sums.** A Schwartz–Zippel bound, a collision count, a
uniform-cardinality argument — these are finite-sum statements, and a sum is the right form for
them. Rewriting them into `∫⁻` would make them worse, not more Mathlib-compatible, since Mathlib's
own discrete results are also stated as sums.

The library therefore keeps the measure form, `𝒟[mx] s` or `Pr{…}[…]`, as the normal form, with the
sums one explicit step below it and the integral as an intermediate (the
[normalization discipline](../agents/probability.md#normalization-discipline)):

- `simp` keeps `𝒟[mx] s` and `Pr{…}[…]` unless it reaches a closed form, such as a numeral or a
  count over a uniform draw;
- one rewrite reaches a finite or countable sum, mass-left (`prEvent_bind_eq_sum_fintype`,
  `prEvent_bind_eq_tsum_of_countable`);
- the integral `∫⁻ x, g x ∂𝒟[mx]`, reached by `prEvent_bind_eq_lintegral_of_discrete`, is an
  intermediate for Mathlib's integration API rather than a target.

Mathlib's toolkit is the objective for expectation, independence, divergence, and anything
continuous or infinite; the sums serve the finite goals.

## Sequencing

The short-term items are settled, and long-term items 1, 2 and 4 are realized. What remains is
independence as `IndepFun` (item 3) and the trace and termination semantics behind item 5, which
the [baseline's remaining work](denotational-probability-semantics.md#remaining-work) lists.
