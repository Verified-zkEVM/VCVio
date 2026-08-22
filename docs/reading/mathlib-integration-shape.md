# Mathlib Integration Shape: Short and Long Term

> Snapshot date: 2026-08-22. Toolchain `v4.33.0`, Mathlib `v4.33.0`.
>
> Scoping companion to `denotational-probability-semantics.md`, which lands with the
> measure-semantics work. That document settles *what the semantic objects are*; this one asks what VCVio's probability
> statements should **look like** so that Mathlib's library applies to them, and so that the parts
> worth contributing are shaped to be contributable.

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
| Discrete distributions | `Measure.sum (fun x => w x • Measure.dirac x)` | The idiom #42821's deprecation strings name. |
| Reaching a `tsum` | `lintegral_countable'`, `Measure.sum_apply` | `∫⁻ f ∂μ = ∑' a, f a * μ {a}` for countable, singleton-measurable `α`. |
| Divergences | `klDiv`, `Measure.rnDeriv`, `llr` | No Rényi and no total variation between measures. |

The last row is the load-bearing exception: total variation and Rényi are genuinely absent upstream,
so they stay ours — but stating them measure-first is what would make them contributable.

## Where VCVio stands against that

| VCVio today | Mathlib-shaped counterpart | Status |
|---|---|---|
| `Pr[= x \| mx]` | `denote mx {x}` | bridged — `FreeM.denote_apply_singleton` |
| `Pr[p \| mx]` | `denote mx {x \| p x}` | bridged — `FreeM.denote_apply_setOf` |
| `Pr[⊥ \| mx]` | mass at `none` in the total `Option` measure | partial — `Measure.dropNone` is the observer; no `probFailure` correspondence lemma |
| `expectedValue mx g` | `∫⁻ x, g x ∂(denote mx)` | **absent** |
| `probEvent` | measure application | **defined through `PMF.toOuterMeasure`** |
| `EvalDist/IndepProduct.lean` | `IndepFun` / `iIndepFun` w.r.t. the denotation | absent |
| `EvalDist/TVDist.lean` | a measure-level total variation | absent upstream and here |
| `EvalDist/RenyiDivergence.lean` | via `Measure.rnDeriv`, as `klDiv` is | absent |

Two of these are worth calling out as liabilities rather than gaps.

**There is no `lintegral` anywhere in `VCVio/EvalDist/`.** Against 555 `tsum` mentions and 190 `∑'`.
Expectation is exactly where Mathlib's analytic toolkit lives — monotone and dominated convergence,
Fatou, Tonelli, `lintegral_bind` — and none of it is currently reachable from a VCVio expectation.

**`probEvent` is defined by `PMF.toOuterMeasure`**, which mathlib4#42821 deprecates outright, with
103 `probEvent` lemmas standing on it. That is the single most dated definition in the layer, and it
sits at the centre of the API rather than the edge.

## Adoption decides bridge-versus-adopt

A surface that is barely used downstream does not need a compatibility bridge — it can simply
*become* the Mathlib object, with notation, a coercion, or a lift preserving the ergonomics. A
surface with a thousand call sites cannot. So the first question for each piece is not "what is the
Mathlib equivalent" but "how much is standing on it".

Measured across `VCVio/`, `ToMathlib/`, `Examples/`, `LatticeCrypto/`, `HashSig/`, `VCVioTest/`,
counting uses outside each definition's own file:

| Surface | Uses | Files outside its own | Verdict |
|---|---:|---:|---|
| `probOutput` | 1712 | 130 | **Bridge.** Keep the notation; move what it means underneath. |
| `probEvent` | 1425 | 98 | **Bridge**, but its *definition* can move off `PMF.toOuterMeasure` invisibly. |
| `tvDist` | 760 | 26 | **Bridge.** Far more adopted than it looks from the file count. |
| `probFailure` | 379 | 75 | **Bridge.** |
| `mOfFn` | 176 | 7 | Borderline — cost the `IndepFun` route before deciding. |
| `renyiDiv` | 79 | 2 | **Adopt directly.** Restate over `Measure.rnDeriv`, as `klDiv` is. |
| `expectedValue` | 69 | 3 | **Adopt directly.** Make it `∫⁻`, not a bridge to it. |
| `Fintype.mPi` | 15 | **0** | **Adopt directly, free.** Nothing outside its own file uses it. |

Two of these went against expectation, which is the argument for measuring rather than eyeballing:
`tvDist` is one of the most-depended-on surfaces in the layer despite living in a single file, and
`Fintype.mPi` has no downstream users at all.

## Short-term shape

Additive, no simp-normal-form changes, safe to land during the current cycle.

1. **Make `expectedValue` an `∫⁻`.** With 69 uses over three files it does not warrant a bridge —
   but the obvious form of the move is a trap worth recording. `expectedValue` is generic over
   `{m} [Monad m] [MonadLiftT m SPMF]`, whereas `FreeM.denote` needs
   `[∀ a, MeasurableSpace (P.B a)] [P.IsMeasureSpec]`. Redefining it as `∫⁻ x, g x ∂(denote mx)`
   would therefore **narrow it from any SPMF-lifting monad to free monads over a measure spec** —
   a regression, not a free adoption.

   The route at the *same* generality goes through the pieces that already exist:
   `SPMF.toPMF : SPMF α → PMF (Option α)`, then `PMF.toMeasure`, then `Measure.dropNone` to discard
   the failure mass. So the target is

   ```lean
   expectedValue mx g = ∫⁻ x, g x ∂(Measure.dropNone (evalDist mx).toPMF.toMeasure)
   ```

   under `[Countable α] [MeasurableSingletonClass α]`, with the existing
   `∑' x, Pr[= x | mx] * g x` form recovered as a `lintegral_countable'` corollary so the nine
   existing lemmas keep their statements. This is the only thing standing between VCVio expectations
   and Mathlib's convergence theory, and it gives `Measure.dropNone` a second consumer, which is
   independent support for keeping it.
2. **Move `probEvent` off the deprecated outer measure.** At minimum add
   `probEvent mx p = (evalDist mx).toMeasure …`; better, redefine it that way, since
   `toMeasure_apply_eq_toOuterMeasure_apply` makes the change propositionally invisible to the 103
   dependent lemmas.
3. **Close the `Pr` bridge set.** `probFailure` has no measure counterpart yet; the other two do.
   All three should be stateable as measure applications.
4. **Name new measure-layer lemmas as Mathlib would.** `_apply`, `_apply_singleton`, `lintegral_`,
   `map_`, `bind_`, `_ae`. Cheap now, expensive to retrofit across a grown surface.

## Long-term shape

1. **`Pr[…]` stays as surface notation and becomes a thin skin over measure application** — ideally
   definitional rather than propositional, so `simp` sees through it without a rewrite. Users keep
   the crypto-legible notation; Mathlib sees `μ s`.
2. **Expectation is `∫⁻`**, with `tsum` available as the discrete corollary rather than the primary
   form.
3. **Independence is `IndepFun` on the denotation**, retiring the hand-rolled product lemmas and
   giving Bluebell's separating conjunction a definition instead of a construction.
4. **Distances are stated measure-first** — total variation and Rényi over `Measure`, with discrete
   pointwise formulas as corollaries. This is the outbound-shaped part.
5. **Kernels carry anything state- or environment-indexed**, so `∘ₖ` composition and Mathlib's
   disintegration and trajectory machinery apply directly.

## The normalization question, answered

The obvious reading of "migrate normalization" is to flip the `tsum`-shaped simp set to
`lintegral`. The evidence does not support that, and it is worth saying why.

The 555 `tsum` mentions exist because **finite cryptographic goals genuinely want sums**. A
Schwartz–Zippel bound, a collision count, a uniform-cardinality argument — these are finite-sum
statements, and `∑'` is the right normal form for them. Rewriting them into `∫⁻` would make them
worse, not more Mathlib-compatible, since Mathlib's own discrete results are also stated as sums.

The useful move is not to replace the discrete normal form but to stop it being the *only* one:

- keep `tsum`/`Finset.sum` as the normal form for discrete goals;
- add the measure and `lintegral` forms as reachable, consistently-named alternatives;
- move a cluster only where Mathlib's toolkit is the actual objective — expectation, independence,
  divergence, and anything continuous or infinite.

So the simp-normal-form breakage budget should be **spent on the expectation and independence
clusters, not on `probOutput`**. `probOutput` is where the discrete form earns its keep.

## Sequencing

Short-term items 1–4 are independent and additive; none changes an existing statement. They are the
prerequisite for any later cluster flip, because a normal form cannot move to a target that does not
yet exist — which is the current situation for `lintegral`.

The long-term items depend on the backend decision holding and on the client sweep, and should not
start before the short-term bridges are in place and used at least once.
