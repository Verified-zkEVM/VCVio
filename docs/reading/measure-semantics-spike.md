# Measure-Native Denotation: Spike Findings

> Snapshot date: 2026-08-21. Toolchain `v4.33.0`, Mathlib `v4.33.0`, PolyFun `v4.33.1`.
>
> Companion to [`probability-semantics-landscape.md`](probability-semantics-landscape.md).
> That document surveys the options; this one records what happened when one was built. The
> resulting accepted design is
> [`denotational-probability-semantics.md`](denotational-probability-semantics.md).

## What was built

The spike is additive: existing probability declarations and crypto proofs remain unchanged.

| File | Content |
|---|---|
| [`ToMathlib/MeasureTheory/DiscreteInstances.lean`](../../ToMathlib/MeasureTheory/DiscreteInstances.lean) | Discrete measurable-space instances for `BitVec n` |
| [`ToMathlib/MeasureTheory/MeasurableSpace/Option.lean`](../../ToMathlib/MeasureTheory/MeasurableSpace/Option.lean) | Coproduct measurable space for `Option` |
| [`ToMathlib/MeasureTheory/MeasurableSpace/Except.lean`](../../ToMathlib/MeasureTheory/MeasurableSpace/Except.lean) | Coproduct measurable space for `Except` |
| [`ToMathlib/MeasureTheory/Measure/Option.lean`](../../ToMathlib/MeasureTheory/Measure/Option.lean) | Success-only `Measure.dropNone` observer |
| [`ToMathlib/Probability/ProbabilityMassFunction/Measure.lean`](../../ToMathlib/Probability/ProbabilityMassFunction/Measure.lean) | `PMF.toMeasure_bind` |
| [`VCVio/EvalDist/PFunctorMeasure.lean`](../../VCVio/EvalDist/PFunctorMeasure.lean) | `IsMeasureSpec`, `FreeM.denote`, discrete monad laws, probability preservation, event and PMF agreement |
| [`VCVio/EvalDist/MeasureSemantics.lean`](../../VCVio/EvalDist/MeasureSemantics.lean) | Effect-preserving transformer measures and reader/state Markov kernels |
| [`VCVio/EvalDist/ResumptionMeasure.lean`](../../VCVio/EvalDist/ResumptionMeasure.lean) | Total truncation measures and success-only output submeasures |
| [`VCVioTest/MeasureSemantics.lean`](../../VCVioTest/MeasureSemantics.lean) | Continuous, discrete, transformer, kernel, and resumption gates |

## The capability question: yes

`VCVioTest.MeasureSemantics.denote_gauss_lift` denotes an oracle whose answers are drawn from
`ProbabilityTheory.gaussianReal 0 1`. This cannot be written against `PFunctor.IsProbabilitySpec`
at all: that class carries a `Handler PMF P`, and `PMF.support_countable` is a theorem, so every
`PMF` is countably supported while a Gaussian is not.

The measure denotation of that program is *definitionally usable by Mathlib* — the follow-up
example applies it at an arbitrary set with no translation layer. That is the whole point of
choosing plain `Measure` over a wrapper.

## The compatibility question: yes, and cheaply

The one-time-pad ciphertext-uniformity result now has a `Measure`-valued statement whose proof is
the existing `Pr[…]` lemma applied directly:

```lean
example (sp : ℕ) (mgen : ProbComp (BitVec sp)) (σ : BitVec sp) :
    FreeM.denote ((oneTimePad sp).PerfectSecrecyCipherExp mgen) {σ}
      = (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  rw [denote_probComp_apply_singleton]
  exact oneTimePad.probOutput_cipher_uniform sp mgen σ
```

The transport goes through one theorem, `FreeM.denote_apply_singleton`, proved in four lines. No
crypto proof had to change, and none had to be reproved.

## Cost, measured

- **The fold.** `FreeM.liftM` is unusable, since it requires `[Monad m] [LawfulMonad m]` and
  `Measure` is not a monad. It is replaced by a three-line structural recursion over `pure` /
  `liftBind` — the same shape `instEvalDistCompatible` already inducts over. This was the cheapest
  part, not the most expensive.
- **Instance-indexing.** `denote` carries `[∀ a, MeasurableSpace (P.B a)]` and `[MeasurableSpace α]`;
  downstream statements add `[MeasurableSingletonClass α]` where they mention singletons. On the
  OTP gate this cost two binders on one helper theorem and zero extra proof steps, because
  `DiscreteInstances` supplies what `BitVec` was missing.
- **Local Mathlib-facing gaps.** `PMF.toMeasure_bind`, `BitVec` measurability, coproduct measurable
  spaces for `Option`/`Except`, and the option success submeasure are staged in `ToMathlib`. They
  deliberately stay local during the design phase and track Mathlib's idiom closely.

## Friction encountered

Recorded because a spike that reports only success is not evidence.

1. **Structural recursion needs `α` fixed in the motive.** Writing
   `{α} → [MeasurableSpace α] → FreeM P α → Measure α` makes Lean fall back to well-founded
   recursion and fail on `sizeOf (cont b) < sizeOf (lift a >>= cont)`. `α` does not change across
   the recursion, so binding it before the match fixes it.
2. **The induction alternative is `lift_bind`, not `liftBind`.**
3. **`P` is a metavariable wherever the program's type does not pin it**, so uses inside a `change`
   or a lambda need an explicit `(P := …)`.
4. **Interfaces must be `@[reducible]`.** Otherwise `P.B a` is stuck behind the `def` and Mathlib's
   instances for the underlying type never apply. The repo's own `unifSpec` is already
   `@[inline, reducible]`, so this matches existing practice.
5. **`(self := …)` does not work on anonymous instance binders.** The "induced measure spec"
   convenience therefore cannot be threaded positionally; `IsProbabilitySpec.toMeasureSpec` is a
   `def` to be introduced with `letI`, and the bridge lemmas take the agreement as a hypothesis.
6. **Rewriting into `denote` of a bind is fragile.** Stating both sides with `change` and letting
   defeq do the work is robust where `rw [denote_liftBind]` is not.
7. **`show` trips the style linter** when it changes the goal; `change` is the intended spelling.

## What this spike settled

- A discrete-answer `FreeM` denotation is a probability measure.
- Existing `Pr[...]` statements transport at both singleton and arbitrary measurable-event
  granularity.
- A continuous query can be followed by a measurable continuous continuation and remains a
  probability measure. The proof exposes exactly the hypothesis Mathlib's Giry bind requires.
- Option/error/writer effects should remain in total outcome measures; reader/state semantics are
  kernels rather than global transformer lifts.
- PolyFun truncations naturally provide total measures on `Option β`, while discarding cutoff mass
  gives increasing subprobability measures of returned values; their supremum is the fuel-free
  returned-output measure.

## What this spike did *not* settle

- **A universal continuous `FreeM` bind law.** The bind law needs a measurable family at every
  continuous answer node. Arbitrary Lean continuations do not provide that invariant. The accepted
  design therefore uses explicit one-step hypotheses and kernels instead of claiming an
  unrestricted law.
- **Infinite traces.** A fixed state carrier alone is insufficient: the coalgebra's transition must
  be measurable. `Kernel.traj` becomes applicable only after a measurable-coalgebra interface and
  compatible finite-prefix kernels are supplied.
- The returned-measure fixpoint equation and almost-sure termination API.
- The `tsum` versus `lintegral` simp-normal-form clash predicted in the survey has **not** been
  encountered, because nothing was converted. It remains a real risk for the client sweep and
  should not be treated as retired.

## Verdict

The ceiling lifts, the compatibility surface survives, and the transformer/nontermination split
has a concrete API. Measure and kernel semantics are therefore the baseline for new denotational
work. Existing clients remain on `Pr[...]` until correspondence lemmas make each migration at least
as usable as the current discrete proof.
