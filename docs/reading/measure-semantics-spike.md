# Measure-Native Denotation: Spike Findings

> Snapshot date: 2026-08-21. Branch `dtumad/measure-semantics`, stacked on
> `dtumad/lean-4.33-module-boundary` (#521). Toolchain `v4.33.0`, Mathlib `v4.33.0`,
> PolyFun `v4.33.1`.
>
> Companion to [`probability-semantics-landscape.md`](probability-semantics-landscape.md).
> That document surveys the options; this one records what happened when one was built.

## What was built

Four files, 383 lines of Lean, purely additive — no existing declaration changed.

| File | Content |
|---|---|
| [`ToMathlib/MeasureTheory/DiscreteInstances.lean`](../../ToMathlib/MeasureTheory/DiscreteInstances.lean) | Discrete measurable-space instances for `BitVec n` |
| [`ToMathlib/Probability/ProbabilityMassFunction/Measure.lean`](../../ToMathlib/Probability/ProbabilityMassFunction/Measure.lean) | `PMF.toMeasure_bind` |
| [`VCVio/EvalDist/PFunctorMeasure.lean`](../../VCVio/EvalDist/PFunctorMeasure.lean) | `IsMeasureSpec`, `FreeM.denote`, the monad-morphism laws, agreement with the `PMF` denotation |
| [`VCVioTest/MeasureSemantics.lean`](../../VCVioTest/MeasureSemantics.lean) | The capability probe and the compatibility gate |

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
- **Upstream gaps.** Two, both small: `PMF.toMeasure_bind` (five lines; Mathlib has only the applied
  `toMeasure_bind_apply`) and the `BitVec` instances (three lines, in the exact style of
  `Mathlib.MeasureTheory.MeasurableSpace.Instances`). Both are ready-made contribution candidates.

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

## What this spike did *not* settle

- **`denote_bind` for continuous answer types.** The bind law needs the continuation measurable in
  two places, and discreteness of the answer type discharges one of them via
  `Measurable.of_discrete`. For a *continuous* answer type that obligation is a per-node condition
  which does not factor into a clean hypothesis. So a continuous oracle currently has a
  **denotation but not compositional reasoning**.

  This is the main open question, but it is a limitation of the **free-monad layer specifically**,
  and the coalgebraic layer looks like it sidesteps rather than inherits it. `Responder.lean`
  already describes a probabilistic responder as a Mealy machine in the Kleisli category of `SPMF`;
  with the Giry monad in that position it is a Markov kernel. `Handler`'s answer types are
  *dependent*, which `Kernel α β` cannot model, but a coalgebra's state space is fixed, so
  `ProbabilityTheory.Kernel` fits exactly — and it **bundles measurability into the structure**, so
  `Kernel.comp` carries no hypotheses and `IsMarkovKernel.comp` is an instance. Mathlib's
  `Kernel.traj` then supplies a measure on the infinite product, which is the trace measure
  `WiredRun`'s fuel bound exists to avoid needing.

  So the natural next spike is arguably `Kernel` under `Responder`/`DynSystem`, not continuous
  `bind` over `FreeM`.
- `IsProbabilityMeasure (denote program)` is not proved.
- Only the `probOutput` (singleton) correspondence exists; `probEvent` does not.
- The `tsum` versus `lintegral` simp-normal-form clash predicted in the survey has **not** been
  encountered, because nothing was converted. It remains a real risk for the client sweep and
  should not be treated as retired.

## Verdict

The ceiling lifts, and the compatibility surface survives. Both halves of the case hold, so the
conversion is worth scheduling — while noting that this increment converted no clients, and the
cost estimate above is drawn from one example, not from the 200 files that use `evalDist` or
`Pr[…]`.
