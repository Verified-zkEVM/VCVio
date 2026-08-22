# Denotational Probability Semantics

> Status: accepted design baseline, 2026-08-21.
>
> This document records the decision reached from
> [`probability-semantics-landscape.md`](probability-semantics-landscape.md) and the executable
> evidence in [`measure-semantics-spike.md`](measure-semantics-spike.md). It is the default for new
> probability-semantics work and resolves the recommendations tracked in
> [VCVio issue #532](https://github.com/Verified-zkEVM/VCVio/issues/532); the landscape remains the
> evidence ledger.

## Decision

VCVio will use a stratified semantics rather than search for one carrier that imitates every
property of `SPMF`:

| Need | Canonical semantic object |
|---|---|
| Qualitative possible returns | PolyFun/Lean return-support and weakest-precondition interfaces |
| Closed, lossless computation | Mathlib `Measure α` plus `IsProbabilityMeasure` |
| Computation parameterized by environment or state | Mathlib `Kernel ρ α` / `Kernel σ (α × σ)` |
| Explicit option, exception, or writer effect | Total measure on `Option α`, `Except ε α`, or `α × ω` |
| Returned values of a possibly nonterminating computation | Subprobability `Measure α` obtained by discarding cutoff mass |
| Finite and infinite execution traces | Probability measure on paths, constructed from measurable kernels |
| Executable exact finite sampling | `FinRatPMF.Raw`; this is an implementation representation, not the denotation |
| Existing proof notation | `evalDist` and `Pr[...]` as a discrete compatibility façade |

Plain Mathlib measures and kernels are the semantic boundary. VCVio will not introduce a global
`Monad Measure`, nor wrap measures merely to make unrestricted Lean functions look measurable.
Where a missing general-purpose lemma or measurable-space instance is needed, it is staged in
`ToMathlib` for now.

## Public surfaces

### Free polynomial programs

[`VCVio/EvalDist/PFunctorMeasure.lean`](../../VCVio/EvalDist/PFunctorMeasure.lean) provides:

- `PFunctor.IsMeasureSpec`, assigning a probability measure to each operation's answer type;
- `PFunctor.FreeM.denote`, with `pure` interpreted by `Measure.dirac` and an operation interpreted
  by `Measure.bind`;
- an unconditional bind law for discrete operation answers;
- a one-operation continuous composition theorem whose measurability and probability hypotheses
  are explicit;
- `IsProbabilityMeasure` for every discrete-answer program;
- equality with the legacy PMF fold and bridges for singleton and measurable predicate events.

`IsProbabilitySpec` remains available during migration. Its induced `IsMeasureSpec` and the
agreement theorem are the compatibility route; new semantic definitions should accept
`IsMeasureSpec` when they do not inherently require point masses or enumeration.

### Monad transformer stacks

[`VCVio/EvalDist/MeasureSemantics.lean`](../../VCVio/EvalDist/MeasureSemantics.lean) packages a
lossless interpretation as `MeasureSemantics m`. Transformer semantics do not erase effects:

- `optionT` denotes the underlying `m (Option α)`;
- `exceptT` denotes the underlying `m (Except ε α)`;
- `writerT` denotes the underlying `m (α × ω)`;
- `readerTKernel` is a kernel from environments to results;
- `stateTKernel` is a kernel from initial states to result/final-state pairs.

This is deliberately not a family of global `MonadLiftT` instances. There is no canonical reader
environment or initial state, and flattening option/error immediately would choose a failure policy
before a proof asks for one. Proofs can observe the enriched measure with Mathlib events and maps;
`Measure.dropNone` is the explicit success-only observer.

### Possible nontermination

[`VCVio/EvalDist/ResumptionMeasure.lean`](../../VCVio/EvalDist/ResumptionMeasure.lean) gives a
PolyFun `Resumption` two finite-fuel observations and their returned-output limit:

- `truncateMeasure k computation : Measure (Option β)` is total; `none` means that no result was
  observed within the fuel budget;
- `outputMeasure k computation : Measure β` discards only that cutoff mass and has total mass at
  most one;
- `returnedMeasure computation : Measure β` is the monotone supremum of `outputMeasure` over all
  fuel bounds and has total mass at most one.

These definitions keep three events distinct: a returned `none`, a returned error, and not yet
returning. Any eventual limit semantics must preserve that distinction.

The infinite-trace layer is intentionally not fabricated from arbitrary `Resumption` values.
PolyFun resumptions are probability-free and their continuation functions are arbitrary Lean
functions. A trace law therefore needs a measurable presentation of the coalgebra: measurable
state and observation spaces, a Markov transition kernel, and compatible finite marginals. Once
that interface exists, Mathlib's Ionescu--Tulcea trajectory kernel or projective-limit machinery is
the intended construction.

## The measurability rule

The decisive boundary is simple:

- a function out of a discrete measurable space is automatically measurable;
- an arbitrary Lean continuation out of a continuous answer type is not;
- a `Kernel α β` is exactly a measurable function `α → Measure β` and therefore carries the proof
  needed for composition.

Consequently, VCVio promises ergonomic monadic equations for discrete programs and kernel-based
composition for continuous/state-indexed semantics. It does not promise a universal
`FreeM.denote_bind` theorem for continuous interfaces without a measurable-program invariant.

This is also why merely fixing the output type does not solve the coalgebraic problem. The state
transition itself must be measurable. Kernel construction sites expose that obligation, and the
resulting kernels compose using Mathlib's existing laws.

## Proof-facing compatibility

The migration is denotation-first, not notation-first:

1. Existing `Pr[...]`, support, finite-sum, and crypto theorem statements remain stable.
2. Correspondence lemmas reinterpret those theorems as facts about `Measure`.
3. New continuous, conditional, stateful, or process semantics use `Measure`/`Kernel` directly.
4. Discrete client lemmas migrate only when the measure-backed surface is at least as convenient.

The current gates cover a continuous Gaussian query and continuation, PMF/measure equality, an
arbitrary discrete measurable event, a one-time-pad theorem, effect-preserving transformers,
reader/state Markov kernels, and finite plus limit observations of a delayed resumption.

## Representation policy

New code follows these rules:

1. Use `Measure`, `ProbabilityMeasure`, and `Kernel` names from Mathlib in semantic statements.
2. Use `Measure.sum` and `Measure.dirac` for new discrete distributions unless an executable
   representation is the actual subject.
3. Keep `PMF` in compatibility adapters and existing discrete proofs while they migrate; do not
   build new foundational APIs around it.
4. Keep `FinRatPMF.Raw` for computation and prove that its denotation agrees with a measure.
5. Put missing general measurable-space instances and Mathlib-facing lemmas in `ToMathlib`.
6. Do not open Mathlib, Lean, or cslib contributions during this design migration. A
   probability-free improvement that belongs intrinsically to PolyFun may be proposed there, but
   VCVio-specific probability policy stays in VCVio.

[`scripts/check-pmf-boundary.sh`](../../scripts/check-pmf-boundary.sh) enforces a per-file ceiling
on direct bare-`PMF` coupling. Existing files may shrink their dependency; a new file starts with a
zero allowance. Updating the baseline is an explicit review action, not a routine response to CI.

## Local Mathlib-facing utilities

The initial `ToMathlib` surface is intentionally small:

- `PMF.toMeasure_bind`, the missing measure equality behind the compatibility proof;
- discrete measurable-space instances for `BitVec`;
- coproduct measurable spaces for `Option` and `Except`;
- `Measure.dropNone`, the success-only submeasure of an option-valued measure.

These declarations should track upstream naming and hypotheses closely so they can be deleted in
favour of upstream equivalents when those become available. No VCVio-specific oracle policy
belongs in this layer.

## Settled questions

- **Total outcome or subprobability result?** Both, at different observation layers: effects use a
  total outcome measure; success-only and termination observations use a submeasure.
- **Failure or divergence?** Returned failure is data. Divergence is missing output mass. Cutoff is
  an approximation marker, not either one.
- **Point distribution or measure-valued query specification?** Measure-valued is the general
  semantic capability. The pointwise PMF capability remains a discrete compatibility input.
- **Discrete measurable spaces?** Install concrete lawful instances, such as `BitVec`, and
  coproduct/product constructions. Do not install a blanket finite-type instance that could
  compete with Borel structures.
- **How does state compose?** As a kernel retaining final state, not by fixing an initial state and
  pretending that evaluation is a monad morphism.
- **Does proof notation change now?** No. `Pr[...]` remains, with measure correspondence theorems.
- **What owns infinite computation structure?** PolyFun owns probability-free resumptions,
  truncation, and coalgebra. VCVio supplies probabilistic readings; Mathlib supplies kernels and
  measure extension theorems.

## Remaining work

The following are implementation questions, not reasons to reopen the architecture:

1. prove the returned-measure fixpoint/continuity laws and formulate almost-sure termination;
2. formulate the smallest measurable-coalgebra interface that yields finite prefix kernels and an
   Ionescu--Tulcea trace law;
3. port expectation, independent-product, coupling, total-variation, and Rényi statements to
   measure-first foundations while retaining discrete corollaries;
4. connect indicator integrals and kernel composition to the evolving `Std.WP`/`vcgen` surface;
5. add denotation theorems from `FinRatPMF.Raw` to finite measures;
6. reassess local utilities at every Mathlib/PolyFun/cslib/toolchain update and delete them as soon
   as stable upstream surfaces subsume them.

Higher design churn is acceptable while completing these items. Compatibility is required at the
proof-facing boundary, not for internal representations that upstream is already steering away
from.
