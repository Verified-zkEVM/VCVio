# Query Tracking and Cost Semantics

This guide explains the query-tracking stack in `VCVio/OracleComp/QueryTracking/`.

The current design is intentionally **weighted-first**:

- `QueryCost[...]` and `ExpectedQueryCost[...]` are the primary notions.
- `Queries[...]` and `ExpectedQueries[...]` are the unit-cost specializations.

The stack is also intentionally split into:

- a writer-cost layer for pathwise and expected-cost facts
- a generic `HasQuery.Program` accounting layer, evaluated against `QueryImpl`
- a thin `OracleComp` facade
- a small `ToMathlib` probability layer for reusable tail-sum facts

The structural instrumentation owners are `Tracing.Core`, `CountingOracle.Core`, and
`LoggingOracle.Core`. Query bounds, cache/programming handlers, and enforcement import native
handler machinery; their structural laws need no probability specification. The older tracing,
counting, and logging module paths additionally export their remaining scalar compatibility
corollaries. Prefer the native owners or `VCVio.Native` for new proofs.

Enforcement event laws use `Pr{...}[...]` and a chosen `IsMeasureSpec`, with discrete query-answer
spaces to interpret arbitrary oracle continuations. They do not require uniform sampling or
discrete result, budget, or state spaces.

`AdaptivePrefix.lean` is separate from the cost semantics above. It owns the probabilistic
stopping-time argument used when an adaptive prefix and a transcript-dependent suffix share one
lazy random function. Protocol-specific files should instantiate this theorem rather than copy its
cache/log induction.

`measure_adaptivePrefixRunFrom_le` proves this bound for any lawful measure semantics with
uniform query measures and a measurable terminal event. Its proof uses a bad-event decomposition
of a Lebesgue integral. The original `probEvent_adaptivePrefixRunFrom_le` is a compatibility
corollary. The online-target counterpart is
`MerkleTreeMultiExtractability.measure_onlineAdaptivePrefixRunFrom_logged_le`; its target set
is evaluated on the pre-query log.

The structural `QueryCache.log_consistent_append`, `log_consistent_cacheQuery_append`,
`cache_covered_append`, `cache_covered_cacheQuery_append`, and `domain_bound_cacheQuery` lemmas
in `CachingLoggingOracle.lean` transport cache/log hypotheses without probability assumptions
or decidable equality on responses.

## Per-index counting

`QueryCount ι` is an ordinary function `ι → ℕ`, with the standard pointwise instances.
`QueryImpl.withCounting` and `countingOracle` use `AddWriterT (QueryCount ι)`.
Use `.runAdd : m (α × QueryCount ι)` to observe counts; raw `.run` exposes the writer's
`Multiplicative` tag. `countingOracle.simulate` retains its ordinary-count result and initial offset.
Writer WP predicates inspect `Multiplicative.toAdd` when using the generic monoid bridge.

A count is emitted before the handler, but failure in the base monad can discard the complete
writer result. `WriterT ω Option` loses the log on `none`; `OptionT (WriterT ω Id)` can retain
a log together with `none`. `VCVioTest/ModuleAPI/Counting.lean` checks both orders, repeated
labels, unchanged answers, and the ordinary function monoid.

## Main Files

| File | Role |
|------|------|
| `VCVio/OracleComp/QueryTracking/WriterCost.lean` | `AddWriterT` cost facts and `QueryImpl` writer-cost instrumentation |
| `VCVio/OracleComp/QueryTracking/QueryCost.lean` | Generic query-cost accounting for direct-style `HasQuery.Program` computations |
| `VCVio/OracleComp/QueryTracking/CostModel.lean` | `OracleComp`-specific facade over the generic semantics |
| `VCVio/OracleComp/QueryTracking/AdaptivePrefix.lean` | Shared-ROM stopping-time bounds for an adaptive prefix followed by a transcript-dependent suffix |
| `ToMathlib/Control/WriterT.lean` | Pathwise and output-indexed cost predicates for `AddWriterT` |
| `ToMathlib/Probability/TailSums.lean` | Tail-sum integration for measurable Nat observables under arbitrary measures |

## Association-list cache representation

`ListCache.lean` supplies `QueryImpl.ListCache.handler` for an executable association-list
cache. It uses `List.lookup`, so the first occurrence of a key wins even when the initial
list contains duplicates. Hits do not run the underlying draw; misses prepend one binding.
`local_projection` preserves the reply and decoded cache after each query, and
`adaptive_projection` lifts that equality through every adaptive client in any lawful monad.

`Examples/PRFTagReader/CacheRepresentation.lean` closes the named PRF reductions with this
handler and retains their bad-event state through `QueryImpl.extendState`. Its
`PRFTagReader.CachedPRF.preserved_bound` proves the same three-loss bound for the bounded FIFO
experiment, from empty list caches. The equality concerns replies and retained state; it makes
no running-time claim about association-list lookup or the network schedule.

## Input Routing and Domain Separation

[`RandomOracle/Routing.lean`](../../VCVio/OracleComp/QueryTracking/RandomOracle/Routing.lean)
proves that injective input encodings preserve the full output measure of every adaptive
client of an initially empty finite random oracle. The eager-table and lazy-cache forms
share the same structural routing operation. Disjoint injective encodings of two domains
use Mathlib's `Function.Injective.sumElim` to discharge the routing condition.

[`Examples/ProgramLogic/RandomOracleRouting.lean`](../../Examples/ProgramLogic/RandomOracleRouting.lean)
shows why the condition matters: comparing distinct Boolean cells accepts with probability
`1/2`, whereas routing both inputs to one target cell accepts with probability `1`.
The ordinary-import tests in
[`VCVioTest/RandomOracleRouting.lean`](../../VCVioTest/RandomOracleRouting.lean)
also cover adaptive and repeated queries, disjoint domains, and structural routing in `Type 1`.
The measure laws use the existing table-sampling API in `Type 0`; arbitrary preloaded caches
require their own consistency condition.

## Instrumentation Pattern: `preInsert` / `postInsert`

Almost every `QueryImpl` wrapper in this directory ultimately bottoms out at the
`preInsert` / `postInsert` combinators in
`VCVio/OracleComp/SimSemantics/QueryImpl/Constructions.lean`:

```
preInsert / postInsert  (generic combinators + bridge theory)
  withTraceBefore / withTrace                         (Tracing.lean)
    withCost                                          (CountingOracle.lean)
      withCounting                                    (CountingOracle.lean)
      withAddCost / withUnitCost                      (WriterCost.lean)
    withTraceAppendBefore / withTraceAppend           (Tracing.lean)
      withLogging                                     (LoggingOracle.lean)
      appendInputLog                                  (LoggingOracle.lean)
```

Read this top-down before adding a new instrumentation wrapper. The rule of thumb:

- **If the wrapper's shape is "for each query, accumulate a value, then delegate"**, define it as a one-liner over `withTraceBefore` / `withCost` (i.e. through `preInsert`).
- **If it's "delegate, then record query+response"**, route it through `withTrace` / `withTraceAppend` / `withLogging` (i.e. through `postInsert`).
- **If the wrapper genuinely needs to inspect external state to decide whether or not to query** (cache-on-hit, seed fallback, budget gate, bad-event gating), write a custom `QueryImpl` — `preInsert` / `postInsert` cannot express this. Existing examples: `withCaching` (`CachingOracle.lean`), `withPregen` (`SeededOracle.lean`), `enforceOracle` (`Enforcement.lean`).

Defining the wrapper through this chain provides structural projection and support equations,
including `proj_simulateQ_*` and `support_proj_simulateQ_*`, plus query-bound transfer. These
equations preserve any observation of the projected program, including its chosen-space measure.
Older facade modules also export their remaining scalar compatibility corollaries.

See `docs/agents/oracle-comp.md` for the full table of combinators and the underlying theory.

## Layering

### 1. `AddWriterT`: raw cost semantics

The semantic core is a writer monad whose log records cost.

At this level, the key notions are:

- `AddWriterT.PathwiseCostAtMost`
- `AddWriterT.PathwiseCostAtLeast`
- `Cost[ oa ] = w`
- `Cost[ oa ] ≤ w`
- `Cost[ oa ] ≥ w`

These are **pathwise** statements: they talk about every reachable execution path.

This file also defines the stronger, output-indexed notion:

- `AddWriterT.CostsAs oa f`

This means:

- the cost of `oa` is completely determined by its output
- there is a function `f` such that every reachable run producing `a` has cost `f a`

That is stronger than a pathwise bound. It is useful when exact cost is determined by the final
result, but it is not the default semantic notion.

### 2. `QueryCost`: generic `HasQuery.Program` accounting

`HasQuery.Program spec m α` is the direct-style shape
`[HasQuery spec m] → m α`. This layer evaluates such programs against a
concrete `impl : QueryImpl spec m`, or against the writer-instrumented
implementations `impl.withAddCost` and `impl.withUnitCost`.

It exposes the public API:

- exact weighted cost:
  `QueryCost[ oa in runtime by costFn ] = w`
- weighted upper/lower bounds:
  `QueryCost[ oa in runtime by costFn ] ≤ w`
  `QueryCost[ oa in runtime by costFn ] ≥ w`
- exact / bounded unit-cost query counting:
  `Queries[ oa in runtime ] = n`
  `Queries[ oa in runtime ] ≤ n`
  `Queries[ oa in runtime ] ≥ n`
- expected weighted cost:
  `ExpectedQueryCost[ oa in runtime by costFn via val ]`
- expected unit-cost query count:
  `ExpectedQueries[ oa in runtime ]`

The intended reading is:

- `QueryCost[...]` is the general notion
- `Queries[...]` means the same thing with `costFn := fun _ ↦ 1`

### 3. `CostModel`: `OracleComp` facade

`CostModel.lean` should be read as a free-`OracleComp` view of the same semantics, not as a
second independent cost semantics.

The important design point is:

- `QueryImpl`, `HasQuery.Program`, and `AddWriterT` are the semantic core
- `CostModel` is now a thin facade for `OracleComp`-specific theorems and asymptotic packaging

Use `CostModel` when you want:

- the free-oracle viewpoint
- `OracleComp`-specific reductions
- the older asymptotic query-cost packaging

Use `QueryCost` when you want:

- a generic theorem over a direct-style `HasQuery.Program`
- runtime-instantiated cryptographic constructions
- weighted expected cost and expected query count

### 4. `ToMathlib`: generic probability facts

Expected-cost proofs should avoid hard-coding query semantics when the real theorem is purely
probabilistic.

`ToMathlib/Probability/TailSums.lean` contains the measure-theoretic tail-sum identity for
measurable Nat observables under arbitrary measures. The query-cost layer specializes it:

- `E[T] = ∑ Pr[i < T]`
- tail domination implies expectation domination

WriterCost, QueryCost, and CostModel respect the chosen cost measurable space and share the
same cost-marginal integral. `CostsAs` gives an output integral under a measurable cost function
and valuation; countable output sums need actual countability and measurable singletons.
Pathwise expectation bounds need a measurable valuation. Upper bounds permit failure; lower
and exact bounds use Mathlib `IsProbabilityMeasure` on the cost marginal. Exact cost needs no
order or monotone valuation. `expectedCost_eq_mul_costMass_of_hasCost` also needs no attachment
and retains successful mass for computations that can fail; the support-based variant handles
valuations constant on reachable costs. Markov bounds observe only the cost marginal. Discarded outputs need no measurable space.

Measurably parameterized cost measures are families accepted by `evalDistKernel`.
`AddWriterT.measurable_expectedCost` certifies their measurable expected valuations. Algebraic
writer tags carry their underlying measurable space through
`ToMathlib/MeasureTheory/MeasurableSpace/TypeTags.lean`.

## Three Cost Notions

There are three distinct notions in the current API.

### Pathwise cost

Use this when the statement is about **all runs**.

Examples:

- encryption uses at most one query
- decryption uses at least zero queries
- signing uses at most `ρ * |Ω|` queries

This is the natural meaning of:

- `QueryCost[...] ≤ w`
- `Queries[...] ≤ n`

### Output-indexed cost

Use this when cost is determined by the final output.

Examples:

- a single Fiat-Shamir signing attempt queries exactly the returned commitment
- a verification procedure always makes a fixed number of queries determined by its output shape

This is expressed by:

- `UsesCostAs`
- `CostsAs`

and is mainly useful as a bridge to exact expected-cost formulas.

### Expected cost

Use this when cost is random and pathwise exact equalities are not the right public theorem.

Examples:

- Fischlin signing has expected query count at most `ρ * |Ω|`
- Fiat-Shamir-with-aborts signing has expected query count equal to a tail sum

This is expressed by:

- `ExpectedQueryCost[...]`
- `ExpectedQueries[...]`

## When To Prove Which Theorem

### Prove exact pathwise cost

Use an exact pathwise theorem when every run really has the same cost.

Examples:

- `FiatShamir.verify` uses exactly one query
- `TTransform.encrypt` uses exactly one query
- `Fischlin.verify` uses exactly `ρ` queries

### Prove `UsesCostAs`

Use `UsesCostAs` when cost is a function of the output, and you want an expectation theorem of the
form “expected cost is the expectation of `val ∘ f` over outputs.”

Example:

- one `FiatShamirWithAbort` signing attempt

Do **not** force this notion onto retry loops or search procedures whose cost is not determined by
the final output.

### Prove a pathwise upper bound

Use a pathwise upper bound when branching or retrying changes the cost across runs.

Examples:

- `TTransform.decrypt` uses at most one query
- `FiatShamirWithAbort.sign` uses at most `maxAttempts` queries
- Fischlin signing uses at most `ρ * |Ω|` queries

These are the right first theorems for search loops, aborting schemes, and stopping-time style
computations.

### Prove expectation via a bridge

After a pathwise bound or a `UsesCostAs` theorem is in place, derive expectation theorems using the
generic bridge lemmas in `QueryCost.lean`.

There are two main patterns:

- `UsesCostAs` gives an exact output-expectation formula
- pathwise bounds give expectation upper/lower bounds

For natural-valued costs, the tail-sum lemmas give sharper expectation theorems.

## Notation Guide

### Weighted cost

```lean
QueryCost[ oa in runtime by costFn ] = w
QueryCost[ oa in runtime by costFn ] ≤ w
QueryCost[ oa in runtime by costFn ] ≥ w
```

### Unit-cost query counting

```lean
Queries[ oa in runtime ] = n
Queries[ oa in runtime ] ≤ n
Queries[ oa in runtime ] ≥ n
```

These are just the weighted statements specialized to `fun _ ↦ 1`.

### Expected weighted cost

```lean
ExpectedQueryCost[ oa in runtime by costFn via val ]
```

The `val` parameter interprets the weighted cost in `ENNReal`. For unit-count expectations, use:

```lean
ExpectedQueries[ oa in runtime ]
```

## Worked Examples

### Weakening a cost bound

Import `Mathlib.Tactic.GRewrite` to rewrite through `AddWriterT.PathwiseCostAtMost` and
`AddWriterT.QueryBoundedAboveBy`. Given `h : a ≤ b`, `grw [h] at hcost` weakens a certificate
with upper bound `a` to one with upper bound `b`. On a goal with upper bound `b`, use
`grw [← h]` to reduce it to the stronger obligation with upper bound `a`. The computation
stays fixed; these are implication rules, so `gcongr` also handles an implication between
the two cost predicates.

`Fischlin/CostAccounting.lean` uses this for early returns and a weighted query charge;
`OracleComp/QueryTracking/CostModel.lean` uses it for the pure branch of the total-query bound.
The rule also applies to function-valued cost vectors: `gcongr` leaves the pointwise order goal,
which can be supplied with `exact h`. Normalize equal bounds with `simpa only` when no weakening
is needed.
Lower-bound registrations remain local experiments; use `pathwiseCostAtLeast_mono` or
`queryBoundedBelowBy_mono` explicitly. The
[generalized-relation investigation](../reading/generalized-relation-automation.md) records the
tests and the promotion criteria for additional rules.

### Fiat-Shamir

See `VCVio/CryptoFoundations/FiatShamir/Sigma.lean`.

This is the clean “exact one query” example.

- signing and verification support exact unit-cost statements
- the single-query cost is also a good example of `UsesCostAs`

### Fischlin

See the modules under `VCVio/CryptoFoundations/Fischlin/` (`CostAccounting.lean` for the cost side).

This is the first substantial bounded-cost example.

- verification uses exactly `ρ` queries
- signing uses at most `ρ * |Ω|`
- the weighted theorem layer generalizes the unit-cost one

This file is the best reference for:

- weighted pathwise upper bounds
- expected weighted cost from pathwise bounds

### T-transform and U-transform

See:

- `VCVio/CryptoFoundations/FujisakiOkamoto/TTransform.lean`
- `VCVio/CryptoFoundations/FujisakiOkamoto/UTransform.lean`

These illustrate:

- exact cost theorems for simple FO-style constructions
- upper bounds for branch-sensitive decryption
- weighted multi-query accounting

### Fiat-Shamir with aborts

See:

- `VCVio/CryptoFoundations/FiatShamir/WithAbort/Cost.lean`
- `VCVio/CryptoFoundations/FiatShamir/WithAbort/ExpectedCost.lean`

This is the main stopping-time example.

The key progression is:

1. one attempt has output-determined cost
2. the full retry loop has only a pathwise upper bound
3. expected query count is expressed by a tail sum
4. the tail sum is rewritten semantically in terms of abort-prefix probabilities
5. geometric upper bounds follow from bounds on the one-step abort probability

The native retry API measures the proposition-valued `signAttemptAborts` observation and the
Nat query-count marginal. Commitments, private prover states, and responses need no measurable
spaces or attachment instances. Abort-prefix powers and geometric upper bounds permit missing
mass. Exact tail probabilities and finite geometric expectations require
`IsProbabilityMeasure 𝒟[signAttemptAborts ...]`: failure is not a successful abort marker.
The shared conditional-branch API supplies the recurrence and losslessness rules.

These identities describe repeated use of the supplied handler in its monad. A persistent
random-oracle cache is state, not independent resampling; establish its abort bound in the
stateful execution rather than applying a stateless power formula to separately reset attempts.

This is the main reference for:

- tail-sum expectation theorems
- stopping-time style query bounds

## Typeclass Hygiene

The query-tracking files now try to keep theorem signatures narrow.

Preferred pattern:

- put only genuinely shared assumptions in section variable blocks
- localize lawful attachment, `LawfulMonad`, measure semantics, chosen measurable spaces,
  measurability proofs, and cost-marginal probability certificates to the declarations that
  need them; structural cost proofs require no probability interpretation
- if a proof needs extra decidability or classical choice, install it locally with `classical` or
  a local instance

Avoid:

- wide sections followed by repeated `omit ... in`
- theorem statements carrying large blocks of unused typeclass assumptions

## Implementation Pattern

When adding a new example or construction:

1. Prove the pathwise exact/bounded theorem first.
2. If cost is output-determined, add a `UsesCostAs` theorem.
3. Derive expected-cost theorems from those generic bridges.
4. If the cost is natural-valued and behaves like a stopping time, look for a tail-sum theorem
   rather than forcing a coarse worst-case expectation bound.

This keeps the theorem layer mathematically honest and makes the public API easier to read.

## Exact Fischlin signing costs

`VCVio/CryptoFoundations/Fischlin/ExpectedCost.lean` instruments the actual zero-stopping
search with `HasQuery.Program.withUnitCost`, retaining its output, additive counter, and final
random-oracle cache. A duplicate-free list of `n` challenges, initially fresh for every response,
has expected hash calls `∑ j < n, (1 - 2⁻ᵇ)^j`. Public execution equations distinguish fresh
sampling from cache hits: both count a call, while a hit preserves its cached answer.

`ExpectedSigningCost.lean` composes the actual searches at distinct repetition tags and proves
the honest signer's exact expectation `ρ * 2ᵇ * (1 - (1 - 2⁻ᵇ)^|Chal|)`. This includes zero
repetitions and a one-point hash range. The count measures hash calls; prover-local randomness,
response arithmetic, and cache lookup work have separate costs. Ordinary-import consumers in
`VCVioTest/FischlinExpectedCost.lean` also check the joint output/count/cache law for repeated
cached queries with a nonzero answer, where the fresh-search formula's hypotheses do not hold.
