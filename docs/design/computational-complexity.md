# Honest computational complexity for VCVio

Status: implemented and tested backend-relative foundation plus staged adequacy design,
audited 2026-08-28. The completed usability spike concludes that the foundation is sound and
replaceable but not yet broadly usable because bounded iteration, quantitative handler
substitution, and concrete-backend adequacy are missing. Bounded sequencing and output recovery
now live in PolyFun's generic resource layer and pass the VCVio root validation gates.
This document fixes the intended meanings, trust boundary, layer ownership, and acceptance
criteria. It distinguishes declarations that exist in the current branches from reserved names
and later adequacy work.

The measured workload matrix, ergonomics score, and promotion decision are in the
[computational-complexity usability spike](computational-complexity-spike.md).
The current reviewer-facing evidence classification and promotion gates are in the
[computational-complexity feasibility record](computational-complexity-feasibility.md).

## Implementation snapshot

The current branches contain the following machine-checked slice:

Here, "landed" means present in these implementation branches; it does not
claim that a pull request has been opened or merged.

- PolyFun has `SecondOrderPolynomial`, deterministic first-order polynomial syntax,
  `QuantitativeStepClass`, `PolyRealizer`, `QuantitativeRealization`,
  `ExecutionCost`, and finite typed `ExecutionTrace`s. `Conforms`,
  `ResolvesInUnder`, `TraceProgressUnder`, and `RunsWithinUnder` give exact
  pathwise bounds relative to an allowed-answer relation. Optional category and
  exact-category mixins, an explicit `PolynomialModel`, quantitative structural
  mixins, and unbounded `ofFn`, precomposition, result-map, uniform
  sequential-composition, and certified lens-transport constructors are also
  present. `QuantitativeRealization.OutputSizeRecovery`,
  `finalHeadSize_le_peakHeadSize`, and `returnedSize_le_peakHeadSize` expose the exact law relating
  a returned payload to the already charged tagged readout; `PolyOutputSizeRecovery` supplies its
  first-order polynomial form. This prevents a tagged encoding from hiding a superpolynomially
  larger returned payload. `RankedRunCertificate` derives nonvacuous termination from a decreasing
  rank. Exact dependent phase decomposition,
  `PolynomialSeqCompHandoffBound`, and `PolynomialSeqCompCostCertificate` support genuine
  polynomially bounded sequencing: component bounds compose once reachable
  handoffs have one envelope and the concrete assembled machine's structural overhead has been
  proved. Exact phase-source lengths account for every visible query, so termination does not
  depend on query units placed in the backend-overhead certificate.
  Bidirectional trace transports support bounded input precomposition, while bounded result
  mapping uses an explicit `MapResultCostCertificate`.
- PolyFun also owns the generic polynomial resource layer: `ExecutionCostPolynomial`,
  `ResponseResourceModel`, `ResponseResourceContract`, `PolynomialRunBound`,
  `PolynomialProgramWitness`, `PureResourceCertificate`, `RankedResource.PotentialCertificate`,
  `RankedResourceCertificate`, and the polynomial sequencing certificates.
- VCVio has `SecurityFamily.packProgram` and thin crypto-facing aliases
  `ResourcePolynomial`, `OracleResourceModel`, `OracleContract`, `StrictPPTWitness`,
  `PureCertificate`, `ResourcePotentialCertificate`, and `RankedPPTCertificate`. VCVio retains the
  policy predicates `IsOraclePPTBy` and its fair-coin specialization `IsPPTBy`.
  `HandlerCertificate` packages
  one uniform strict-PPT dispatcher plus whole-tree answer conformance, and semantic handler
  closing preserves leaf conformance. Every such name retains an explicit quantitative backend
  and pinned `Boundary`. Every strict witness also carries a boundary-local polynomial
  output-recovery certificate. `BindCertificate` packages PolyFun's generic reachable-handoff and
  exact structural-cost certificates and exposes their composed run bound through the VCVio
  strict-PPT facade.
- The ElGamal canary exposes the one-time DDH reduction as fully syntactic open
  oracle code, proves its exact three-query structure, and proves that semantic
  closing recovers the established reduction. The conservative
  `@[ppt_primitive]`, `ppt`, `ppt?`, and `ppt using` tooling performs only exact
  lookup of certified `PolyRealizer` data or proved `IsOraclePPTBy` theorems.
- The optional `VCVioComplexity` package directly imports the compatible
  complexitylib machine and Cobham-definition modules. It provides closed
  representations, exact `TM.reachesIn` run certificates, exact run costs, a
  pointwise polynomial certificate, a Mathlib-polynomial-to-PolyFun adapter, and
  explicit closure requirement structures. Its `PureCanary` constructs the
  concrete machines for a unit identity realization and proves an end-to-end
  backend-relative `IsOraclePPTBy` theorem over the empty oracle. Its
  `OracleCanary` uses the same trusted representation and exact-run layer for a
  real enabled fair-coin transition, proves both replies have the same exact
  resource cost, and derives `oneCoin_isOraclePPTBy` and the public facade
  `oneCoin_isPPTBy`. Exact-run output-length lemmas justify
  `PolynomialCode.toPolyRealizerFromTime`. The package records that its pair codec is incompatible
  with complexitylib's canonical pairing and tests second-order quantification over two
  fixed-answer envelopes. It does not yet export an inhabitant of the general machine-level
  closure gates or compile arbitrary PolyFun machines to complexitylib machines.

The following are design targets, not claims about the current API: a richer
event-decorated `ResourceTrace`, bounded iteration and handler composition, general polynomial
resource laws for remaining structural closure, trace projection into all existing VCVio
semantics, efficient-sampler certificates, the resource-substitution theorem that closes a
caller with a `HandlerCertificate`, an exact-resource instantiation of the
existing `SecurityGame.ReductionWithCost`, and expected/nonuniform and UC
classes. Most importantly, **the general `OracleTM` compiler and adequacy theorem,
the machine-level closure-gate inhabitants, and an unqualified
`VCVioComplexity.IsPPT` are not yet proved or exported**. Backend-relative names
ending in `By` do not become conventional machine-model PPT until that adequacy
chain is proved.

## Decision summary

VCVio will use a fully syntactic model of probabilistic and oracle computation.
A computation is polynomial time only when executable code realizes every local
step, the code has an operational cost semantics, and the resulting interaction
tree satisfies a proved resource bound on every contract-admitted, well-typed
answer path. A Lean function, an injective encoding, a query bound, or a claimed
numeric cost is not by itself evidence of efficient computation.

When it is eventually exported, the unqualified `PPT` name will mean **strict
uniform probabilistic polynomial time**. The machine will be fixed across the
security parameter, receive `1^n` and the encoded input, and halt within one
polynomial on every random tape. Nonuniform, expected-time, and open-oracle
variants have different names. Until adequacy is proved, only the explicit
backend-relative `IsOraclePPTBy` and `IsPPTBy` predicates are available.

Only the [VCVio](https://github.com/Verified-zkEVM/VCVio) and
[PolyFun](https://github.com/Verified-zkEVM/PolyFun) repositories receive PRs
for this project. complexitylib, CSLib, and Mathlib are dependencies and design
inputs for now; this plan opens no PRs or issues in those repositories.

The dependency boundary is:

```text
VCVioComplexity ----> VCVio ----> PolyFun ----> Mathlib
       |--------------------> PolyFun
       `----> complexitylib ------------> Mathlib
```

An arrow means "imports." PolyFun owns the generic syntactic and quantitative
realizability theory. Core VCVio owns the backend-neutral `OracleComp`,
probability, and cryptographic bridges. An optional nested Lake package,
`VCVioComplexity`, owns the first concrete backend substrate and adapter work using
[complexitylib](https://github.com/SamuelSchlesinger/complexitylib). Core
PolyFun and core VCVio do not import complexitylib.

## Security and trust model

### What the definition must prevent

The design treats the following as attacks on the complexity definition:

- **Shallow-function escape:** an arbitrary Lean function performs
  noncomputable or exponential work inside `pure`, a bind continuation, a
  state transition, or an output map.
- **Encoding cache:** an existentially selected encoding stores the answer to a
  hard problem alongside its input. Injectivity alone does not prevent this.
- **Advice escape:** a separate machine for every `n` stores an unbounded truth
  table. That is nonuniform computation, even when each selected machine runs
  quickly.
- **Fake meter:** a definition labels an operation with cost `1` without tying
  the label to an executable operational semantics.
- **Query-count substitution:** a program makes polynomially many queries but
  performs unbounded work between them, emits exponentially large data, or
  receives unbounded replies.
- **State-growth escape:** polynomially many individually polynomial steps
  double the represented state at each round.
- **Representation escape:** a theorem changes to an incompatible encoding at
  an existential boundary or assumes a decoder without proving its cost.
- **Sampling escape:** an arbitrary `PMF` or a finite uniform distribution is
  declared efficient without an implementation from random bits.
- **Expected-time composition escape:** two expected-time components are
  composed despite adversarial correlation invalidating the expected bound.
- **Reactive ping-pong:** every node is locally polynomial per activation, but
  the network creates superpolynomially many activations.

These are not merely documentation warnings. Each becomes a negative regression
test or a missing-constructor theorem described below.

### Trusted core

The desired trust chain is:

1. a syntactic PolyFun interaction machine;
2. executable realizers for `init`, `head`, and enabled `update?`;
3. the backend's small-step execution and exact resource trace;
4. semantic-preservation and overhead theorems connecting that execution to
   the original `FreeM` tree;
5. polynomial closure in Mathlib's ordinary mathematics.

No complexity theorem may depend on `sorryAx`, a custom axiom, `unsafe`,
`native_decide`, or an unverified evaluator. Existing VCVio axiom-sweep and
import-isolation gates apply. Classical logic used by proofs is acceptable;
unproved computational behavior is not.

## Target vocabulary and current availability

The names and quantifiers below are normative. Namespace qualification may be
adjusted to satisfy the module system, but their meanings may not drift.

| Name | Availability | Meaning |
| --- | --- | --- |
| `PolyRealizer` | Landed in PolyFun | Executable backend code with first-order polynomial certificates for both work and encoded output growth. |
| `OutputSizeRecovery` | Landed in PolyFun | A boundary-local monotone law recovering returned-payload size from the charged tagged readout size. |
| `PolyOutputSizeRecovery` | Landed in PolyFun | The first-order polynomial form of `OutputSizeRecovery`, usable with the trace's charged `peakHeadSize`. |
| `ExecutionTrace` | Landed in PolyFun | A finite typed query-answer prefix of one realization. Its exact fold charges local work, total traffic, query count, and peak state/readout sizes. |
| `ExecutionTrace.Conforms` | Landed in PolyFun | Every answer in a typed trace satisfies one explicit dependent allowed-answer relation. |
| `ResourceTrace` | Reserved | A richer event decoration adding explicit randomness, final-output, and other resource events to `ExecutionTrace`. |
| `RunsWithinUnder` | Landed in PolyFun | A componentwise bound on every conforming finite `ExecutionTrace`, relation-restricted resolution, and an allowed answer at every conformingly reachable pending query. It is exact and backend-relative, not asymptotic. |
| `RunsWithin` | Landed in PolyFun | The specialization of `RunsWithinUnder` allowing every typed answer. |
| `PolynomialSeqCompHandoffBound` | Landed in PolyFun | An input-indexed polynomial envelope for the second-phase bound at every value actually returned by a conforming first-phase trace. |
| `PolynomialSeqCompCostCertificate` | Landed in PolyFun | An exact comparison between the concrete composed realization's cost and its phase-decomposed source cost plus explicit polynomial structural overhead. |
| `PolynomialRunBound.seqComp` | Landed in PolyFun | Derives cost, progress, and resolution for bounded dependent sequential composition from two component bounds, a handoff envelope, and a concrete cost certificate. Exact phase-source length makes the resolution argument independent of certificate overhead. |
| `RankedRunCertificate` | Landed in PolyFun | A natural rank decreasing on every admitted answer, plus explicit query progress; it proves termination but does not invent backend costs. |
| `MapResultCostCertificate` | Landed in PolyFun | A pathwise comparison between exact mapped-result and source trace costs, used for sound bounded result mapping. |
| `SecondOrderPolynomial` | Landed in PolyFun | A monotone polynomial expression over base input size and named length functions. |
| `ResponseResourceModel` / `OracleResourceModel` | Landed in PolyFun / VCVio alias | A dependent allowed-answer relation and per-interface monotone reply-size functions, with a proof that every allowed typed reply fits its encoded-size envelope. Handler costs are intentionally outside the open contract. |
| `ResponseResourceContract` / `OracleContract` | Landed in PolyFun / VCVio alias | A pinned query-to-interface classification, an admissibility predicate on resource models, and evidence that the compatible model space is nonempty. |
| `PolynomialProgramWitness` / `StrictPPTWitness` | Landed in PolyFun / VCVio alias | One realization by backend `B` and one second-order resource polynomial bounding every path conforming to every compatible resource model. |
| `IsOraclePPTBy B` | Landed in VCVio | Propositional existence of the crypto-facing strict witness above. |
| `IsPPTBy B` | Landed in VCVio | `IsOraclePPTBy B` specialized to the explicit fair-coin interface. |
| `PureResourceCertificate` / `PureCertificate` | Landed in PolyFun / VCVio alias | Explicit polynomial result and resolved-readout code, plus executable unreachable-transition code, sufficient to derive the generic witness and VCVio's `IsOraclePPTBy` for `pure`. |
| `RankedResource.PotentialCertificate` / `ResourcePotentialCertificate` | Landed in PolyFun / VCVio alias | Local resource potentials over actual realization costs, paired with rank/progress evidence, sufficient for `RunsWithinUnder`. |
| `RankedResourceCertificate` / `RankedPPTCertificate` | Landed in PolyFun / VCVio alias | One realization, implementation proof, resource polynomial, and model-relative ranked potentials, sufficient for the generic witness and VCVio's `IsOraclePPTBy`. |
| `BindCertificate` | Landed VCVio facade | Packages PolyFun's generic polynomial handoff and structural-cost certificates and derives a VCVio strict-PPT bind. |
| `HandlerCertificate` | Landed seam in VCVio | One uniform strict-PPT packed handler dispatcher, an explicit map from each inner model to the outer model it implements, and answer conformance for that selected pair. Semantic leaf conformance composes; machine and resource substitution remain staged. |
| `ppt` | Landed conservative tooling | Exact local-assumption or registered-primitive lookup for goals headed by `PolyRealizer` or `IsOraclePPTBy`; it performs no recursive synthesis or generic proof search. |
| `VCVioComplexity.IsPPT` | Reserved, not exported | The eventual strict uniform PPT predicate after the complexitylib adequacy theorem. |
| `IsExpectedPPT` | Reserved | Expected polynomial time with its probability space and tail/independence hypotheses exposed. It has no unrestricted oracle-substitution rule. |
| `IsNonuniformPPT` | Reserved | A polynomial-size randomized machine or circuit family with explicit description/advice bounds. |
| `P`, `FP`, `BPP`, `PPoly` | Upstream concepts | Conventional language, function, randomized-language, and circuit-family classes of a concrete backend. They are not aliases for interactive predicates; the current optional package does not re-export the incompatible full class layer. |

Strict bounds quantify over every coin path and every oracle-answer path admitted
by the pinned contract. Probability enters only when those syntactic paths are
interpreted. Thus a legal zero-probability reply cannot hide an overlong branch,
while a typed reply explicitly excluded by the contract cannot be smuggled into
a conforming trace. `TraceProgressUnder` prevents choosing an empty allowed
relation at a reachable query merely to make the path quantification vacuous.

### Uniform security families

An arbitrary Lean family `n -> machine n` is not a uniform implementation.
VCVio now provides a `SecurityFamily` packing layer with the following behavior:

- `SecurityFamily.Spec` tags all interfaces `spec n` by the security parameter.
- `packProgram` tags the inputs and outputs of
  `forall n, alpha n -> OracleComp (spec n) (beta n)`.
- Member-wise resource contracts use one global label space and response modulus, so the one
  uniform second-order polynomial can mention fixed oracle symbols. The raw dependent carrier
  `Σ n, label n` does not let a finite polynomial select the current arbitrary parameter; it is
  useful only when the finitely mentioned sigma labels have separate fixed meanings.
- A uniform realization is one fixed piece of code for the packed program. The
  landed packing is representation-neutral: its input is the dependent pair
  `(n, input)`, and it deliberately does not choose an encoding of `Nat`.
- A concrete cryptographic backend must pin a unary encoding of `n` and prove
  the intended relationship between `Q.size bd.input (n, input)` and
  `n + inputBits`. That relationship is a staged adequacy obligation, not a
  theorem of `packProgram`.
- The landed resource fold charges the encoded final readout, every query and
  tagged answer, and peak intermediate-state/readout size. A separately named
  output-length event remains part of the richer `ResourceTrace` target.

The packing declarations only express a family. Uniformity comes from the one
realizer theorem, never from the packing function itself. A family of separate
codes will be admitted only by the staged `IsNonuniformPPT`, where code/advice
length is part of the bound.

## PolyFun implementation

PolyFun already provides the qualitative foundation:
`StepClass`, `Boundary`, `Realization`, `IsRealizableWithin`, structural closure,
`CodeRetract`, `PolyCodable`, and `PolyTranslatable`. It also exposes the correct
first-order machine boundary:

```lean
init    : alpha -> State
head    : State -> beta ⊕ p.A
update? : State × p.Idx -> Option State
```

The partial transition is load-bearing. `updateFlat` maps mismatched answers to
the unchanged state and does not compose across a sequential handoff without
extra decidable equality and junk-state conventions. `output`, `expose`, and
`updateFlat` remain useful derived execution APIs, but they are not the
complexity boundary.

### Quantitative step classes

The landed quantitative refinement has a Type-valued witness with the following
surface:

```lean
QuantitativeStepClass C
QuantitativeStepClass.Realizer source target f : Type
QuantitativeRealization Q boundary : Type
QuantitativeRealization.toRealization : Realization C boundary
```

A `Realizer` is backend code indexed by the function it computes.
`QuantitativeStepClass` supplies its admissibility erasure, a pinned size
function, and a backend-relative exact cost. Identity and sequential composition
are deliberately optional: `HasCategory` supplies executable code, connection
overhead, and a sound cost inequality, while `HasExactCategory` and
`ExactCategory` record an optional exact equation. Landed Type-valued mixins
retain executable product, sum, option, and distributivity code. The induced
qualitative `StepClass.Hom` merely forgets the witness.

`PolyRealizer` adds first-order polynomial work and encoded-output-size bounds
to one `Realizer`. `FirstOrderPolynomial.ofNatPolynomial` gives a deterministic
translation from Mathlib's `Polynomial ℕ`, including powers. `PolynomialCategory`,
`StructuralKernel`, `PolynomialStructuralClosure`, and `PolynomialModel` package
explicit polynomial categorical and structural choices without forcing a global
instance or claiming that every quantitative backend has machine-level closure.

`QuantitativeRealization` stores realizers for `init`, `head`, and `update?` and
erases to the existing `Realization`. Program predicates retain an `Implements`
proof as their semantic anchor, so the realization agrees with the original
`FreeM` tree. The landed trace fold charges initialization once, `head` at every
visited state, every enabled `update?`, and the final observation.
`RunsWithinUnder` bounds only traces whose replies satisfy its explicit relation,
but also requires `ResolvesInUnder` at the query budget and
`TraceProgressUnder` at every conformingly reachable pending query. This rejects
infinite allowed paths and empty allowed-response sets rather than obtaining
bounds vacuously.

The landed closure layer constructs quantitative realizations for an explicitly
realized returning function, input precomposition, result postcomposition, and
sequential composition, as well as interface transport along a
`Lens.QuantitativelyAdmissible`. The second phase of sequential composition is
one realization over all intermediate values, so pointwise continuation
witnesses cannot introduce nonuniform advice.

The landed bounded-sequencing layer decomposes every dependent composite prefix into its
exact left, handoff, and right source phases. The decomposition generically preserves answer
conformance. `PolynomialSeqCompHandoffBound` bounds the second phase only at values actually
returned by a conforming first phase, while `PolynomialSeqCompCostCertificate` compares the
concrete composed realization's `ExecutionCost` with that exact source cost plus explicit
structural overhead.
`PolynomialRunBound.seqComp` then derives the composite cost bound, progress, and resolution.
Thus bounded sequencing is present without pretending that PolyFun can infer a backend's
structural wiring cost.

A separately packaged reachable-state invariant, explicit decoder cost,
structural resource transformers, and a distinct final-output event remain
staged. Current peak-size accounting nevertheless ranges only over states and
readouts that occur on a typed trace, rather than imposing a bound on every
inhabitant of the state carrier.

### Resource traces

The landed `ExecutionTrace` is an indexed inductive family of finite typed
query-answer prefixes. `ExecutionCost` folds five components:

- backend-relative local work;
- total visible query count;
- total encoded query-and-answer traffic;
- peak encoded hidden-state size; and
- peak encoded one-step readout size.

Per-interface query-count and traffic folds, append laws, exact query-count
agreement, and componentwise ordering are present. `ExecutionTrace.Conforms`
checks every dependent response in a prefix. `RunsWithinUnder` bounds every
conforming prefix, separately bounds relation-restricted syntactic resolution,
and requires every conformingly trace-reachable pending query to admit an
allowed response. `RunsWithin` recovers the unrestricted all-typed-answer form.

The reserved `ResourceTrace` target is a decoration of the existing PolyFun
interaction path with a more granular event vocabulary. It retains the landed
aggregates while exposing, at minimum, separate initialization/readout/update
work events, current state size, individual query and answer lengths, explicit
random-bit consumption, and final encoded output length.

Erasing that future decoration must produce definitionally, or by a named
theorem, the existing execution path. VCVio's `QueryCount`, `QueryLog`, weighted
writer cost, and total query bound still need to be proved projections rather
than parallel semantics.

### Open-oracle costs

A relative oracle invocation contributes one invocation event. The caller still
pays for constructing and writing the query, reading and decoding the answer,
and all subsequent local work.

`SecondOrderPolynomial` is an inductive expression with natural constants, one
base-size variable, addition, multiplication, and applications of named
monotone function variables. In an open strict-PPT witness, `OracleModulus`
exposes only reply-length functions. Evaluation, composition, reindexing,
substitution, and monotonicity theorems are part of the landed core API.

An `OracleResourceModel` supplies a dependent relation of admitted replies and,
for each query size, an upper bound on encoded reply length. It proves that every
admitted typed reply fits the bound. The bound covers the tagged response
`p.Idx`, so pairing and tag overhead are visible.

The landed `OracleContract` pins the query-to-interface classification, defines
which resource models are admissible, and requires a nonempty compatible model
space, preventing a universal bound from being proved vacuously.
`StrictPPTWitness` quantifies one realization, one `ResourcePolynomial`, and one polynomial
returned-payload recovery law over every compatible model. Handler time and state are deliberately
absent from the open caller contract. The landed `HandlerCertificate` instead packages one
uniform strict-PPT realization of the packed dependent handler and proves that
each inner-conforming result is admitted by the outer model selected through its explicit
`modelMap`. It does not impose compatibility between unrelated inner and outer models. The
semantic `packHandler`/`closeHandler` layer and whole-tree result-conformance
lemmas are also present.

What is not yet proved is the resource substitution theorem that combines a
caller's conforming trace with those handler traces, accounts for handler work,
state, query traffic, and answer lengths, and derives an exact resource
inequality and polynomial corollary. A `HandlerCertificate` is therefore a
sound proof-bearing seam, not yet a general PPT closure theorem. This follows
the type-2 feasibility discipline of [Kapron and
Cook](https://doi.org/10.1137/S0097539794263452).

### Structural closure

Executable structural mixins and unbounded constructors are landed for:

- `pure` only when the returned function has a `Realizer`;
- input precomposition and result mapping with certified realizers;
- `seqComp`/monadic bind using one uniform second-phase machine;
- products, sums, options, and distributivity; and
- interface transport along a quantitatively admissible lens.

For the immediately returning case, PolyFun's `PureResourceCertificate`, exposed in VCVio as
`PureCertificate`, is also a landed bounded
constructor. It requires a `PolyRealizer` for the result function, a
`PolyRealizer` for the resolved `Sum.inl` readout (so tag cost and growth are
charged), and executable code for the unreachable partial transition. From
these it derives `RunsWithinUnder`, `StrictPPTWitness`, and `IsOraclePPTBy` under
any pinned contract.

For sequential composition, PolyFun derives a `PolynomialRunBound` from the two component bounds,
a reachable-handoff envelope, and an exact cost certificate for the assembled realization.
VCVio's `BindCertificate` is intentionally only a facade over those generic obligations. The
remaining client obligations are genuinely backend-specific: establish the reachable handoff
bound and prove the exact composite-to-phase cost comparison with polynomial structural overhead.

The following cost-preserving constructors and polynomial corollaries remain
staged:

- bounded/PPT forms of the remaining landed structural and lens constructors;
- bounded folds and the fair-coin primitive;
- caller/handler resource substitution from a `HandlerCertificate`;
- `RunsWithin`-preserving representation transport with polynomial transcoders.

A pointwise family of PPT witnesses for the continuations `k x` is not enough
for uniform bind closure. The continuation dispatcher itself must be represented
by one code object.

### Representations

The landed backend-relative predicates pin representations in an explicit
`Boundary`; they never quantify existentially over a convenient encoding. The
final concrete cryptographic statements must additionally carry `PolyCodable`
evidence: an admissible word encoder, admissible partial decoder, and
`decode (encode x) = some x`.

Add a quantitative representation-equivalence certificate, provisionally
`PolytimeEquivalentEncoding`, which includes forward and backward executable
transcoders, semantic identity proofs, and polynomial time/size transformations.
Only this certificate transports `IsOraclePPTBy` between encodings. Existential
choice of an encoding is never part of the predicate.

## VCVio implementation

### Backend-neutral bridge

Core VCVio translates `OracleSpec` and `OracleComp` to the packed PolyFun
interface and exposes `IsOraclePPTBy`/`IsPPTBy` with an explicit backend
argument. Do not choose a backend through a global, unconstrained typeclass.

The landed bridge packages security families, evaluates a five-component
`ResourcePolynomial` in each response-conforming `OracleResourceModel`, supplies
a canonical fair-coin contract admitting both Boolean answers, and erases a
strict witness to quantitative and qualitative realizability. When a selected
model admits every typed reply, its query component also gives a syntactic
`IsTotalRollBound`. `PureCertificate` provides the first complete PPT
constructor, while `HandlerCertificate` pins the executable and semantic inputs
needed by future closing. Soundness fixtures check that illegal replies cannot
conform, allowed zero-probability replies remain charged and resolving, and a
reachable empty response type refutes `RunsWithinUnder`. The following bridge
theorems remain staged:

- quantitative erasure agrees with `simulateQ` and existing support semantics;
- under `IsProbabilitySpec`, interpreting response events agrees with
  `evalDist` and `Pr[...]`;
- current query-bound and weighted-cost results are trace projections;
- `simulateQ`/interface replacement transforms resource contracts
  compositionally.

`IsProbabilitySpec` says how to interpret a query probabilistically; it says
nothing about efficient sampling. The staged `EfficientSampler` certificates
have separate constructors for strict, expected-time, and statistically
approximate coin implementations. Exact finite uniform sampling for a
non-power-of-two cardinality must not acquire strict bit-PPT through rejection
sampling.

Randomness is modeled as an explicit coin interface. A deterministic syntactic
machine asks for bits; the probability semantics interprets those answers as
fair and independent. The same principle applies to oracle responses,
adversarial messages, and later scheduler choices.

The existing `SecurityGame.ReductionWithCost` already pairs a reduction with an
abstract monotone cost transformer and composes those packages. Its staged
complexity bridge instantiates those profiles with `ExecutionCost` and
second-order bounds and connects them to exact realization traces.

The first conservative automation layer is landed. `@[ppt_primitive]` validates
only concrete `def`/`opaque` values ending in `PolyRealizer` and
theorem/opaque proofs ending in `IsOraclePPTBy`; finalized metadata prevents an
axiom placeholder from remaining registered. `ppt` and `ppt?` try only a
definitionally exact local assumption or a declaration in the matching literal
head bucket, and `ppt using term` elaborates exactly the supplied term. There is
no simp set, recursive application, or generic search. Compositional synthesis
from proved structural closure rules remains staged, and arbitrary Lean
functions never become executable through the tactic.

Existing security APIs parameterized by an abstract `isPPT` predicate remain
available during migration. Concrete wrappers using certified adversaries are
added first, and ambiguous wrappers are deprecated only after the adequacy
theorem and canary examples land.

### Syntactic ElGamal canary

`Examples/ElGamal/ComputationalComplexity.lean` presents the established
one-time ElGamal DDH reduction as an open `OracleComp` over three explicit
capabilities: adversary message selection, a challenge coin, and adversary
distinguishing. It proves a total query bound of three, exactness when the first
adversary state type is inhabited, and one query for each classified
capability. Primitive realizer fields expose every nonstructural local operation
that a later quantitative realization must implement. Finally, closing the open
syntax with a concrete adversary and the fair-coin implementation is proved by
`rfl` to recover the existing semantic reduction.

This canary establishes that the interaction-first API is usable for a real
reduction and that its syntax agrees with existing probability-level code. It
does not yet claim a complete `IsOraclePPTBy` theorem for ElGamal: constructing
the full quantitative realization and composing polynomial bounds through the
three capabilities remain follow-on work.

### Optional complexitylib instantiation

The first concrete backend lives in a nested package in this repository, not in
the default VCVio dependency graph. Its Lake package depends by path on root
VCVio and directly on complexitylib. This avoids making every VCVio user fetch a
young complexity library and avoids a dependency cycle.

The audited source is complexitylib commit
[`b6738219a3a3c50967d6bd16cba9487887ca6b66`](https://github.com/SamuelSchlesinger/complexitylib/tree/b6738219a3a3c50967d6bd16cba9487887ca6b66).
At Lean/Mathlib 4.33, direct imports of
`Complexitylib.Models.TuringMachine` and
`Complexitylib.Classes.P.Cobham.Defs` compile unchanged. The package builds an
exact certificate layer on that machine model and inhabited PolyFun
quantitative backends for individual exact `Code` and polynomially certified
`PolynomialCode` values. `PolynomialCode.toPolyRealizer` translates the stored
Mathlib polynomial into PolyFun's first-order syntax and deliberately requires a
separate encoded-output-growth proof. The package does not yet define a backend
capable of realizing arbitrary PolyFun structure. The conventional aliases
`VCVioComplexity.IsOraclePPT`, `IsPPT`, `IsExpectedPPT`, and
`IsNonuniformPPT` are reserved and are not exported.

This import direction is conceptually sound: VCVio-specific interaction is an
instantiation over a general concrete machine library. Compatibility of the
higher machine-combinator stack is a blocker for general closure, not a layering
problem. The cited complexitylib revision pins Lean and Mathlib 4.30, while
VCVio pins 4.33. The completed preflight used VCVio's toolchain and made the
direct Mathlib 4.33 pin authoritative. No file in the checked-out complexitylib
dependency was edited.

The preflight found two separate incompatibilities. The upstream asymptotics
module fails, so the package contains one attributed adaptation,
`VCVioComplexity.Asymptotics.PolyBound`, omitting only the `BigO` bridge. The
higher Turing-machine combinator stack also fails, so the package exposes
PolyFun's category, exact-category, product, sum, option, and distributivity mixins as explicit
requirements but has no exported inhabitants
for those general machine-level gates. Future machine combinators must inhabit those PolyFun
interfaces directly; VCVio does not maintain parallel wrapper contracts or conditional adapters.
Direct and adapted implementations of the same declaration are not maintained simultaneously;
`PROVENANCE.md` records the exact source and removal condition. Any future
snapshot must remain minimal, use a distinct VCVio namespace, preserve upstream
attribution and the
[Apache-2.0 license](https://github.com/SamuelSchlesinger/complexitylib/blob/b6738219a3a3c50967d6bd16cba9487887ca6b66/LICENSE),
and keep new oracle-machine code outside the adapted source.

No compatibility work is sent to complexitylib, CSLib, or Mathlib during this
project. Improvements discovered there are recorded locally for later
coordination.

### Concrete adequacy target

The landed concrete substrate provides a closed representation grammar for
words, empty types, unit, booleans, unary naturals, fixed-width bit vectors,
products, sums, and options; exact total word-machine `Code`; a bridge to
complexitylib's `TM.ComputesInTime`; `PolynomialCode`; and conversion of its
Mathlib polynomial work bound to `PolyRealizer`. Its representation grammar
prevents callers from smuggling an arbitrary cached encoding into the backend
boundary.

`VCVioComplexity.Backend.PureCanary` is a small complete instantiation rather
than another abstract cost meter. It supplies the exact complexitylib runs for
unit initialization, a two-step machine that writes the resolved-left sum tag,
and the unreachable transition; packages their work and output-size
polynomials in `PureCertificate`; pins the nonvacuous empty-oracle contract; and
derives `unitIdentity_isOraclePPTBy`. This proves that the exact-machine adapter
can reach VCVio's strict backend-relative predicate for a concrete program.

The general machine-level closure gate is still uninhabited, so this canary does
not establish arbitrary identity/composition/structural closure. Nor is it the
general PolyFun-to-machine adequacy theorem required for an unqualified class.

The not-yet-proved adequacy phase must define a general `OracleTM` control layer
over complexitylib's concrete multi-tape machine and trace model. It has
read-only input, work, query, answer, and output tapes; explicit query/answer
control states; a distinguished coin port; and deterministic behavior on
malformed encodings.

Provide:

- exact time, space, query, and traffic traces;
- `CompilesTo` from a quantitative PolyFun realization;
- `SimulationOverhead` with an explicit polynomial;
- preservation of output, complete typed oracle transcript, and coin behavior;
- a converse embedding of `OracleTM` behavior into PolyFun;
- an adapter from Bolton Bailey's Cobham/`FP` syntax to PolyFun realizers, with
  direct machine construction as an escape hatch.

`VCVioComplexity.IsPPT` is not defined or exported before this chain and the
required machine-level closure results are proved. A sum of separately asserted
step costs, such as PR #500's `detTotalTime`, is a useful derived estimate but is
not an adequacy theorem.

## Prior VCVio work

The new work is modeled on the earlier attempts, but no declaration is accepted
solely because it appeared there.

| Work | Retain or port | Replace or reclassify |
| --- | --- | --- |
| [#460](https://github.com/Verified-zkEVM/VCVio/pull/460) | The inductive-program/coalgebraic-machine correspondence, typed transcripts, all-handler semantic agreement, early halt, query-bound bridges, and the observation that state growth must be charged. Most generic dynamics now belong to PolyFun. | Its extensional per-step computability witnesses were vacuous under per-`n` encodings; replace its local dynamical API with current PolyFun, and do not use query bounds or all-state size alone as PPT. |
| [#481](https://github.com/Verified-zkEVM/VCVio/pull/481) | The description-size defense against lookup-table advice, pinned-boundary intent, bounded coin fold, closure experiments, and the counting/non-vacuity construction. | Its `PointedMachine` carrier is retired. A machine family is explicitly nonuniform; "canonical by statement-site discipline" becomes `PolyCodable`; component costs become operational traces and compilation. |
| [#487](https://github.com/Verified-zkEVM/VCVio/pull/487) | Port the closed counting cruxes with their existing Elias Judin and Aristotle (Harmonic) attribution when the new backend needs them. Preserve a diagonal non-vacuity theorem as a regression sentinel. | Non-vacuity is not adequacy and cannot replace executable realization or compiler correctness. Its content was already re-extracted into #500, so do not duplicate the proof lineage. |
| [#500](https://github.com/Verified-zkEVM/VCVio/pull/500) | `DynComputation.ImplementsWithin`, derived query bounds, final-readout accounting, the sorry-free non-vacuity theorem, useful coin/closure constructions, and its explicit P/poly diagnosis. | Do not merge the layer as-is. Replace `output`/defaulted `expose`/`updateFlat` as the cost boundary, raw injective encodings, the ambiguous `IsPolyTime` name, per-parameter machines as default PPT, all-carrier state bounds, the local cslib wrapper, and `detTotalTime` as the final foundation. |

The retained results should be ported theorem-by-theorem after the new APIs
exist. Old branches are reference material, not a source directory to copy.

## Literature decisions

### Complexity and cryptography textbooks

- [Arora and Barak, *Computational Complexity: A Modern
  Approach*](https://theory.cs.princeton.edu/complexity/book.pdf), motivates a
  fixed machine, explicit input length, and robustness through polynomial-cost
  simulations. VCVio follows that model-invariance pattern: exact costs are
  backend-specific, while polynomiality transports only through a proved
  simulation.
- [Goldreich, *Foundations of
  Cryptography*](https://www.wisdom.weizmann.ac.il/~oded/foc-book.html), uses
  probabilistic polynomial time in the strict sense: the polynomial bound is
  independent of internal coin tosses. That is the reserved meaning of VCVio's
  eventual unqualified `IsPPT`.
- [Boneh and Shoup, *A Graduate Course in Applied
  Cryptography*](https://toc.cryptobook.us/), and conventional reductionist
  texts track running time, number of oracle calls, and advantage as separate
  parameters. VCVio's existing abstract `ReductionWithCost` can therefore be
  instantiated with a structured resource profile instead of collapsing
  everything to an asymptotic predicate.
- [Katz and Lindell, "Handling Expected Polynomial-Time Strategies in
  Simulation-Based Security Proofs"](https://www.cs.umd.edu/~jkatz/papers/expected-full.pdf),
  shows why expected polynomial-time oracle strategies require care under
  simulation and composition. Expected PPT is a separate phase and receives no
  unrestricted `simulate` theorem.

### Oracle and reactive computation

[Kapron and Cook's type-2 feasibility
model](https://doi.org/10.1137/S0097539794263452) makes running time depend on
oracle-answer length through second-order polynomials. VCVio adopts this for
open computations rather than pretending that an oracle reply is a unit-cost
word.

For reactive systems, the [IITM
model](https://doi.org/10.1007/s00145-020-09352-1) distinguishes universally
bounded environments from environmentally bounded protocols. This explains why
per-node or per-activation PPT is insufficient. The later UC phase must account
for activations, sessions, scheduler decisions, and boundary traffic, and must
include a superpolynomial ping-pong counterexample before proving a composition
theorem.

### Formal cryptography foundations

- [FCF](https://www.cs.cornell.edu/~jgm/papers/FCF.pdf) demonstrates a
  foundational probabilistic language, concrete/asymptotic security bounds, and
  security definitions parameterized by admissible adversaries. VCVio keeps the
  parameterization and aims to supply an operationally adequate machine
  realization for it.
- [CertiCrypt](https://doi.org/10.1145/1480881.1480894) and
  [EasyCrypt](https://github.com/EasyCrypt/easycrypt) demonstrate the value of
  an explicit program language, relational reasoning, and game transformations.
  EasyCrypt's mechanized [adversarial complexity
  system](https://adrienkoutsos.fr/papers/journal-ec-cost.pdf) separately tracks
  intrinsic cost and calls to each oracle/adversary. The target `ResourceTrace`
  and staged exact-resource instantiation of the existing `ReductionWithCost`
  adopt that compositional resource-vector lesson, grounded in VCVio's syntactic
  paths.
- [SSProve](https://doi.org/10.1145/3594735) demonstrates typed package
  interfaces, free-monad semantics, and algebraic sequential/parallel linking.
  VCVio uses PolyFun's analogous structural machinery, while requiring
  additional executable certificates for pure host-language functions.
- [CryptHOL](https://eprint.iacr.org/2017/753.pdf) demonstrates foundational
  game-based probability and asymptotic cryptography in Isabelle/HOL. Its
  probability and game-proof ideas are complementary evidence, not a concrete
  Lean machine-cost backend.

Across these systems, compositional game or package semantics and honest local
runtime are separate achievements. VCVio must prove their connection rather
than infer one from the other.

## Lean ecosystem assessment

### complexitylib

complexitylib is the preferred first concrete backend because it has an
Arora--Barak-style multi-tape model, explicit machine traces and resource
bounds, uniform `P`/`FP`, randomized classes, circuits and `PPoly`, and a broad
complexity-theory development. In particular, Bolton Bailey's merged
[bitstring encodings PR](https://github.com/SamuelSchlesinger/complexitylib/pull/21)
provides parser-oriented encodings, and the merged [Cobham characterization of
`FP`](https://github.com/SamuelSchlesinger/complexitylib/pull/23) provides a
compositional feasible-function frontend. The open [projection refactor
PR](https://github.com/SamuelSchlesinger/complexitylib/pull/30) is research
input only; VCVio does not depend on an unmerged branch.

The Cobham syntax is the preferred user-facing way to certify ordinary pure
functions. It must compile to a quantitative realizer with semantic and cost
proofs. complexitylib's raw encoding injectivity is not enough for a VCVio
boundary; the adapter must also construct PolyFun's encode/decode retraction and
prove both directions feasible.

### CSLib

At VCVio's current pin, CSLib has a single-tape
[`PolyTimeComputable`](https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean)
with identity and composition, and a multi-tape
[`ComputableInTimeAndSpace`](https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean).
Its [complexity-theory roadmap](https://github.com/leanprover/cslib/issues/611)
explicitly favors several concrete machine models connected by resource-aware
simulations and discusses oracle/path tapes and a higher-level functional
machine. That is compatible with this design.

CSLib is therefore the likely long-term standardization target, but not the
first VCVio backend. Once both APIs stabilize, a second VCVio-owned adapter and
a polynomial-equivalence theorem can be added without changing PolyFun's core.
No CSLib PR is part of the current work.

### Mathlib

Mathlib currently exposes encoding-relative
[`TM2ComputableInPolyTime`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Computability/TuringMachine/Computable.lean),
but its composition theorem remains `proof_wanted` at the VCVio pin. Mathlib's
idiomatic long-term contribution is model-independent mathematics: explicit
encodings and retractions, polynomial/asymptotic algebra, counting, trace folds,
and probability. VCVio should not build its immediate end-to-end adequacy story
on an incomplete Mathlib TM API, and no Mathlib PR is planned now.

## Delivery phases

Any eventual review-sized PRs are limited to PolyFun or VCVio; no PR or issue is
opened in complexitylib, CSLib, or Mathlib. The present work is kept on those
two implementation branches. The
status annotations below describe this implementation snapshot; compatibility
preflight was intentionally performed early and does not bypass the adequacy
gate.

1. **Foundation and usability audit landed — record and qualitative baseline
   (VCVio/PolyFun).** This document, the completed usability-spike report, the
   optional-backend isolation gate, the qualitative-law inventory, and
   negative fixtures for empty responses, illegal replies, zero-probability
   allowed replies, and uncertified `ppt` lookup are present. Broader regression
   statements for `updateFlat`, encoding-cache, advice, and state-growth failures
   remain staged.
2. **Core and first bounded closure landed — quantitative PolyFun.**
   Type-valued realizers, optional categorical closure, first- and second-order
   polynomials, `PolyRealizer`, polynomial structural models, erasure, conforming
   typed resource traces, relation-restricted resolution/progress, ranked termination,
   bidirectional trace transport, bounded precomposition and result mapping, executable
   structural mixins, unbounded machine/program closure, exact dependent `seqComp` phase
   decomposition, and certified polynomial `PolynomialRunBound.seqComp` are present. The latter requires
   a reachable-handoff envelope and a cost comparison for the actual assembled machine. Richer
   events and reachable-state packages remain staged.
3. **Core and first proof-bearing constructors landed — backend-neutral VCVio
   bridge.** Packed security families, response-conforming oracle contracts,
   `IsOraclePPTBy`, fair-coin specialization, the conditional total-query
   corollary, crypto-facing aliases for PolyFun's pure and ranked certificates, and the
   `HandlerCertificate` seam are present. `BindCertificate` packages PolyFun's handoff and cost
   obligations and exposes the generic composed run bound and witness through VCVio. Semantic
   handler closing uses PolyFun's generic weakest-precondition theorem and preserves leaf
   conformance.
   These predicates and constructors currently classify returning, finite `FreeM` programs
   (including VCVio's `OracleComp` facade). They do not yet provide a complexity theorem for
   `ITree`, coinductive executions, `ProbResponder`, or the reactive/UC setting.
   General trace projections, probability erasure, efficient samplers,
   caller/handler resource substitution, and the exact-resource instantiation
   of `ReductionWithCost` remain staged.
4. **Substrate, adapter, and finite canaries landed — optional backend package.** The
   direct compatibility preflight, attributed `PolyBound` adaptation, exact
   per-machine substrate, exact-run output bound, Mathlib-polynomial-to-`PolyRealizer` adapter, and
   concrete unit `PureCertificate`/`IsOraclePPTBy` theorem are present. A second
   end-to-end certificate executes exactly one fair-coin query through concrete
   head and enabled-update machines, proves a strict bound for both replies, and exposes the
   public `IsPPTBy` facade. Pair-codec incompatibility, guarded trust reports, and a two-model
   second-order acceptance canary are regression-tested.
   The general machine-level category and structural closure gates remain
   uninhabited; a VCVio-owned `OracleTM` semantics remains staged.
5. **Not landed — adequacy.** Prove PolyFun-to-`OracleTM` compilation, converse
   embedding, transcript/coin preservation, and polynomial overhead. Only then
   export the unqualified concrete `IsPPT` alias.
6. **Partially landed — end-to-end canaries and tooling.** Direct exact-machine
   pure and one-query fair-coin canaries reach `IsOraclePPTBy`. Honest control-flow and
   certificate-builder regressions cover two queries, an adaptive branch, and one fixed
   natural-input parity loop, but do not instantiate backend code or PPT witnesses. The ElGamal
   one-time DDH canary exposes
   open syntax, exact query accounting, primitive-code obligations, and semantic
   closing; and conservative `ppt` lookup is present with rejection tests. A
   Cobham-frontend pure function, a certified sampler/handler closure theorem,
   an end-to-end bounded adaptive oracle computation, a bounded fold, one-time pad, a complete
   quantitative game reduction, compositional tactic rules, and migrated
   security wrappers remain staged.
7. **Not landed — expected time.** Add expectation and tail certificates,
   formalize the Katz--Lindell counterexample, and expose only hypothesis-rich
   closure rules.
8. **Not landed — reactive/UC complexity.** Instrument open processes,
   scheduler decisions, messages, sessions, activations, and environments;
   prove the relevant boundedness and composition results after the ping-pong
   negative test.

## Acceptance gates

These are release gates for the finalized design, not a claim that every test
or theorem below is present in the current partial implementation. Current
machine-checked fixtures already cover explicit realizers for `pure`, rejection
of unregistered or ill-shaped `ppt` goals, illegal-answer nonconformance,
charging and resolving allowed zero-probability branches, failure on a reachable
empty response, exact structural query accounting, ranked two/adaptive/parity control flow,
`HandlerCertificate` API shape and semantic closing, ElGamal semantic closing, exact complexitylib
pure and one-coin canaries, exact-run output growth, pair-codec incompatibility, and multiple
second-order environments for a fixed-size response. Root validation also covers polynomial
returned-output recovery and bounded dependent `seqComp`. The fixtures do not yet cover
quantitative handler substitution, a usable bounded loop, or a genuinely variable-size oracle
reply. The other bullets remain acceptance targets.

### Anti-cheating tests

- `pure` applied to an arbitrary or noncomputable Lean function has no PPT
  constructor; explicit executable polynomial realizers are required.
- A bind whose continuations merely have pointwise witnesses is rejected until
  one uniform dispatcher realizer is supplied.
- Producing `2^n` output bits forces at least the corresponding output/time
  resource.
- A machine selected independently for each `n` is classified as
  `IsNonuniformPPT`, never `IsPPT`.
- An injective encoding with a cached hard bit cannot construct `PolyCodable` or
  a quantitative encoding-equivalence witness.
- Polynomially many steps that double the state fail the reachable-state-size
  bound.
- A polynomial query bound with exponential local work does not imply PPT.
- A reachable pending query with an empty response type fails `RunsWithin`, even
  when the numeric query budget is positive.
- An unbounded answer length prevents a closed PPT theorem unless supplied
  `OracleContract` bounds control it.
- An arbitrary `PMF` and an unsupported finite uniform sampler do not receive
  `EfficientSampler` instances.
- Expected-time components do not compose through an unrestricted oracle
  substitution theorem.
- Locally PPT reactive nodes can exhibit a rejected superpolynomial ping-pong
  run.

### Positive and semantic tests

- `pure`, precomposition, result mapping, bind, bounded fold, lens transport,
  and handler substitution derive exact resource bounds and polynomial
  corollaries.
- Resource erasure reproduces the existing `FreeM`/`OracleComp` computation,
  typed transcript, `support`, and `evalDist` semantics.
- Existing query tracking is recovered by trace projection.
- Compilation preserves result, complete oracle-call order, typed answers, and
  coin behavior on every path, with a proved overhead.
- A canonical encoding round-trips, and a representation change preserves PPT
  only through proved polynomial transcoders.
- PR #500's diagonal theorem is retained, with attribution, as evidence that
  the concrete class is nontrivial.

### Repository gates

Run the full root build, the nested-package build, targeted negative fixtures,
`scripts/test-axiomsweep.sh`, `lake exe axiomsweep --check`, and the Extern and
Interop isolation checks. New files follow VCVio module/attribution policy. No
new `sorry`, nonstandard axiom, native-trust debt, or dependency from PolyFun or
core VCVio to `VCVioComplexity` is accepted.
