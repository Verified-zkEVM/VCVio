# Measurable services, observations, and executable randomness

Exploratory design and literature survey, updated 17 October 2026.

## Why a non-maximal sigma algebra is useful

There are two different reasons, and confusing them obscures the useful examples.

1. **Information restriction.** A finite machine state can have the discrete sigma algebra,
   while the information available to a participant is a much smaller sub-sigma algebra.
   For a view `v : State → View`, it is `MeasurableSpace.comap v inferInstance`.
   An event belongs to it exactly when it is a preimage of a measurable view event.
   In a finite model this says that the event cannot separate states with the same view.
   This is useful for leakage, masking, local party views, nonanticipating schedulers,
   and conditional independence. No continuous sampler is involved.
2. **A law on a complete, potentially infinite object.** A random function on infinitely
   many keys, an infinite fair-bit tape, or an indefinitely running service has a product
   measurable space. Finite-coordinate cylinders generate it. The law can exist even though
   no implementation materializes the complete object. Finite observations, stopping times,
   and almost-sure limits connect the idealization to finite execution.

On a countable space, measurable singletons imply the maximal sigma algebra: every set is a
countable union of singletons. Thus ordinary strings, natural numbers, finite caches, and
finite machine configurations usually lose nothing by being discrete. This does **not** imply
that the space of *infinite sequences* of such configurations is countable or discrete.
The fair-bit-table law here assigns mass zero to every singleton and every countable set of
complete tables. It cannot be represented by a countably supported mass function. This is not
an assertion that cardinality alone rules out every measure on a powerset sigma algebra;
that stronger assertion would raise set-theoretic questions we do not need.

The sigma algebra is also not a class of computationally feasible distinguishers. Polynomial
algorithms are not closed under arbitrary countable unions, and statistical equality on a
public view is different from computational indistinguishability. Keep VCVio's complexity
certificates and adversary classes. Likewise, coarsening observations does not automatically
make the observed process Markov: hidden history may still affect the next observation.

## What this exploration implements

The main reusable interface is a **probabilistic reconstruction of private ideal state**.
For concrete state `S`, ideal state `T`, and a probability kernel `R : Kernel S T`, require

```
ideal q ∘ₖ R = retainLeft Answer R ∘ₖ concrete q.
```

This is an equality of *joint answer/state laws*. Drawing the represented ideal state first
and taking one ideal step agrees with taking the concrete step and then reconstructing its
successor. Retaining the answer is essential. Equal answer marginals by themselves do not
justify a second adaptive query. A deterministic state projection is a special case.

[`Reconstruction.lean`](../../VCVio/ProgramLogic/Relational/Reconstruction.lean) lifts this
local law to every `FreeM` client, shared-state handler inlining, arbitrary initial measures,
and output equality after hiding both private states. Answers are countable with measurable
singletons; private states and client results need not be discrete. This restriction is the
measurability seam for answer-dependent continuations, not a universal theorem about arbitrary
continuous-answer syntax.

The implementation intentionally leaves `OracleComp`'s discrete answer interface intact.
Measurable internal states enter through kernels and `PFunctor` interpretations. Replacing
all continuations by unbundled functions on arbitrary measurable answers would create a
measurability obligation that the current free syntax does not enforce.

### Polynomial syntax, stateful machines, and continuous interpretations

The companion [PolyFun PR #308](https://github.com/Verified-zkEVM/PolyFun/pull/308)
provides the generic syntax/execution layer. VCVio pins its immutable commit
`be5095ef56e623df2bdef93f471600cf5319f088`; normal builds do not require a sibling
checkout. The optional `-KpolyfunPath=/path/to/PolyFun` Lake setting is for local
companion development, and is not used in the committed manifest.

`MachineHandler P Q S` assigns each dependent operation of `P` a returning
`DynComputation` over `Q`. Its dispatcher retains the caller continuation,
shared service state, and the active operation's private state. Entry and return
are explicit unary administrative events. The existing chunk runners therefore
pause within a call and resume without replaying primitive effects. The same
dispatcher accepts arbitrary caller machines; finite clients use `compile`.
`execute_ofFreeM` identifies finite service implementations with the existing
stateful fold, and `execute_liftM` reuses stateful reindexing for interface translation.

| Existing model | Role in this development | Checked bridge |
| --- | --- | --- |
| `FreeM` | Finite adaptive clients, capped optional implementations | Finite measure/kernel folds; machine compilation |
| `DynComputation` | Retained execution phases and injected bit drivers | Dispatch behavior weakly bisimilar to stateful ITree interpretation |
| `Resumption` | Visible-query, potentially infinite behavior | Least continuous measure/kernel interpretation; increasing finite truncations |
| `ITree` | Explicit silent steps and stateful interpretation | Returned measures respect weak bisimulation; silent divergence returns zero |
| `DynSystem`, `M`, `CofreeC` | A continuing adaptive threshold client | Canonical behavior, trajectory, and ITree equations |
| `IPFunctor`, scoped/displayed syntax | Indexed protocols and binding already supplied by PolyFun | Existing fold/reindex/traversal coverage reused; no redundant indexed probability AST |

The measure and kernel continuity proofs support substitution and fixed-point
fusion. The free-to-resumption measure theorem now applies to *every* well-founded
free client, including a client that first receives a natural number and then
performs that many queries. Such a program need not admit any uniform finite
query-depth bound. An ordinary-import regression proves that distinction.

[`KernelHandler.Realizes`](../../VCVio/EvalDist/KernelHandler/Realizes.lean)
is a local joint answer/state contract. It lifts to arbitrary adaptive finite
clients and then to the actual composed machine, through the generic behavior
bridge. The ternary sampler now has both an executable `sampleIO` and a theorem
about the returned law of that exact composed machine. A separate capped handler
produces ordinary `OptionT (FreeM ...)` syntax; the proved error bound applies to
that program, including timeout mass. A noncomputable semantic `ProbResponder`
bundle is not passed into the executable sampler: its computable machine family
and its mathematical certificate are kept separately accessible.

[`KernelAdmissible`](../../VCVio/EvalDist/PFunctorKernel.lean) certifies the
joint measurability of answer-dependent continuation laws on ordinary `FreeM`
syntax. Countable answers receive the certificate automatically. Continuous
answers require an explicit proof. Certified bind/map laws and probability-mass
preservation make the obligation compositional. The
[stateless compatibility theorem](../../VCVio/EvalDist/PFunctorKernel/Stateless.lean)
identifies the certified interpretation with the existing guarded `FreeM.denote`.
The [continuous-answer example](../../Examples/MeasurableServices/ContinuousSyntax.lean)
samples a Borel real, applies the measurable ternary partition, and proves equality
with the fair-bit machine's output law. This is a prototype proof predicate over
existing syntax, not an assertion that every Lean continuation is measurable.

The [reactive threshold example](../../Examples/MeasurableServices/ReactiveThreshold.lean)
continually queries the midpoint of its current dyadic interval. Each completed
call consumes exactly one fair bit and retains the chosen half. Its finite history
clients compile to machines and have the same output law as observation of one
persistent ideal real. The completed-call Markov kernel equals the kernel obtained
by reconstructing the real from the current cell, giving equality of their full
product-space path laws. This path theorem concerns the posterior-reconstructed
completed-call chain. It does not identify equal micro-fuel cutoffs, or construct a
concurrent scheduler. The continuing client's empty return type separately gives
zero returned-output mass, illustrating why a returned law cannot replace a path law.

The stateful machine layer is stacked on PolyFun #290 and integrates #297
(silent-step machines), #298 (continuous-domain interpretations), #299 (indexed
traversal), #301 (execution runners), #302 (transformer bounds), and #307 (dependent
answer elaboration fixes), together with the then-current main branch. The scoped
consumers use the canonical indexed `FoldAlgebra`; the execution runner uses the
canonical silent-step adapter. This avoids maintaining competing abstractions
from the overlapping PRs. The stack remains exploratory and should be split/rebased
as its dependencies land.

### Infinite random functions with finite lazy state

[`InfiniteTable.lean`](../../ToMathlib/Probability/InfiniteTable.lean) constructs the independent
uniform product law, proves its finite restrictions and disjoint-coordinate independence, and
proves the fair-bit table's absence of atoms. Its
[resampling lemma](../../ToMathlib/Probability/InfiniteTable/Resampling.lean) retains the drawn
coordinate alongside the updated table. It works for an arbitrary key type; no finite bound
on all possible keys is needed.

The [lazy-cache reconstruction](../../VCVio/OracleComp/QueryTracking/RandomOracle/InfiniteTable.lean)
fills every uncached key from an independent infinite table. The concrete state is an ordinary
association list, with the same first-binding-wins convention as `QueryImpl.ListCache.handler`.
Its local kernel is proved equal to that existing handler's `evalDist` when supplied with
`SampleableType` draws. The reconstruction law handles arbitrary initial lists, including
shadowed entries, and lifts to adaptive clients. The empty cache represents the full product law.
This complements the existing finite eager-table proofs; it does not replace efficient caching
or the finite query bounds used by reductions.

### A persistent real with an actual bit implementation

The [threshold service](../../VCVio/OracleComp/Coinductive/UniformThreshold.lean) represents a
single uniform real `U ∈ [0,1)` using a finite prefix `(depth, cell)`. A query is a rational
`q`; its answer is `U < q`. The machine returns immediately if its entire dyadic interval lies
on one side of `q`, otherwise it reads a fair bit and halves the interval. It keeps the prefix
for the next query. All execution uses integer/rational arithmetic.

The [posterior reconstruction](../../VCVio/OracleComp/Coinductive/UniformThreshold/Interval.lean)
is normalized Lebesgue measure on the represented half-open interval. The
[correctness proof](../../VCVio/OracleComp/Coinductive/UniformThreshold/Semantics.lean) shows that
successful bounded executions reconstruct a submeasure of the ideal answer/real law. The
missing mass tends to zero, yielding exact reconstruction for the returned kernel and then
for arbitrary adaptive clients. This proves persistence, not just a fresh Bernoulli draw for
each query. Replacing every query by an independent Bernoulli sampler would give the wrong
correlations.

The [cost proofs](../../VCVio/OracleComp/Coinductive/UniformThreshold/Cost.lean) establish, from
*every* retained prefix and rational query:

- probability of needing more than `k` new bits is at most `2⁻ᵏ`;
- return occurs almost surely;
- expected new-bit cost is at most two;
- the cutoff estimate remains true after averaging over adaptive query/prefix choices;
- event bounds `2^{-(λ+i+1)}` give probability at most `2⁻λ` of any timeout over a countable
  session, without an independence assumption.

[`BitRealization`](../../VCVio/OracleComp/Coinductive/BitRealization.lean) packages the executable
machine and its joint returned-law certificate separately from a finite `ProbComp` realization.
The IO driver receives its bit source explicitly. The theorem assumes independent fair bits;
it does not certify an arbitrary IO RNG. Generic chunk/resume laws preserve residual state.
A cutoff is missing successful mass, not renormalized success and not an automatic restart.
The [capped service](../../VCVio/OracleComp/Coinductive/UniformThreshold/Approximation.lean)
instantiates approximate reconstruction with a query- and prefix-dependent cap. The ternary
example proves event-TV error at most `2 · 2⁻ᵏ` when each query is capped at `k` bits.

[`UniformTernary`](../../Examples/MeasurableServices/UniformTernary.lean) uses thresholds `1/3`
and `2/3` on the same persistent real to obtain an exact uniform `Fin 3` output. This ties the
Lebesgue idealization to a small implementable, non-dyadic discrete distribution. A fixed
finite number of fair bits alone cannot give exact probability `1/3`: its output probabilities
are integer multiples of `2⁻ᵏ`. Unbounded almost-sure bit execution or an explicitly bounded
approximation is the relevant implementation bridge. VCVio's existing uniform finite oracle
can already sample `Fin 3`; the new point is a certified realization using fair bits.

The [timing example](../../Examples/MeasurableServices/ThresholdTiming.lean) computes the one-bit
law at threshold `1/3`: half the runs time out, and every run finishing then returns false.
This establishes timing/output correlation; it does not by itself prove additional leakage
when that answer is already public.

The expected-bit bound is **not** a constant-time or PPT theorem. Rational comparisons have
operand-size costs, prefix storage grows, and stopping behavior can reveal information about
answers. The provided tape regressions exercise the compiled generic machine driver, including
cutoff/resume and persistent-prefix behavior; they are not statistical RNG tests.

### Observation and path laws

The [observation API](../../VCVio/Interaction/ObservationMeasure.lean) identifies equality of
pushed-forward view laws with equality of measures trimmed to the view's sigma algebra.
Measurable factoring preserves equality and contracts event total variation. The
[filtration API](../../VCVio/Interaction/ObservationFiltration.lean) records only observations
already made, proves that measurable finite-history decisions use that information, and makes
first publicly observed events stopping times. A scheduler must satisfy that condition; merely
having a globally measurable scheduler does not forbid using hidden or future information.

[`Trajectory`](../../VCVio/EvalDist/Trajectory.lean) supplies infinite laws through Mathlib's
Ionescu–Tulcea construction and identifies their finite-prefix marginals. Equality of all
prefix laws implies full product-law equality. A **uniform** finite-prefix event-TV bound
also bounds every measurable event of the full trajectory. The proof uses approximation by
the generating ring under the finite measure `μ + ν`; it is not an unjustified assertion that
every measurable event is itself a cylinder. A growing `n ε` bound alone need not yield a
useful infinite-horizon estimate.

This layer requires an explicitly measurable transition kernel. It does not assign a new
measurable-space instance to arbitrary resumptions or arbitrary higher-order continuations.
Returned-output measures are already available for resumptions; the new
[machine bridge](../../VCVio/EvalDist/MachineMeasure.lean) identifies finite operational unrolling
and chunk/resume laws with those measures. The
[stopped-observation bridge](../../VCVio/EvalDist/StoppedObservation.lean) proves that any
measurable path model with the supplied finite truncation laws and almost surely persistent returned values
has the corresponding eventual-return events. Its waiting-prefix count integrates to the
resumption tail-sum cost. The premises remain explicit: this does not construct a path model
for arbitrary syntax.

### Two further constructions suggested by the survey

**Expected error charges.** [Approximate reconstruction](../../VCVio/ProgramLogic/Relational/ApproxReconstruction.lean)
allows a measurable state-dependent local event-TV charge. The adaptive client bound is the
expected accumulated charge under the concrete execution, with a potential rule and an
initial-state mismatch term. A
[geometric potential](../../VCVio/ProgramLogic/Relational/ApproxReconstruction/GeometricBudget.lean)
pays for an arbitrary finite client using a counter that advances after each query, and a
uniform-charge corollary recovers the usual query-count bound. This supports expensive rare states, varying per-query sampler
precision, and a principled route from exact ideal samplers to capped implementations. The
[resumption approximation theorem](../../VCVio/EvalDist/ResumptionApproximation.lean) bounds the
distance between finite successful output and the eventual returned law by cutoff mass, and
preserves that bound through any subprobability continuation kernel. Missing mass is included
in this event-TV convention. It is not the unnormalized total-variation norm of a signed measure.

**Conditional views with a named simulator.**
[`ConditionalView`](../../VCVio/ProgramLogic/Relational/ConditionalView.lean) states that a supplied
kernel simulates leakage given permitted public information while retaining the secret. It
supports measurable postprocessing and proves the implication to Mathlib's conditional
independence. Standard Borel/nonempty hypotheses enter at the regular-conditional-distribution
bridge, and conditional laws agree almost everywhere. The
[finite masking example](../../Examples/MeasurableServices/Masking.lean) gives an explicit fair-bit
simulator, verifies a masked share, and proves that the secret is not measurable from that share.
Both shares recover the secret, and their joint observation is proved not independent of it. The distinction already matters on four underlying outcomes.
An arbitrary simulator kernel is not automatically efficiently realizable.

## Ancestry and related work

The assessment below distinguishes formal artifacts, mathematical antecedents, and algorithmic
inspiration. These are not claims of priority based on an exhaustive search.

| Work | Connection and boundary |
| --- | --- |
| [Interaction Trees, POPL 2020](https://arxiv.org/abs/1906.00046) | Direct ancestry for coinductive effectful syntax, interpretation, and equivalence up to silent steps. The dispatch/interpretation theorem is an application of this established approach, not a new semantics of effects. |
| [Niu–Spivak, Polynomial Functors](https://arxiv.org/abs/2312.00990) | Mathematical ancestry for polynomial interfaces, dynamical systems, and interaction. PolyFun's existing lens, coalgebra, and cofree constructions provide these models; VCVio supplies probability and concrete consumers. |
| [CertiCrypt, POPL 2009](https://software.imdea.org/~szanella/Zanella.2009.POPL.pdf), [EasyCrypt](https://easycrypt.gitlab.io/easycrypt-web/docs/reference/) | Mechanized game-based cryptography, probabilistic relational reasoning, and game transformations are established. EasyCrypt's [PRF encryption tutorial](https://easycrypt.gitlab.io/easycrypt-web/docs/tutorials/encryption-from-prf/proof/) is a concrete comparison for lazy oracles. Non-maximal sigma algebras are not necessary for most finite games. |
| [Foundational Cryptography Framework](https://arxiv.org/abs/1410.3735) | Coq development of probabilistic computations, oracle reasoning, and cryptographic reductions. A discrete foundation can support substantial verified cryptography and implementation reasoning. |
| [CryptHOL](https://isa-afp.org/entries/CryptHOL.html) | Isabelle/HOL's probabilistic programs and generative probabilistic values are close ancestors of oracle-oriented semantics. Discrete subprobabilities already handle failure and unbounded probabilistic behavior; unbounded execution is not by itself a reason to abandon them. |
| [Formalizing Constructive Cryptography using CryptHOL, CSF 2019](https://people.inf.ethz.ch/basin/pubs/csf19.pdf) | Particularly close ancestor: mechanized reactive resources, trace equivalence, composition, and a distribution-based proof rule. Section V explains why eager/lazy examples require more than ordinary pointwise probabilistic bisimulation. Our reconstruction kernel is a concrete sufficient rule, not a claim to their sound-and-complete characterization. |
| [SSProve, TOPLAS 2023](https://doi.org/10.1145/3594735), [artifact](https://github.com/SSProve/ssprove) | Modular stateful cryptographic components and relational verification in Coq. Shared-state handler composition belongs in this lineage. |
| [Clutch, POPL 2024](https://cs.au.dk/~birke/papers/clutch-popl24-final.pdf) | Mechanized higher-order probabilistic separation logic with presampling tapes. It addresses the mismatch between eager and lazy sampling through a different, resource-sensitive proof interface. |
| [Eris](https://arxiv.org/abs/2404.14223) | Mechanized error credits, including amortized probabilistic reasoning. This motivates state-dependent expected charges rather than only a worst-case error multiplied by query count. Our kernel inequality is a smaller interface, not an Iris implementation. |
| [Approxis, POPL 2025](https://arxiv.org/abs/2407.14107) | Approximate higher-order relational reasoning, including exact reasoning obtained from approximations and cryptographic examples. The cutoff-to-exact proof strategy has clear precedent. |
| [Continuous-Eris, LICS 2026](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.71), [artifact](https://doi.org/10.5281/zenodo.20114732) | Particularly close sampling precedent: Rocq-verified exact uniform, Gaussian, and Laplace samplers using lazy computable-real digits, with exact real arithmetic and mutable state. Its discrete program logic supports continuous ideal laws. This directly rules out novelty claims for verified lazy exact real sampling and supports keeping the executable interface discrete. |
| [Lilac, PLDI 2023](https://arxiv.org/abs/2304.01339) | Independence and conditioning as compositional probabilistic resources, including continuous distributions. Mathematical/program-logic inspiration; do not infer a machine-checked artifact solely from the paper. |
| [Bluebell, POPL 2025](https://arxiv.org/abs/2402.18708) | Joint conditioning connects relational and independence reasoning. Useful motivation for retaining the secret/public view jointly in a simulation assertion. |
| [Amaryllis, 2026 preprint](https://arxiv.org/abs/2605.13765) | Rocq/Iris development combining independence and conditioning with mutable state. The reported development concerns finite-support terminating programs; it should not be cited as an existing general continuous-measure crypto foundation. |
| [Formal Verification of Probing Security via Conditional Independence, CSF 2026](https://arxiv.org/abs/2605.23316), [conference listing](https://www.ieee-security.org/TC/CSF2026/accepted.html) | Direct evidence that conditional independence and simulation-based probing security are connected. This motivates a reusable public-view simulator API; the paper alone is not evidence that our particular Lean examples or a complete probing calculus already exist. |
| [Zar](https://arxiv.org/abs/2211.06747) | Verified compilation to random-bit samplers in Coq. Strong precedent for separating a probabilistic specification from an executable bit realization. |
| [SampCert](https://arxiv.org/abs/2412.01671), [Lean artifact](https://github.com/leanprover/SampCert) | Verified practical samplers for differential privacy in Lean. Practical verified sampling and real/discrete specification bridges are not new to Lean. |
| [Karney's exact normal sampling](https://arxiv.org/abs/1303.6257) | Algorithmic inspiration for lazy exact real digits and finite observations. The citation is not a formal-verification claim. Our first implementation deliberately uses the simpler persistent rational-threshold service. |
| [Continuous apRHL](https://arxiv.org/abs/1603.01445), [advanced coupling proofs for DP](https://arxiv.org/abs/1606.07143) | Measure-based relational reasoning and coupling arguments have substantial antecedents beyond cryptography. The latter includes EasyCrypt mechanization; continuous semantic generality and mechanization scope must be distinguished. |
| [Task-PIOA](https://people.csail.mit.edu/lcheung/task-pioa/), [EasyUC](https://github.com/easyuc/EasyUC) | Scheduling, information available to schedulers, and composable security are existing research topics. This draft's filtration is a reusable condition, not a complete computational UC scheduling theorem. |
| [Privacy filters and odometers](https://arxiv.org/abs/2203.05481) | Adaptive stopping and accounting are another consumer of filtrations and state-dependent budgets. An event-TV charge is not a replacement for DP's likelihood-ratio/divergence accounting. |
| [Quasi-Borel spaces](https://arxiv.org/abs/1701.02547) | Ordinary measurable spaces do not supply a satisfactory unrestricted higher-order function-space semantics. This is a reason to preserve the explicit kernel/first-order observation seam, not to introduce QBS into VCVio without a concrete consumer. |

The underlying probability is classical: generated sigma algebras, conditional laws,
Ionescu–Tulcea extension, and Markov-kernel intertwining. Rogers and Pitman's
[Markov Functions (1981)](https://doi.org/10.1214/aop/1176994363) belongs to the intertwining
ancestry; no theorem from that paper is assumed here. Mathlib supplies the foundational
measure, kernel, product, trajectory, and conditional-distribution results used by the proofs.

## Novelty assessment

**Established:** lazy/eager sampling, information hiding, probabilistic state relations,
subprobability semantics, almost-sure termination, exact random-bit sampling, conditional
independence, and expected/amortized error budgets. None should be advertised as new inventions
of this branch. CryptHOL's constructive-cryptography development is an especially important
comparison before making a formal-crypto novelty claim. Continuous-Eris already mechanizes
lazy exact continuous samplers in a richer language, making it an equally important comparison
for the sampling part.

**Potentially distinctive engineering contribution:** a common, machine-checked VCVio interface
for probabilistic reconstruction over Mathlib kernels, exercised both by an infinite random
function with finite caching and by a persistent real with rational executable state; plus
adaptive approximate reconstruction, observation filtrations, and public-view simulation.
These pieces make the measure choice useful to an ordinary consumer without requiring their
implementation to manipulate reals or infinite objects. We have not established that this
combination is first in formally verified cryptography. A publishable novelty claim would
require a closer artifact comparison, especially with CryptHOL, Clutch/Approxis, and SampCert.
That comparison must also include Continuous-Eris; this draft's narrower rational-threshold
implementation is useful as a VCVio consumer and proof example, not as a new sampling algorithm.

The result is an exploratory draft. Its value is in a concrete interface and proofs that can
be evaluated and refactored, not in making every game or every sampling primitive continuous.

## Foundation recommendations and upstream comparison

Keep discrete `OracleComp` answers, finite samplers, the existing cost model, and backend-relative
PPT certificates. Add measurable services beside them, with explicit implementations and
refinement contracts. Do not put a blanket `MeasurableSpace := ⊤` on arbitrary types; do not
conflate a party's observation sigma algebra with the full implementation state; do not infer
Markovianity, runtime bounds, or computability from a measure.

At the surveyed snapshot, Samuel Schlesinger's
[cslib PR #1129](https://github.com/leanprover/cslib/pull/1129), head
`4e626b5449d9c93b4ac7028e596e91324ed2f4f1`, is open and uses a PMF evaluator for its finite
uniform free-program specialization. Its free syntax can still have other interpretations.
The PR body refers more broadly to PMF sampling and should not substitute for inspecting that
revision. The separate [measure semantics PR #1089](https://github.com/leanprover/cslib/pull/1089),
head `2f373a69658b9aaccc5a81a5725a05b66f54ea75`, is also open. These are snapshots, not claims
about a settled upstream design.

The strongest case for a shared measure interpretation is the compositional seam demonstrated
here: non-countably-supported *private ideal state*, infinite trajectories, and refinement back
to executable discrete behavior. “We might sample a Gaussian someday” is a much weaker argument.
A PMF-facing API can coexist with that interpretation. VCVio's no-direct-PMF policy is a local
library decision, not a proof that PMFs are inadequate for finite cryptographic games.

## Follow-through and limits of the prototype

The present contracts concern arbitrary terminating free clients and measurable service
transitions. Infinite path results concern finite-prefix marginals of explicitly supplied
kernels. Connecting an arbitrary coinductive client, its first-return path event, the resumption
returned measure, and a public scheduler is a further theorem, not implicit in having all four
objects. Full concurrent/UC scheduler composition is likewise outside this prototype.

The approximate rule exposes a potential condition; consumers still have to prove their
particular potential pays for all reachable adaptive steps. The countable timeout union theorem
likewise requires bounds on the reached-query events in one common session probability space.
It does not silently construct that coupling or certify a restart policy.

The [rejection timing example](../../Examples/MeasurableServices/RejectionTiming.lean) proves
that every finite successful law of the existing four-outcome rejection sampler is completion
mass times its eventual uniform law. This is a cumulative timing/output factorization, unlike
the threshold example's correlated cutoff. A full joint return-time distribution would package
these cumulative results more conveniently.

Useful next consumers are a precision-budgeted reactive protocol beyond dyadic refinement and a finite-field
multi-share refresh/probing example with an explicit observation schedule. The threshold
implementation should be used as an exact sampling example, not as a constant-time primitive.

The next engineering pass can split this draft at the reusable math, reconstruction, execution,
and example boundaries. It should standardize naming and add the strongest consumers before
expanding the generality of continuous answers, higher-order state, or scheduler interfaces.
