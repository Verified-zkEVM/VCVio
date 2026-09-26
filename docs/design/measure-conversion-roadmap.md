# Measure and kernel conversion checkpoints

Mathlib measures are the probability semantics. Closed successful computations denote
subprobability measures; measurably parameterized computations denote kernels. Executable finite
samplers retain their algorithms and carry measure certificates. Operational reachability is a
separate structural notion.

Current upstream already supplies the native sampling, unary/relational WP, measure-coupling,
stateful security, and `Std.Internal.Do` foundations. Continue from those owners rather than
introducing competing assertion carriers, coupling structures, or handler representations.

## First integrated conversion

The initial slice moves structural handler composition, instrumentation, tracing, counting,
logging, finite support, and uniform query implementation into native owners. Cache/programming
handlers, query bounds, enforcement, state invariants/projections, and the signature/MAC/KEM/DEM
definition layer use them directly. `VCVio.Native` exports this surface, and `VCVioTest.Native`
rejects imports of PMF/SPMF and retired compatibility classes.

Core `MonadAttach` and the native measure map law turn pathwise predicates into AE predicates
on the chosen result space, provided the observed event is measurable. This needs neither a
discrete result space nor a probability compatibility class. Shared event bounds after a common
oracle computation need no measurable structure on the unobserved intermediate result. Their proofs induct over actual query answers, using Mathlib
bind and Lebesgue integration. Stateful kernel bind retains the joint result and final state.
Regression proofs use real-valued states with their usual measurable structure and arbitrary
intermediate result types without measurable-space instances.

The scalar tracing/counting/logging corollaries remain in their existing compatibility modules
until their clients migrate. Native owners do not import those modules. This is an import
boundary, not a conversion through the scalar backend.

## Expected cost checkpoint

WriterCost, QueryCost, and CostModel now use the chosen cost space throughout, with native
Measure integrals, measurable output-indexed cost functions, and actual cost-marginal
probability certificates. The structural instrumentation API remains monad-parametric.
Pathwise bounds use lawful attachment to imply AE bounds for measurable observations; no
probability compatibility class is involved. Exact cost needs neither an order on costs nor a
monotone valuation. Structural constant-cost laws also need no attachment. Failure contributes
zero, and constant reachable valuations retain successful mass. Markov bounds observe the cost
marginal without measuring discarded outputs. Algebraic writer tags carry their underlying measurable space.

Fiat–Shamir, aborting Fiat–Shamir, Fischlin, and the FO transforms use these cost rules. Their
other security and probability theorem families remain separate conversions.
A generic Measure tail-sum theorem applies to Nat observables on arbitrary spaces; query counts
specialize it. Measurably parameterized cost measures use `evalDistKernel`, and their expected
valuations are measurable. Native regressions cover continuous cost/output spaces, discarded
outputs without measurable spaces, and vacuous exact cost on a failed computation.

## Conditional branching and aborting Fiat–Shamir checkpoint

Conditional event and measure laws factor through the actual finite observation, retaining
missing mass and leaving discarded intermediate values unmeasured. Measurable selector and
branch families integrate with the existing kernel API on chosen environment/output spaces.
Program instrumentation exposes bind and pure equations, so retry cost proofs normalize
without unfolding handler implementations or inserting `change` steps.

Aborting Fiat–Shamir retry powers, tail recurrences, and geometric bounds use native event
semantics throughout. Exact finite expectations require only a probability certificate on the
abort observation; upper bounds permit failure. No arbitrary commitment, response, or private
state measurable space is imposed. Correctness compares events over the joint signature/cache
execution using reachable continuation bounds, then uses the native Boolean mass partition.
The stateful random-oracle abort premise stays explicit; separately reset stateless attempts do
not establish it. Regressions cover generic monads without attachment, continuous kernel
families, and a failing handler whose zero query-tail mass differs from the zeroth abort power.

## Independent-product checkpoint

`EvalDist/IndepProduct` is a native event/reachability owner exported by `VCVio.Native`.
Finite product measures, observable products, lossy coordinate marginals and integrals, and
measurable product families use Mathlib's `Measure.pi` and kernel products. Coordinate event
equality needs full success mass only in the other factors. Reachability elimination uses
core `LawfulMonadAttach` without an exactness mixin. Event factorization and coordinate
observations require no measurable space on the original payloads.

The two Fischlin product callers use these public laws at their existing scalar observation
boundaries. Their surrounding scalar theorem families remain a separate conversion slice.
The independent-product owner imports no retired probability backend or compatibility class;
its regression module checks that boundary along with real parameter/output spaces and loss
from an unobserved factor. This checkpoint targets `main` independently of the expected-cost
and abort-analysis conversion PRs.

## Chosen-space integration checkpoint

Native tower and map integration admit AE-measurable valuations under the resulting measure.
Continuation families keep their explicit measurable-bind boundary. `evalDist_bind_congr_ae`,
`prEvent_congr_ae`, `prEvent_mono_ae`, and `prEvent_bind_congr_ae` use the chosen source space.
Pointwise observational rules need no source space: their actual measure or predicate observer
supplies a Mathlib pullback space, without inventing discreteness on the hidden payload.

Optional and exceptional successful-output bind uses the full-run observation's pullback to
refine the chosen source space, then transports its measure through the measurable identity.
Neither proof requires an auxiliary discrete space. The same observation principle proves the
native ordered expectation algebra's bind monotonicity.

`OracleComp.evalDist_bind_bind_swap` commutes independent computations whose actual answer types
are countable; arbitrary hidden result types need neither countability nor measurable spaces.
The ML-DSA seed/matrix bridge uses this structural rule. The generic countable swap theorem
retains chosen source spaces with measurable singletons.
`OracleComp.lintegral_evalDist_bind_mono_of_support` compares measurable valuations of different
continuation output types using reachability only on the hidden common draw. Continuous free
operations instead use `FreeM.lintegral_evalDist_liftBind` with explicit AE continuation and
valuation hypotheses. The regression module checks all these native boundaries, including a
Gaussian operation, arbitrary AE valuations, lossy real results, and hidden outputs.

## Observed continuation comparison API checkpoint

`Measure.bind_apply_le_sum_add_lintegral_ae` and
`Kernel.comp_apply_le_sum_add_lintegral_ae` accept arbitrary prefix measures, different reference
output spaces, and AE continuation hypotheses without probability or finiteness certificates.
`lintegral_le_sum_add_lintegral_of_le_ae` owns their common integral comparison argument.
`EvalDist/Monad/Disagreement/Measure` provides the computational comparison facade.
The chosen-space rule integrates an AE conditional bound and a varying allowance without
requiring that allowance to be measurable. Reachable bounds use core attachment and the actual
continuation-measure observation; arbitrary hidden source and continuation payloads need no
measurable space. Constant allowances retain the prefix's success mass. The two-world and
bad-world disagreement rules share this finite-sum argument.

The API is exported by `VCVio.Native` and has an independent native import guard, chosen real
source examples, a Gaussian common measure with real/Boolean kernels, arbitrary AE continuations
under a Dirac measure, unmeasured source/result types, and mixed observed output types.
It is a prerequisite checkpoint for the full PRFTagReader direct-coupling conversion. Existing
scalar disagreement declarations remain with their current consumers until that complete
reader/slot/composition family and its table/cache dependencies migrate. No retiring declaration
is moved or wrapped for the new API.

## Native TV composition checkpoint

Native TV composition is published in [#762](https://github.com/Verified-zkEVM/VCVio/pull/762),
independently based on `main`.

`Measure.etvDist` contracts under measurable subprobability transitions on chosen spaces. Its
bounded-observation law uses Mathlib's layer cake formula, without singleton probabilities,
countability, discrete spaces, or probability-prefix assumptions. Conditional composition accepts
an AE majorant under the actual prefix law; the distance function need not be measurable.
AE-measurable measure families suffice. Kernel composition uses the same measure rules.

Exceptional events cost their prefix mass, and constant good-branch allowances retain the
complement's successful mass. Native computation laws expose these rules under measurable
denoted continuation families. Real-valued bounds require finite majorant integrals, since
`ENNReal.toReal` cannot interpret an infinite bound. Measurability of a parameterized expected
majorant uses Mathlib's existing s-finite kernel integral theorem.

Native regressions use usual real spaces, deterministic continuous transitions, null-set changes,
a half-mass Gaussian prefix, measurable expected majorants, and explicit optional aborts.
The public native facade exports the composition API and checks its retired-import boundary.

## Quantitative WP checkpoint

[PR #761](https://github.com/Verified-zkEVM/VCVio/pull/761) publishes this checkpoint, stacked on #758.

Quantitative Hoare triples, simulation and oracle-signature lifting now interpret configured
answer measures directly. The expectation carrier and transformer laws use core
`Std.Internal.Do`; bounded expectations restrict the existing algebra to `Set.Iic 1`.
The qualitative oracle WP remains structural and requires no probability interpretation.

Chosen-space assertion integrals require measurable postconditions. Mapped assertion integrals,
pathwise bounds, finite answer partitions, and state-discarding simulation leave hidden outputs
and handler states unmeasured. Uniform finite averages are separate laws with native uniform
measure premises on the actual answer space. Composed signatures preserve those chosen spaces.
Public transformer equations and conditional measure equations normalize the tactic rules
without new `change` steps. Cached triples retain their core assertion and WP instances.
Proposition indicators and their monotonicity rule belong to the native Hoare owner;
generalized rewriting works on the assertion-valued event normal form.

The finite query-count bounds in the random-oracle commitment example use native event
observations and pathwise WP comparisons. Fiat–Shamir correctness and quantitative tactic
walkthroughs use those laws. Native import guards check both the Hoare surface and a nonuniform
oracle regression; regression proofs also use real observations and hidden function states.

Retiring relational coupling, scalar probability-equality automation, seeded forking, and the
commitment example's TV theorem remain distinct theorem families. Their required connections
use the existing explicit coherence theorem in their compatibility owners. The native Hoare
and simulation modules do not import PMF/SPMF or probability compatibility classes.

## Dead and orphaned retiring-probability checkpoint

The retirement surface kept for compatibility is the façade itself: `SPMF`, `evalSPMF`/`𝒮[…]`,
`probOutput`/`probEvent`/`probFailure` with their `Pr[…]` notation, and the equations crossing
between `Pr[…]` and `𝒟[…]`. Scalar lemmas survive only while an unconverted consumer uses them.

Declarations with no remaining consumer are deleted rather than deprecated: unused scalar
twins of native lemmas, the unused `SPMFSemantics`/`PMFSemantics` bundles, the ReaderT and
`FinRatPMF.Raw` PMF lifts, the deprecated fork façade, and orphaned lemmas of the scalar
EvalDist, SPMF, uniform-selection, tracing, and query-tracking APIs. Consumers are counted
through proof terms, including the auxiliary declarations that `simp` generates for its lemmas.
Lemmas carrying `simp`, `grind`, `gcongr`, or `aesop` attributes are kept even when orphaned,
since automation can use them without a recorded reference; they retire with the scalar
automation benchmarks. The executable `FinRatPMF.Raw` sampler and its native denotation are
unaffected.

## Measure normal form checkpoint

`simp` keeps measure goals in measure normal form. The façade equations
`evalDist_apply_singleton`, `evalDist_apply_setOf`, and `evalDist_apply_univ` are explicit
rewrites rather than simp rules, so a native proof is never silently turned into a scalar one;
a proof that still reasons in `Pr[…]` crosses with `rw`. The `game_rule` set normalizes
`evalDist_pure` instead of the scalar `pure`/`bind` evaluations. The native support
characterization of probability-one events follows the scalar ones out of the default `grind`
set. The native import guard also rejects `evalSPMF`, the scalar evaluation functions, and the
PMF-backed specification classes.

## Native simulation and congruence checkpoint

`OracleComp.SimSemantics.Measure` states the simulation laws natively for any lawful target
semantics: implementations with equal answer measures simulate every computation to the same
measure, and an implementation denoting each query's configured answer measure preserves the
computation's denotation. The stateful form constrains only the answer marginal from every
state; the service state needs no measurable space, and a warm cache is correctly excluded.
The canonical uniform sampler is such an implementation.

Event and measure congruence after a common oracle computation compare continuations on
structural support, including continuations with different unmeasured output types. Uniform
specifications supply the countability that the bind-swap law needs. Event masses do not depend
on the measurable structure that makes the event measurable, so results proved under the discrete
structure `⊤` apply under any chosen space, such as a Borel structure. Native regressions cover a
hidden counter state, real-valued outputs, and different continuation output types.

## Native probability-equality planner checkpoint

The `vcstep` probability-equality planner recognizes native goals: equalities of `Pr{…}[…]`
events, of applied `𝒟[…]` masses, and of output measures. Swaps rewrite with the native bind-swap
laws, under shared prefixes through measure congruence, and congruence leaves the continuations
on the structural support of the shared prefix. The retiring scalar goals keep their existing
actions. Native Hoare lowering lemmas use `prEvent` names, and the singleton-output variants,
which are the events `(· = x)`, are removed. `VCVioTest/NativeProbabilityTactics.lean` gates the
native `simp` and planner contract and records the remaining `simp` gaps.

## Import-closure checkpoint

Modules that import a retiring hub (`SampleableType`, `ProbComp`, `OracleComp.EvalDist`,
`LoggingOracle`, `SubSpec`, `Replicate`, `UniformCompatibility`, the bundled-semantics and
random-oracle simulation modules, `SecExp`) but use none of its declarations import the hub's
native owners instead. `SecExp` itself imports only what `BoundedAdversary` needs, and its clients
import the scalar modules they use explicitly. `scripts/check-spmf-closure.py` keeps the exact set
of modules whose imports reach the SPMF backend; this checkpoint takes it from 455 to 390 of the
tracked proof-library modules. Final removal deletes the modules in that closure's core and
regenerates the umbrellas.

## Leaf example checkpoint

Self-contained examples are native end to end: ElGamal and hashed ElGamal (correctness, the
real-branch game identity, the uniform-masking random branch, and the IND-CPA bounds), BR93,
the reactive OTP separation tests, the UC observation success probabilities, and the optional
failure example. Their game hops use the native bind-swap and support-congruence laws on output
measures, and several hop lemmas are strengthened from `true`-event equalities to equalities of
output measures. `simp` evaluates the Boolean sample space `{false, true}` under any probability
measure. Scalar lemmas that only these examples used are removed with them.

## Symmetric-encryption checkpoint

`SymmEncAlg` states correctness and perfect secrecy with output measures over any lawful measure
semantics. Correctness is a Dirac round trip; perfect secrecy has the channel form (equal
ciphertext rows) and the independence form (the joint law of a lossless message sampler is the
product of its marginals), and equal rows imply independence. Shannon's theorem is ported: a
uniform key and deterministic encryption that is bijective in the key give uniform, hence equal,
ciphertext rows. The posterior and joint-factorization restatements of independence are removed,
as is the compatibility bridge to the scalar predicates. The one-time pad proves both forms
directly from its measure laws.

## State-separating equivalence checkpoint

State-separating packages compare handlers by `MeasureDistEquiv`: equal output measures for
every client, with the `≡ᵈ` and `≡ᵈ₀` notation. A handler step that agrees with another after
transporting its state along a bijection gives an equivalence (`of_step_bij`), and parallel
composition is congruent in both components under uniform measure specifications
(`parSum_congr`). Distinguishing advantages are read off equivalences directly, so the scalar
equivalence and advantage modules are removed. The heap one-time pad proves its single and paired
encryption equivalences from the uniform-mask bijection, and the ElGamal state-separating proof
states its random-branch swap as a measure equivalence.

## Cell-frame and instrumentation checkpoint

Support-level cell frames determine event probabilities under any lawful measure semantics:
a preserved cell changes with probability zero and keeps its value with the full successful
mass, and the except-event, relational and measured frames give the corresponding event
bounds. Interpreted handlers reach these through the support frame of the simulation, so the
per-handler probability restatements are removed. Support-reachability congruence and zero
events are generic over monads with lawful attachment, replacing their oracle-computation
copies. The instrumentation combinators document their transfer principle at the projection
equation, and the scalar corollaries of that equation are removed with their façade module.

## Query-instrumentation checkpoint

Counting, logging and trace instrumentation are covered by their native core modules: the
projection equations identify the uninstrumented execution, so output measures and events
transfer by rewriting, and the scalar failure, output and event corollaries are removed with
their compatibility modules. The lazy random oracle's probability-one characterizations are
stated as `Pr{…}` events: an event holds almost surely exactly when it holds for every total
answer table extending the starting cache, and the mixed form keeps uniform queries
probabilistic. Merkle-tree completeness is stated in that form. The combined-signature
coercion façade is removed, so modules that only need the canonical inclusions no longer
import the discrete hubs; the two consumers that use discrete lemmas import them directly.

## Random-oracle collision checkpoint

The random-oracle collision family is native under uniform measure specifications. A single
uniform query assigns an event the proportion of satisfying answers, which drives the log and
cache birthday bounds, fresh-query uniformity, and the cache preimage and finite-target hit
bounds. Collision resistance in the random-oracle model fixes the discrete answer space and the
uniform specification inside its advantage. The adaptive-prefix, Merkle extractability,
multi-checkpoint extractability, and commitment binding and extractability bounds are stated as
`Pr{…}` events with measurable-answer binders. Unpredictability of a sampler is a pointwise
`Pr{…}` bound. The universe-polymorphic statements are specialized to `Type`, where the event
form lives, and the vacuous single-oracle collision bounds are removed.

## Diffie-Hellman checkpoint

The discrete-logarithm, CDH and DDH relations are native. The DDH game is a uniform-bit branch
over its real and random experiments at the level of output measures, the CDH-to-DDH reduction
runs the CDH experiment exactly in the real branch, and in the random branch it hits the target
with the uniform baseline probability. The DLog-to-CDH bound squares the success probability
through two independent DLog attempts. A continuation event with a constant probability keeps it
after any lossless draw.

## Primitive-notion checkpoint

Correctness spread, commitment hiding and extractor setup consistency are stated with output
measures: δ-correctness bounds the mass of a failed round trip, γ-spread bounds each ciphertext
event, and hiding and setup consistency compare distributions under the discrete measurable
structure. KEM–DEM correctness composes at the level of reachable outputs and transfers to
probability one under uniform oracle semantics. The Pedersen commitment is perfectly hiding by
the uniform bijection law and binding by a DLog reduction on a shared base program; the PRF-based
MAC bound and Falcon's discrete-Gaussian sampler law use native events. The lattice sampling
instances import only the sampling class, which removes the lattice stack from the discrete
import closure.

## Second import-closure checkpoint

Modules that use no discrete declarations import the native layer directly. The stateful
simulation compatibility module is removed, since its one congruence has a native twin; query
morphisms, bit-vector sampling, and the clean importers of the remaining hubs no longer pull in
the discrete layer. Together with the lattice sampling change this takes the SPMF import closure
from 357 to 227 modules, including the random-oracle simulation and the SLH-DSA stack.

## Scheduling checkpoint

Proportional UC scheduling is native: the output relation compares measures under the discrete
measurable structure and reads, on countable outputs, as pointwise agreement of `Pr{…}` point
events; slot draws, binary and flat choices, and the coherence laws are computed with finite
bind sums. The oracle runtime observes the native output measure of the simulated run. Events of
pure computations and of binds over finite draws have native equations.

## Deferred-sampling checkpoint

The first-fire and deferred-sampling kernels are native. A hidden target probed by `q` adaptive
reads fires with probability at most `q · ε` by an event union bound, the multi-key game adds one
such term per key, and averaging over a random key count integrates the count against its output
measure. The output-irrelevant draw deferral is an instance of the bind-swap law. The list
multiplicity kernel integrates the count against the key marginal, tape factorization compares
output measures under the discrete structure, and state-relation transfer is stated for
lintegrals through simulated runs. Discrete bind laws already covered by native swap, lossless
prefix and congruence laws are removed.

## Uniform-selection checkpoint

Uniform selection has native event formulas: selecting from a nonempty vector or list vector,
and through the optional monad from a list, finset or multiset, gives an event its proportion of
entries, an empty collection contributing no successful mass; a uniform range and a fair coin
give an event its proportion of admissible values. The discrete selection lemmas remain only
while the legacy tactic benchmarks exercise them. Two orphaned scalar lemmas are removed.

## Indicator-triple checkpoint

The indicator-postcondition relational triple, which restated the coupling-based `RelTriple`
through `eRelWP`, is removed together with its bridges, its effect rules and the finite-support
compactness development that proved its equivalence with coupling existence. Trace
noninterference is stated with `RelTriple`. The zero-error approximate equality coupling
identifies output distributions through the total-variation characterization, and the coherence
file keeps the direction in which a supported coupling gives the indicator full relational mass.
The converse returns with the measure-backed rebase of `eRelWP`.

## Qualitative relational checkpoint

`CouplingPost` is a measure coupling of the two output laws, each observed in the discrete
structure on its output type, under which the relation holds almost everywhere; `RelWP` and
`RelTriple` keep their names and the sequential rule needs finite response types. The anchoring
instance and the query bijection rule assume uniform response measures, under which every
reachable output has positive mass. The second oracle-level coupling interface is folded into
this one. Equality couplings give equal output measures and equal event probabilities, and an
implication along a coupling bounds one event by another. Game equivalence compares output
measures in the discrete structure, and the advantage bound measures the distance of the `true`
mass from one half, transported by measure total variation. Trace noninterference, trace leakage
freedom and leakage bounds are native, as are the coupling rules for simulated computations and
the stochastic-dominance rules for bad-state events; identical-until-bad bounds stay on the
discrete layer for now. Coupling-existence coherence with `eRelWP` returns with its rebase.

## Quantitative relational checkpoint

`eRelWP` is the supremum of coupled `lintegral` expectations over couplings of the two output
measures observed in the discrete structure. A coupling of oracle computations concentrates on the
finite product of their supports, so its expectation is a finite sum; exchanging the supremum with
that sum and choosing conditional couplings on the support gives the bind rule. A `pure` side
collapses `eRelWP` to the unary expectation of the other side, and the graph of a bijection
couples a uniform sample or query with itself, with the unary expectation along the bijection as
its value. The total-variation characterization of `eRelWP` on equality returns once the maximal
coupling of output measures is available. The discrete subprobability coupling module is removed,
and the public-projection total-variation bound used by the stateful Fiat–Shamir hops sits beside
the discrete event bound it refines.

## Maximal-coupling checkpoint

Two probability measures concentrated on a common finite set have total variation equal to one
minus their overlap `∑ a, min (μ {a}) (ν {a})`. No coupling puts more than the overlap on a
diagonal point, and the maximal coupling, which puts the overlap on the diagonal and spreads the
residual masses independently, attains it. For oracle computations this identifies measure total
variation with the complement of the best coupled probability of equal outputs, so an approximate
equality coupling with error `ε` is exactly a total variation bound `ε`, and a zero-error one gives
game equivalence.

## Identical-until-bad checkpoint

The fundamental lemma of game playing is native. Two stateful handlers that give every event the
same probability on steps between good states, and that keep bad states bad, produce simulations
that agree on every event away from a bad final state; their output-state pairs, and hence their
outputs, are within the probability of ending in a bad state in measure total variation. The
handlers may disagree on the step that sets a bad flag, and they may run in a different oracle
specification than the simulated program; agreement off bad input states, as equal runs or equal
output measures, is a special case. Two computations that agree on every event away from a bad
event are within its probability after any post-processing, with no measurable structure on the
outputs. The programmable-oracle bounds, the random-oracle bridge and the query-bounded
exact-output transport are native, and `by_upto` targets the native bound; the ε-slack
refinements and their consumers remain on the discrete layer.

## Next conversion batch

The canonical campaign tracker is [issue #532](https://github.com/Verified-zkEVM/VCVio/issues/532).
Shared integration is published in #758; quantitative WP in #761; native TV composition in #762.
Compact native event formatting is published in #763. The observed continuation comparison API
is published in #764 as a separate prerequisite for the next complete reader conversion.
Continue with independently validated PRs:

1. Convert the complete PRFTagReader direct-coupling reader/slot/composition families and their
   table/cache dependencies through the native disagreement API, then delete unused scalar
   disagreement declarations.
2. Convert abort-aware HVZK, ML-DSA simulator/pregate/gating, and affected aborting Fiat–Shamir
   security clients, preserving observable `none` outcomes.
3. Convert Sigma HVZK, exact transcripts, predictability, and challenge uniformity, with Schnorr
   and affected Fiat–Shamir simulation/stateful-hop/security families.
4. Convert Fischlin search/runtime/model/completeness using native products and projections.
5. Convert Fischlin extraction/potential/supermartingale/soundness and delete unused expectation
   declarations.

Independent products (#756), exact expected signing costs (#752), and reader cache representation
(#760) have landed. Preserve their algorithms and Schnorr transform guarantees in #755. These feature algorithms are not duplicated by conversions.
Record each published checkpoint and its remaining compatibility consumers here and in #532.

## Subsequent campaign work

| Slice | Scope and API checkpoint |
|---|---|
| General measure reasoning | Chosen-space expectation, measurable and AE-measurable composition, native finite/countable sum bridges, concentration and full-support certificates; compiled recipes and representative client proofs. |
| Tracking and constructions | Writer/query expected costs, tails and stopping rules, remaining simulation and traversal probability families; pathwise bounds imply AE bounds for measurable events. |
| Program logic | Finish direct core predicate-transformer integration and measurable fixed-program WP; quantitative and relational rules use native measures and explicit measurable joint kernels. |
| Security and games | Convert reductions, games, advantages, asymptotic packaging, and necessary lattice/hash/example clients by theorem family. |
| Statistics | Native total variation, divergence, expectations, concentration, and independent product rules through Mathlib owners. |
| Forking | Seeded and replay forking after their tracking and relational prerequisites pass validation. |
| Fiat–Shamir | Convert complete theorem families, including abort bounds and their downstream scheme proofs. |
| Fischlin | Convert cost, completeness, and soundness together with all affected clients. |
| Retirement | Delete unused scalar backends, compatibility classes, and fallback instances; finish required downstream conversions and empty the retired-probability ledger. |

PRs may cover broad independent theorem families once their shared APIs are established. Validate
each family before expanding to another subsystem. Publish a complete checkpoint before opening
the next family. Start from current `main` and keep necessary stacked dependencies explicit;
merge-queue management is outside this batch. Reconcile landed dependencies before retargeting
so the diff contains only the next family. Each published checkpoint must build all
proof libraries, pass native import guards, tests, boundary/style/environment checks, and the
axiom/initialization ratchets. Prune obsolete lint entries; do not add exceptions for conversions.

## Standard proof conversion

| What the proof establishes | Native representation and rule |
|---|---|
| Equality of output distributions | Equality of `Measure`; public handler projection equations or `evalDist_bind_congr_of_support`. |
| Event probability | `Pr{...}[...]`, or measure application to a measurable event; singleton results require measurable singletons. |
| Common-prefix upper bound | `evalDist_bind_apply_mono` under measurable continuation kernels, or `OracleComp.evalDist_bind_apply_mono_of_support` for oracle reachability premises. |
| Conditional additive comparisons | `prEvent_bind_le_sum_add_lintegral_ae` on a chosen source, or `prEvent_bind_le_sum_add_mul_mass_of_support` using attachment and successful mass. |
| Common-prefix lower bound | `le_evalDist_bind_apply` under AE premises and losslessness, or `OracleComp.le_evalDist_bind_apply_of_support` for reachable continuation bounds. |
| Unchanged instrumented output | Structural projection equality, followed by measure observation; final writer/state marginals use measurable projections. |
| Expected cost | Cost-marginal Lebesgue integral on the chosen cost space; measurable valuations and cost functions, native AE/pathwise bridges, and Mathlib probability certificates for lower/exact bounds. |
| Conditional continuation | `evalDist_bind_ite`, `prEvent_bind_ite`, and `prEvent_bind_eq_mul_of_ite`; finite observation measures retain missing mass. |
| Natural-valued expectation | `MeasureTheory.lintegral_coe_nat_eq_tsum`; countability applies to the observable range. |
| Losslessness | Mathlib `IsProbabilityMeasure`; bind requires AE lossless continuations. |
| Common-transition TV contraction | `Measure.etvDist_bind_le` / `Kernel.etvDist_comp_le`; measurable subprobability transitions on the chosen spaces. |
| Conditional TV composition | `Measure.etvDist_bind_bind_le_lintegral` / `measureETVDist_bind_bind_le_lintegral`; AE majorants, without assuming measurable conditional TV or selecting couplings. |
| Different prefix and transition laws | `Measure.etvDist_bind_bind_le_add_lintegral` / `Kernel.etvDist_comp_comp_le_add_lintegral`; charge prefix TV and the conditional majorant under the second prefix law. |
| Exceptional conditional TV | `Measure.etvDist_bind_bind_le_of_bad`; retain exceptional prefix mass and the good complement's mass. |
| Conditional measure/event equality | `evalDist_bind_congr_ae` / `prEvent_bind_congr_ae`, with measurable families on the chosen source space. |
| AE output valuation | `lintegral_evalDist_bind_of_aemeasurable` / `lintegral_evalDist_map_of_aemeasurable`, relative to the resulting output measure. |
| Hidden-output expectation comparison | `OracleComp.lintegral_evalDist_bind_mono_of_support`, observing the actual continuation results. |
| Independent hidden-output interchange | `OracleComp.evalDist_bind_bind_swap`, requiring countable actual query answers only. |
| Continuous free-operation tower | `FreeM.lintegral_evalDist_liftBind`, with explicit AE continuation and valuation hypotheses. |
| Every possible execution satisfies an invariant | Operational support or indexed reachability; probability interpretation is unnecessary. |
| Stateful composition | Joint result/state kernels; `StateT.evalDistKernel_bind` threads the resulting state. |
| Independent joint events or tuple equality | `prEvent_forall_coord_mOfFn`/`mPi` and `prEvent_eq_mOfFn`/`mPi`, with no payload measurable-space premise. |
| Coordinate observation or expectation | `evalDist_map_eval_mOfFn_eq_smul`/`mPi_eq_smul` and `lintegral_evalDist_mPi_coord_eq_mul`; retain other factors' success masses. |
| Independent observable family | `Fin.mOfFn_map`/`Fintype.mPi_map`, then `evalDist_map_coord_mOfFn`/`mPi` on the chosen observation space. |
| Parameterized independent family | `measurable_evalDist_mOfFn`/`mPi`, then `evalDistKernel` on the chosen parameter space. |
| Relational sequencing | Explicit measurable coupling families, or justified countable/AE selection rules already in the native coupling API. |
| Finite or countable probability calculation | Mathlib sum/integral identities under the actual concentration and measurability assumptions. |

Do not manufacture a discrete measurable space on a general intermediate type to make bind or
WP elaborate. If a proof repeatedly needs `change`, add a public normalization equation or reuse
an upstream equation. A hard conversion can reveal a missing measurable-family premise, an
unjustified support/positive-mass equivalence, discarded state, or an invalid measurable-selection
argument; repair that mathematical contract before introducing adapters.
