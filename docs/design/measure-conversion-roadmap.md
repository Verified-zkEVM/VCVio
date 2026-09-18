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

## Next conversion batch

The canonical campaign tracker is [issue #532](https://github.com/Verified-zkEVM/VCVio/issues/532).
Shared integration and event laws are published in
[PR #758](https://github.com/Verified-zkEVM/VCVio/pull/758). Continue with independently validated PRs:

1. Finish quantitative Hoare/WP, simulation/lifting, and affected finite-counting proofs through
   upstream operation specifications and core `Std.Internal.Do`.
2. Extend native measure/kernel TV composition with contraction, explicit measurable conditional
   majorants, and exceptional-event bounds.
3. Convert disagreement and the complete PRFTagReader direct-coupling reader/slot/composition
   families with their table/cache dependencies.
4. Convert abort-aware HVZK, ML-DSA simulator/pregate/gating, and affected aborting Fiat–Shamir
   security clients, preserving observable `none` outcomes.
5. Convert Sigma HVZK, exact transcripts, predictability, and challenge uniformity, with Schnorr
   and affected Fiat–Shamir simulation/stateful-hop/security families.
6. Convert Fischlin search/runtime/model/completeness using native products and projections.
7. Convert Fischlin extraction/potential/supermartingale/soundness and delete unused expectation
   declarations.

Reuse independent products in #756 and preserve exact expected signing costs in #752 and Schnorr
transform guarantees in #755. These feature algorithms are not duplicated by conversions.
Record each published checkpoint and its remaining compatibility consumers here and in #532.

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
| Common-prefix lower bound | `le_evalDist_bind_apply` under AE premises and losslessness, or `OracleComp.le_evalDist_bind_apply_of_support` for reachable continuation bounds. |
| Unchanged instrumented output | Structural projection equality, followed by measure observation; final writer/state marginals use measurable projections. |
| Expected cost | Cost-marginal Lebesgue integral on the chosen cost space; measurable valuations and cost functions, native AE/pathwise bridges, and Mathlib probability certificates for lower/exact bounds. |
| Conditional continuation | `evalDist_bind_ite`, `prEvent_bind_ite`, and `prEvent_bind_eq_mul_of_ite`; finite observation measures retain missing mass. |
| Natural-valued expectation | `MeasureTheory.lintegral_coe_nat_eq_tsum`; countability applies to the observable range. |
| Losslessness | Mathlib `IsProbabilityMeasure`; bind requires AE lossless continuations. |
| Conditional measure/event equality | `evalDist_bind_congr_ae` / `prEvent_bind_congr_ae`, with measurable families on the chosen source space. |
| AE output valuation | `lintegral_evalDist_bind_of_aemeasurable` / `lintegral_evalDist_map_of_aemeasurable`, relative to the resulting output measure. |
| Hidden-output expectation comparison | `OracleComp.lintegral_evalDist_bind_mono_of_support`, observing the actual continuation results. |
| Independent hidden-output interchange | `OracleComp.evalDist_bind_bind_swap`, requiring countable actual query answers only. |
| Continuous free-operation tower | `FreeM.lintegral_evalDist_liftBind`, with explicit AE continuation and valuation hypotheses. |
| Every possible execution satisfies an invariant | Operational support or indexed reachability; probability interpretation is unnecessary. |
| Stateful composition | Joint result/state kernels; `StateT.evalDistKernel_bind` threads the resulting state. |
| Relational sequencing | Explicit measurable coupling families, or justified countable/AE selection rules already in the native coupling API. |
| Finite or countable probability calculation | Mathlib sum/integral identities under the actual concentration and measurability assumptions. |

Do not manufacture a discrete measurable space on a general intermediate type to make bind or
WP elaborate. If a proof repeatedly needs `change`, add a public normalization equation or reuse
an upstream equation. A hard conversion can reveal a missing measurable-family premise, an
unjustified support/positive-mass equivalence, discarded state, or an invalid measurable-selection
argument; repair that mathematical contract before introducing adapters.
