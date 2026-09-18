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

## Subsequent PRs

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
each family before expanding to another subsystem. Prioritize landing the current core PRs before
opening further conversion slices. After each merge, reconcile dependent branches with current
`main`, retarget their PRs as needed, and validate the resulting integration. Follow every check
on the current head and the merge queue through to the actual merge result.
Since `main` uses squash merges, bring its landed commit into each dependent branch before
retargeting the PR to `main`, so the diff contains only the next conversion family.
Each published checkpoint must build all
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
