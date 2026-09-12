# Polynomial composition as cryptographic evidence

This work starts with PR consolidation, followed by three dependent milestones. A milestone is complete only when its concrete
consumer uses the new theorem, the stated assumptions are checked, and validation passes.

1. **Probabilistic wiring.** Compose measurable conditional couplings and subcouplings over
   initial state laws. Interpret the existing polynomial wiring and displayed-handler APIs;
   retain explicit measurability and unmatched mass. Refactor the PRF tag/reader proof into
   local contracts without changing its loss. Exercise reuse with cached/eager random oracles
   and a continuous kernel example.
2. **Routed bounded execution.** Give unquotiented open syntax actual FIFO packet delivery,
   stable component identities, explicit schedules and bounded adaptive clients. Prove
   observation-relative factorization, then use the PRF network's transcript and verdict as
   the contextual-security consumer. Structural activation equivalence alone is insufficient.
3. **Resource closure.** Construct an executable caller/handler phase machine with bounded
   administrative iteration, a uniform dependent dispatcher and derived prefix/resource bounds.
   Instantiate it for the ElGamal reduction and an inhabited variable-size exact backend.

The first source of constructions is the polynomial-functor literature, particularly
[Niu and Spivak's *Polynomial Functors*](https://arxiv.org/abs/2312.00990), its treatment of
substitution and systems, and the existing PolyFun implementations of wiring, displays and
responders. Evidence must connect each construction to a theorem and a cryptographic consumer;
neither a second notation for handlers nor an assumed bound on the completed machine suffices.

## Baseline and ownership

The implementation starts at VCVio `6d5c7d502ad97f676293a84c3d364c518cbde117`, with locked PolyFun
`c0c923693fc827a41d17116579a0c16ed4873b19`. The sibling PolyFun checkout has divergent history and
does not contain the locked resource API. Generic additions must preserve that API. Probability
and security statements belong in VCVio; generic polynomial constructions belong in PolyFun.
Dependency caches are not development checkouts. Coordinated pins need published commits.

Remote PolyFun main at `31773b17a2c4c9d884c43cd34eb9365b2bb4deb9` is 35 commits ahead of
the locked revision and preserves its resource APIs. It includes generic routing hooks, sampler
equivalence and quotient/factorization infrastructure. These are prerequisites to reuse, while
typed packet delivery and its cryptographic semantics remain obligations.

## Consolidation before implementation

The user authorized review and merge of ready drafts as well as non-drafts, focusing on quick wins
and prerequisites. Review candidates in this order within their dependency chains:

- VCVio #704 and #662: StateT lift priority and signed fixed-point multiplication.
- PolyFun #196–201: lint configuration, conversion, universes, warning tests and notation.
- VCVio #702: separate substantive review of source splits, public APIs and lint orchestration.
- VCVio #686 → #687 → #690 → #693 → #694 → #695 → #696: overlapping measure foundations,
  eager tables, observations and structural invariant proofs.
- PolyFun #202 → #203, then VCVio #572: constructor/path APIs, finite-prefix accounting and
  proportional scheduling, using a consolidated published pin.
- Refresh VCVio #684 against the resulting source and validation drivers.

Use isolated review checkouts and preserve stack references. A merge requires review of the
actual delta, applicable regression tests, fresh checks on the candidate base, and a head-SHA
guard. Squash each eligible PR and replay only each child's unique commits. Do not count a title,
draft promotion, or a clean mergeability indicator as review evidence. Defer unrelated substantial
security developments and the Lean 4.34 upgrade. The original feature checkout and paper edits
remain separate from review checkouts.

| PR | Established evidence | Result |
| --- | --- | --- |
| VCVio #704 | Both lift-path regressions pass; the first fails on the original priority. Full build, lint, tests, boundaries and axiom checks pass. | Merged as `5631dd303276da8c24386a4dd128dd1127feb4bf` through the merge queue. |
| PolyFun #196 | Upstream option defaults and absent-baseline handling checked. Full validation and source-style checks pass, with zero axiom/sorry debt. | Merged as `88a795eca4fef79726fc4696e57cc476227f7e05`. |
| PolyFun #197 | Reviewed the uniqueness/injectivity split and Boolean information-loss counterexample. Full validation, ordinary VCVio source consumers and fresh rebased CI pass. | Merged as `e0a5c7724944416d884a6d03ac4399233cb1a8b7`. |
| PolyFun #198 | Removed obsolete universe-check suppressions while retaining independent universe parameters. Full validation and source-style checks pass. | Merged as `0d7c5b5fa9c4ff302e291a3e566e3159a0d1b891`. |
| PolyFun #199 | Compatibility tests now assert the exact expected deprecation warnings. Full validation and source-style checks pass. | Merged as `80538e6df89035eac3216a1f370dc668d60405fd`. |
| PolyFun #200 | Five `mvcgen` warnings are asserted in tests instead of suppressed. Full validation and source-style checks pass. | Merged as `7ee80169dcc966d9a6e52a6ef5c1a16de65758c0`. |
| VCVio #662 | Reference signed shifts checked; 4,385 product/square tests agree with exact integer arithmetic, while the original code fails. Full validation passes on current-main contents. | Merged as `91cbdae0694dca614dc7be9e4a0c044fc7ee898c` through the merge queue. |
| VCVio #702 | Reviewed lint orchestration and API migrations; resolved the Falcon test rename conflict. Combined candidate passes full validation and the 4,385 arithmetic checks. | Merged as `ffc3e8bc49444380b979ebf0ea0831afe5c8c43b` through the merge queue. |

| PolyFun #201 | Full validation, source style, ordinary VCVio imports, and fresh CI pass. Composition operands and parenthesization checked. | Merged as `328218a25b2a6139925ebc95732ef49903e9ba99`. |
| PolyFun #202 | Constructor normal forms and public path observations reviewed with the published cslib prerequisite and its tests. Full validation and fresh CI pass. | Merged as `a137b66c4d894e1a6faa7abaa0cbc4c1a6aef62d`. |
| PolyFun #203 | Prefix concatenation, query budget, trace witness and cost erasure reviewed. Full validation and fresh CI pass, with zero trust debt. | Merged as `988a1ab00bf3fe8da73c648757033548586f45d4`. |
| VCVio #686 | Measure/cost congruence rules and their positive/negative tactic tests pass in the full integration and fresh CI. | Merged as `82252d8344519961f63163247b68bfe8257433c7`. |
| VCVio #687 | Full combined validation and fresh CI pass. | Merged as `17771926df735157a98f8d5ef2d0a48df2fe816b`. |
| VCVio #690 | Full combined validation and fresh CI pass. | Merged as `841fae0553ab796822ab88c0756e37c8f12b3ccd`. |
| VCVio #693 | Full combined validation and fresh CI pass. | Merged as `9788aa7150b5c0abbce59f6fc33fcda245b7676b`. |
| VCVio #684 | Verified source branches and refreshed documentation and validation instructions; documentation checks and CI pass. | Merged as `3ecdb0a606a874d7d2332a18d966af3570eca82b`. |
| VCVio #694–696 | The combined stack passes full validation: 18,243 declarations across 594 modules, 40 existing sorry-tainted declarations, zero nonstandard-axiom taint. | Rewritten heads are receiving fresh checks after intervening main changes. |
| VCVio #572 | Consolidated PolyFun pin, positive-natural scheduler masses and constructor API integration pass full local validation and optional backend checks. | Current-main integration validation is running before publication. |

GitHub's native stacked-PR merge endpoint rewrites and retargets descendants automatically.
Preserve the original references, fetch each rewritten head, compare its complete source tree,
and use its fresh CI results before requesting the next merge. A pending asynchronous request
or merge-queue entry is not a completed merge.

## Evidence ledger

| Construction | Required evidence | Consumer | Status |
| --- | --- | --- | --- |
| Sequential substitution | Measurable coupling bind, explicit residual mass | State-law handler contracts | Validated; PRF reader discard uses the residual rule |
| Indexed wiring | Local contracts imply a whole wired-program bound | PRF tag/reader, cached/eager oracle | Kernel contracts and Gaussian wiring validated; full PRF wiring contracts remain |
| System composition | Routed execution transports schedules, packets and samplers | Bounded PRF network | Pending |
| Quantitative substitution | Executable normalization and derived resource bounds | ElGamal and exact-backend canary | Pending |

## Acceptance boundaries

- Almost-everywhere probability claims and all-branch displayed invariants are different APIs.
- A shared service has one state, including when several wires reference it.
- Unequal successful-output mass requires subcouplings; exact couplings force equal mass.
- Eager hidden randomness is related through state laws, not an invalid pointwise small bound.
- Schedule correspondence is explicit. Rebracketing nested fair choices changes probabilities.
- Fuel counts activations/deliveries, including administrative work and pending requests.
- No general asynchronous fairness, full machine adequacy, or unproved productivity claims.
- Preserve existing proof attribution and security assumptions; introduce no trust debt.

## Validation

Build each affected module during development. Regenerate import umbrellas after adding files.
For each completed milestone run the repository validation, lint, test and axiom checks, and the
corresponding checks in any changed PolyFun checkout. Record concrete results and remaining
obligations here before updating paper snippets or pins.

## Implemented probability foundation

`Coupling/Bind.lean` composes explicit measurable joint families under almost-everywhere marginal
laws. `Coupling/Residual.lean` propagates unmatched left mass and proves one-sided event bounds
with a separate joint bad event. `MeasureProgramLogic.CouplingPost.bind` and `relWP_bind` expose
this through the existing relational logic without assuming measurable choice.

`Examples/ProgramLogic/MeasureCoupling.lean` applies the rule to shared Gaussian noise and
arbitrary initial state laws, and checks propagation of entirely unmatched mass through a
possibly lossy continuation. These modules compile on the original pinned dependencies. This
is foundation evidence only: the wired PRF proof, cached/eager reuse, and contextual and resource
milestones are still required before strengthening the paper's claims.

## Validated kernel and wiring checkpoint

`FreeM.runKernel` interprets countable query answers with arbitrary measurable private states.
It preserves subprobability bounds and sequential handler substitution. Its state-transport and
almost-everywhere invariant theorems prove both marginals of `KernelHandler.CouplingContract`.
Those contracts extend through free handlers and the existing `PFunctor.Wiring` syntax, including
arbitrary coupled initial-state measures. This common-answer contract does not assert a
pointwise coupling for eager hidden tables.

`Examples/ProgramLogic/GaussianWiring.lean` instantiates the rule with a two-port box whose ports
share one continuous Gaussian state service. The sequencing theorem threads the successor state
from the first call into the second; recursive networks preserve the offset under initial laws.

The explicit discard subcoupling keeps the rejected region as residual mass. The PRF reader's
asymmetric-discard proof uses its measure-semantic rule, and the headline direct-coupling theorem
compiles with the original loss and assumptions. `RandomOracle/Wiring.lean` transports the
cache-parametrized lazy/eager measure equality through recursive wiring; its eager randomness
remains in the initial table law.

Full validation (`./scripts/validate.sh --lint --test --axioms`) passes at this checkpoint:
18,338 declarations across 608 modules, 40 existing sorry-tainted declarations and zero
nonstandard-axiom taint. The log is `/private/tmp/vcvio-kernel-wiring-validation.log`.
This is a checkpoint within milestone 1. Local contracts for the complete PRF wiring, the bounded
routed network and executable resource closure are still implementation obligations.
