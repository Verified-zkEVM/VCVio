# Static computational UC campaign

Status: implementation in progress, September 13, 2026. The semantic requirements in
[uc-semantics.md](uc-semantics.md) govern this campaign. The earlier
[composition evidence ledger](polynomial-composition-evidence.md) records the completed
foundation and its counterexamples.

## Completion contract

The endpoint is static computational UC derived from actual routed execution, with executable
simulators, admissible contexts, and proved resource closure. It requires both modular OTP and
PRF consumers of the shared composition theory and one verified variable-size OTP/simulator
path through a concrete machine backend. The generic theorems stay backend-relative.

The first network model fixes its finite topology and adversarial boundary before private setup.
The OTP consumer assumes honest endpoints, private fresh pads, and an authenticated public
channel. Its extension separates sender, channel, delivery adversary, receiver, and environment,
including an adversary/environment backchannel and statically indexed sessions. Dynamic
corruption, spawning, measurable infinite trajectories, and conventional ITM equivalence have
separate evidence gates.

## Implementation sequence

1. **Consolidation and upstream audit.** VCVio #711 merged as
   `825a8ead8e7c319011fd8ef0af5804b609a0ce16` after all head checks passed and the merge queue
   completed. Its PolyFun foundation is #209 at `2116a47ea3aaefde403cff05584e1a21d56cf107`.
   Historical #494 is closed as an archival design snapshot, with its branch retained.
   Review remaining PRs for prerequisites and duplicate results; isolate dependency upgrades.
2. **Routed composition.** Compile existing raw open syntax to finite typed diagrams; select
   the global environment at closure. Prove map/par/wire/plug factorization with component,
   queue, state, and schedule transport. Extend the serial FIFO/token theorem to all finite
   prefixes, retaining delivery cost. Give identity wires actual charged forwarding behavior.
3. **Operational security.** Add structural simulator processes and runtime-derived real/ideal
   experiments. Prove graded composition and operational dummy-adversary factorization.
   Quantify `∀ uniform adversary, ∃ uniform simulator, ∀ uniform environment`, with simulator
   code fixed before the environment, security parameter, and setup. Negligibility is per
   adversary/environment pair. Preserve return, abort, and unfinished observations.
4. **Cryptographic consumers.** Derive separated-actor OTP from the shared theory; relate its
   restricted execution to the existing aggregate example; extend with fresh-session keys and
   session checks. Complete PRF local kernel contracts and preserve the existing reduction loss.
5. **Resource closure and verified implementation.** Derive costs for handlers, routing, queues,
   scheduling, parsing, randomness, initialization, and output recovery. Require a global
   activation/potential bound for feedback. Reuse the existing coin-vector semantics and build
   one uniform encoded OTP/simulator implementation with all-path bounds for arbitrary widths.

Each stage needs a positive consumer and a semantic separating theorem before its public API
and paper claim are considered complete. Full validation, lint, tests, import boundaries, and
axiom checks are required at integration; no new trust debt is permitted.

## Routed composition checkpoint

Merged in [PolyFun #210](https://github.com/Verified-zkEVM/PolyFun/pull/210), commit
`fc96202707d97be2c470a6fc100e988d8e4e7c0e` (identical tree to the validated head
`75f158e64529e746bdafa6a07f6abb8ddf1c7623`). PolyFun's full
`./scripts/validate.sh --lint --test --axioms` passes: 11,940 declarations across 310 production
modules, zero sorry or nonstandard-axiom taint. Log:
`/private/tmp/uc-composition-polyfun-validation.log`. VCVio's full validation also passes
against the published dependency: 18,688 declarations across 623 modules, the same 40 existing
sorry-tainted declarations, and zero nonstandard-axiom taint. Log:
`/private/tmp/uc-composition-vcvio-validation.log`.

The implementation now compiles `OpenSyntax.Raw` into finite `ReactiveNetwork.Assembly`
values, with component polynomial interfaces retained and the global environment chosen at
closure. `Diagram` has exact map/plug transport, plug symmetry, and the four parallel/wired
closure factorizations under explicit component bijections. Network versions retain the
designated context environment. `runToken_reindex_cast` and `runFIFO_reindex_cast` transport
complete residual states through these equalities; VCVio derives experiments and Measure laws
from the actual runners and sampled setup.

`runSerial_eq_runToken` proves all finite serial FIFO/token prefixes from an empty pending
queue, preserving the extra delivery cost. The proof supports every lawful monad and does not
assume effects terminate successfully. The OTP consumer checks both completed and unfinished
prefixes and retains its reachable-queue counterexample. Raw-assembly tests distinguish the
eight-step charged identity relay from direct four-step echo. A two-component context consumes
the generic factorization theorem; an unchanged schedule after node relabeling gives a different
observation. These checks establish routed execution, not simulator admissibility or PPT closure.

The historical [design suite in VCVio #494](https://github.com/Verified-zkEVM/VCVio/pull/494)
remains an archival reference for displayed logic, separation logic, dynamic participants,
protocol-scale verification, and quantum proposals. Its dated API inventory and deployment
sequence are superseded by the current semantic contract and campaign; those broader proposals
are not being presented as completed or removed by retiring that PR.

## Executable statistical-security checkpoint

Merged [PolyFun #211](https://github.com/Verified-zkEVM/PolyFun/pull/211), commit
`025109160102028c04a950a6f02c78951c5e5f3d` (identical tree to the validated head
`a6a377018d5de1ec8fd8458527fec5e8141d4cd1`), carries intrinsic polynomial-operation
interpreters through raw compilation and all four parallel/wired graph factorizations.
Token and FIFO observation equations retain the actual effects and transport schedules.
Its full validation passes: 12,025 declarations across 312 production modules, with zero
sorry or nonstandard-axiom taint. Log: `/private/tmp/uc-handled-polyfun-validation.log`.
VCVio full validation passes against the published dependency: 18,752 declarations across
625 modules, the same 40 existing sorry-tainted declarations, and zero nonstandard-axiom
taint. Log: `/private/tmp/uc-reactive-security-validation.log`.

VCVio's `ReactiveSecurity` fixes an injective observation of returned Booleans, explicit
aborts, and unfinished prefixes. Its `ProbComp` interpretation is total and `law_univ`
proves unit mass. Generic PolyFun tests separately distinguish failing interpreters from
unfinished executions in the `Option` monad. `Contextual` has additive statistical
transitivity and parallel/wired replacement; `ContextualWithin` requires explicit admission
of each executable residual context.

`ReactiveWorld` connects a protocol's adversarial interface to an ordinary handled assembly,
retaining its environment backchannel. `Simulates` names an executable witness;
`StatisticallyEmulates` chooses it before every closing environment and horizon. The
transitivity theorem feeds the first simulator to the second emulation theorem and adds
errors. This is a finite-prefix statistical layer, not uniform computational admission.

The executed tests derive the server's observation from a five-activation request/draw/reply
conversation. False, uniform, and true local operations have adjacent distances one half and
endpoint distance one, refuting fixed-positive-error transitivity. The allowed-context API
consumes those comparisons with the correct sum. An explicit relay/backchannel conversation
needs nine activations and remains unfinished at five, preventing a free timed identity claim.
Its factorization test uses the generic wired observation theorem. General dummy-adversary
factorization, uniform executable admission, separated cryptographic consumers, and network
resource closure remain outstanding stages of the completion contract.

## Separated single-use OTP checkpoint

Full `./scripts/validate.sh --lint --test --axioms` passes: 18,896 declarations across
629 production modules, the same 40 existing sorry-tainted declarations, and zero
nonstandard-axiom taint. Log: `/private/tmp/uc-separated-validation.log`.

`Examples/OneTimePad/Separated` now defines six distinct polynomial machines for the
environment, private setup, sender, authenticated public channel, delivery adversary,
and receiver. The setup samples locally and distributes private shares only on internal
routes. The public channel retains its original ciphertext and accepts a Boolean delivery
decision. The adversary has one actual ciphertext/advice round with the environment;
advice may depend on the chosen plaintext and retained private memory.

`experiment_eq` proves that 29 token activations execute the complete conversation. Drop
and delivery retain their explicit costs. The ideal encoding sends an independently sampled
ciphertext to the sender and preserves the plaintext privately for the receiver. Correctness
and a message-independent ciphertext law imply equality of the two actual observation
measures; `oneTimePad_experiment_simulation` instantiates that theorem with the named uniform
ciphertext sampler. No advice countability or key measurability is required by this simulation
proof. The aggregate bridge retains the respective 29/9 budgets and requires ciphertext-only
advice, matching the earlier model's access restrictions.

Executed counterexamples distinguish the 28-step unfinished prefix, suppressing real
backchannel advice, and a receiver which returns the wrong plaintext despite using the same
randomized encryption. These are finite single-use results. They do not yet derive arbitrary
contextual OTP replacement, statically indexed sessions, a general dummy-adversary theorem,
or computational resource closure.

## Complexity foundation: source audit and adoption decision

This audit distinguishes the current VCVio pins from upstream source inspected on September 13.
It does not claim that the newer dependency set has been built with VCVio. In particular, the
optional backend's successful compatibility preflight recognizes known unavailable modules;
that success alone does not inhabit composition or oracle-closure instances.

The isolated checkout at complexitylib `6c248df7859f2f245e731c1e07057bf69d165fe2`
successfully built `TuringMachine.Composition`, `Combinators`, `Hoare`, `OutputBounds`,
`Asymptotics`, and `Classes.P.Defs` on its matched Lean 4.34.0-rc2 / Mathlib / CSLib
dependencies (2,062 build jobs). This validates those upstream modules; the VCVio adapter
and its downstream canaries still require a coordinated candidate build before adoption.

| Surface | Inspected evidence | Consequence |
| --- | --- | --- |
| [CSLib single-tape deterministic machines](https://github.com/leanprover/cslib/blob/main/Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean) | `TimeComputable` contains one machine working on every word. `PolyTimeComputable.comp` constructs composition, given monotonicity of the second bound, and accounts for intermediate output length. | This core is uniform. The optional P/poly facade's different quantifiers do not characterize CSLib's underlying definition. |
| [CSLib multitape deterministic machines](https://github.com/leanprover/cslib/blob/718cbea1a92e582eb5dbbe8efaaa0d3dcb3a5df0/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean) | Explicit input/output embeddings and input-indexed time/space bounds; finite binary machines in `ComputableInTimeAndSpace`; `runFrom_comm_of_step` transports exact step simulations. | A useful common reference target. Actual-input bounds fit dependent representations; a commuting-step theorem alone supplies neither encoding efficiency nor polynomial-overhead simulation. |
| [CSLib composition stack](https://github.com/leanprover/cslib/pull/875) | #870 merged; #871–875 closed without merging. The inspected main multitape directory has definitions and deterministic/nondeterministic bridges, but not that composition stack. | Do not treat those PR proofs as available dependencies. The separate single-tape composition theorem remains available. |
| [complexitylib dependency alignment](https://github.com/SamuelSchlesinger/complexitylib/pull/34) | Current inspected head `6c248df7859f2f245e731c1e07057bf69d165fe2` uses Lean 4.34.0-rc2 and adds a pinned CSLib dependency with matching Mathlib. | Test the matched dependency set together; the existing VCVio 4.33.1 compatibility failures are not a verdict on current upstream. |
| [complexitylib machine core](https://github.com/SamuelSchlesinger/complexitylib/blob/6c248df7859f2f245e731c1e07057bf69d165fe2/Complexitylib/Models/TuringMachine.lean) | Its own finite-state four-symbol machines, one-sided tapes, movable read/write output tape, exact runs, and finite choice traces. CSLib's multitape model instead has append-only output and different tape conventions. | A dependency edge is not machine equivalence. Output discipline, tape boundaries, halting conventions, and costs need explicit translations. |

**Working foundation:** retain PolyFun's existing representations, quantitative realizers, and
resource contracts as the UC-facing interface. Complete the first concrete implementation using
the isolated complexitylib adapter. Evaluate the newer matched dependency set in a separate
candidate and retain the validated baseline until its builds and canaries pass. Do not introduce
an unqualified PPT alias from a backend-relative certificate.

The cross-library bridge ledger is directed:

| Bridge obligation | Required evidence |
| --- | --- |
| Representations | Executable encoding/decoding or translation, round trips on valid inputs, malformed-input behavior, and bounds on work and encoded size. |
| Machine execution | Initialization correspondence, a reachable-configuration invariant, local simulation, halting/output recovery, and a composed polynomial overhead. |
| Randomness | Agreement of finite random-choice observations and consumption bounds; nondeterministic acceptance is insufficient. |
| Oracle interaction | Typed request/response correspondence, reply-size contracts, suspension/resumption, and dispatcher costs. |
| Class transport | One fixed compiler and code witness across all security parameters and inputs; transfer of the complete polynomial bound. |
| Equivalence | Both directed transports under stated representations and access models. A one-way simulation proves only one direction. |

CSLib's multitape model is the first common-target candidate for this ledger. Its single-tape
composition API is the comparison point for immediately usable deterministic closure.
Neither future upstream convergence nor a roadmap checkbox discharges these obligations.

## Adversarial evidence gates

Retain the existing leakage, incorrect-decoder, reused-pad, insufficient-fuel, missing-delivery,
reachable-pending-queue, and shared-state reply counterexamples. Add separating examples for
untransported schedules, hidden-state scheduler access, omitted relay costs, cross-session
traffic, fixed-positive-error transitivity, and unbounded feedback between locally bounded
components. For complexity, distinguish a slow implementation from the complexity of its
computed function: an exponential-delay realizer can fail a polynomial run bound while its
constant output has another efficient implementation.

Record the construction, public theorem, concrete consumer, counterexample, and exact literature
support before advancing the paper's claims. Polynomial wiring, free interpretation, displayed
contracts, and exact behavior remain the source of reusable structure; backend comparisons
serve the computational adequacy boundary.
