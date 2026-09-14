# Interaction Integration

VCVio depends on PolyFun for the generic interaction framework.
Do not duplicate PolyFun's interaction guide here.
Use this page for VCV-specific runtime, computational, and example integration only.

## Source of Truth

Generic protocol theory lives in PolyFun:

- Sequential specs, transcripts, decorations, strategies, append, replicate, and state chains: `PolyFun.Interaction.Basic.*`
- Two-party, multiparty, and concurrent interaction layers: `PolyFun.Interaction.TwoParty.*`, `PolyFun.Interaction.Multiparty.*`, `PolyFun.Interaction.Concurrent.*`
- Generic UC interfaces, open processes, structural boundary traces, open theory, notation, environment actions, and leakage scaffolding: `PolyFun.Interaction.UC.*`

For conceptual background, read PolyFun's `docs/wiki/interaction.md` and the module docstrings in the PolyFun dependency.
VCVio should only document how those generic APIs are instantiated with probabilistic semantics, oracle computations, and crypto examples.

## VCV-Specific Layers

VCVio retains the computational and runtime interpretation of PolyFun's generic UC layer:

| File | Purpose |
|------|---------|
| `VCVio/Interaction/UC/Computational.lean` | Computational observation layer for UC-style emulation using subprobability measures and total variation distance. |
| `VCVio/Interaction/UC/ProportionalScheduler.lean` | Mass-aware `ProbComp` scheduler whose output distribution is invariant under swap and reassociation. |
| `VCVio/Interaction/UC/Runtime.lean` | Synchronous runtime semantics for closed open processes, including `processSemantics`, `processSemanticsProbComp`, and `processSemanticsOracle`. |
| `VCVio/Interaction/UC/AsyncRuntime.lean` | Asynchronous runtime semantics with process ticks and environment events. |
| `VCVio/Interaction/UC/AsyncSecurity.lean` | Fair-PPT security wrappers for asynchronous env-open executions. |
| `VCVio/Interaction/UC/OracleNetwork.lean` | Explicit FIFO requests/responses for static oracle clients, with ticket-checked resumption. |
| `VCVio/Interaction/UC/OracleNetwork/Serial.lean` | Derived bounded serial schedule, transcript and verdict agreement with traced oracle interpretation. |
| `VCVio/Interaction/UC/OracleNetwork/Transport.lean` | Transport of complete runtime states, pending packets and schedules along identity bijections. |
| `VCVio/Interaction/UC/ReactiveRuntime.lean` | Setup-sampled token/FIFO execution and measures of actual terminal environment outcomes. |
| `VCVio/Interaction/UC/ReactiveSecurity.lean` | Fixed outcome observations and graded statistical replacement for executable handled assemblies. |
| `VCVio/Interaction/UC/ReactiveWorld.lean` | Actual adversary/backchannel wiring and named executable statistical simulators. |
| `VCVio/Interaction/UC/ReactiveKernel.lean` | Joint local-handler laws preserve complete residual-state measures at every token/FIFO prefix. |
| `VCVio/Interaction/UC/Standard.lean` | Standard VCVio UC imports and conveniences. |
| `VCVio/Interaction/UC/StdDoBridge.lean` | Bridges from VCVio program-logic/Std.Do idioms into the UC runtime layer. |

These files may import PolyFun interaction modules.
Generic interaction modules should not be reintroduced under `VCVio/Interaction` or `ToMathlib`.

## Runtime Semantics

PolyFun separates the shape of an interaction from the effects that choose its moves:

- `TypeTree` describes the dependent tree of move types;
- `TypeTree.Path tree` records one complete play through that tree;
- `TypeTree.Sampler m tree` decorates every node with an `m`-computation that chooses its move.

`OpenProcess m Party Δ` comes from PolyFun and carries its per-step
`TypeTree.Sampler m` intrinsically. VCVio's runtime layer interprets a closed process by running
those samplers and then observing the resulting state in a probabilistic semantics. Use PolyFun's
`OpenStep.boundaryTrace` when you need to read the emitted output packets from a completed open-step
path; routing and probabilistic interpretation remain VCVio runtime concerns.

For composition whose scheduler must be insensitive to binary-tree
parenthesization, use `ProportionalScheduler.theory Party`. Each atomic
component starts with one positive scheduler slot, composition adds slot
masses, and a binary scheduler node chooses a subtree in proportion to its
mass. `ProportionalScheduler.isCoherent` proves that the resulting output
distribution is unchanged by swapping or reassociating component frontiers.

Use the synchronous entry points in `VCVio/Interaction/UC/Runtime.lean`:

```lean
import VCVio.Interaction.UC.Runtime
```

- `processSemantics` runs in an arbitrary surface monad `m` with bundled `MeasureSemanticsVia m`.
- `processSemanticsProbComp` specializes to coin-flip-only `ProbComp` protocols.
- `processSemanticsOracle` specializes to `OracleComp superSpec`, interpreting shared oracle access through `simulateQ'`.

Use the asynchronous entry points in `VCVio/Interaction/UC/AsyncRuntime.lean` when the environment can interleave direct events with process steps:

```lean
import VCVio.Interaction.UC.AsyncRuntime
```

- `RuntimeEvent Event` distinguishes `processTick` from `envTick e`.
- `EnvAction m Event State` is provided by PolyFun and reacts in the same surface monad as the runtime.
- `processSemanticsAsync` and `processSemanticsAsyncProbComp` are the main async semantic constructors.

## Computational Security

Use `VCVio/Interaction/UC/Computational.lean` for the distributional observation layer:

```lean
import VCVio.Interaction.UC.Computational
```

Important definitions:

- `Semantics T` bundles a result type and measurable space, a surface monad, its
  `MeasureSemanticsVia`, and a closed-system runner.
- `Semantics.evalDist` evaluates a closed system to a `Measure sem.Result`.
- `Semantics.distAdvantage` computes total variation distance between two closed systems.
- `ObservedCompEmulates sem ε real ideal` states fixed-advantage computational emulation.
- `AsympObservedCompEmulates` packages the negligible asymptotic variant.
- `ObservedCompUCSecure` is the simulator-based security wrapper.
- `Execution T` is the distributional experiment consumed by paper-level `Standard.UCSecure`.

The generic equivalence-style UC judgments live in PolyFun.
The VCVio layer gives them a crypto-facing distributional interpretation.
Use the `Observed*` definitions when you intentionally work relative to a chosen observer.
`Standard.UCSecure exec ε π F` states security relative to the supplied execution experiment.
Correspondence with textbook UC additionally needs justified execution, access, simulator,
and resource models. `Execution.ofSemantics` packages an observer as an execution; that
constructor alone does not establish those obligations.

## Examples

Start concrete reactive execution work with `Examples/OneTimePad/Reactive.lean` and
`Reactive/Security.lean`. They derive both runners from an actual input/output conversation
and prove single-use OTP simulation for ciphertext-only delivery adversaries, including
environments retaining countable private auxiliary state across the exchange. The actor and
access restrictions are explicit; this is not yet a general UC composition theorem.
`Reactive/Separation.lean` proves that plaintext leakage defeats every allowed simulator
and that uniform ciphertext marginals do not justify key reuse.
`VCVioTest/ReactiveNetworkAdversarial.lean` checks insufficient fuel, missing deliveries,
a reachable nonempty serial queue, and shared-state reply dependence.

`PolyFun.Interaction.UC.ReactiveNetwork.Assembly` compiles raw open syntax to finite typed
diagrams; select the single global environment after composition. `Factorization` and
`Factorization.Right` prove all four parallel/wired closure factorizations under explicit
node bijections, retaining the original machines. The generic `runToken_reindex_cast` and
`runFIFO_reindex_cast` transport complete residual states. `ReactiveRuntime` derives the
corresponding experiment and Measure equations, with FIFO schedules transported too.
`serialLaw_eq_tokenLaw` compares every serial FIFO prefix with its corresponding token prefix;
the underlying state theorem retains the extra delivery cost and requires an empty queue.
The raw relay canary and untransported-schedule counterexample live in PolyFun's UC tests.

`HandledAssembly` also carries each local polynomial-operation interpreter. `ReactiveSecurity`
specializes it to total `ProbComp` sampling and proves additive statistical composition from
actual token execution. Its fixed observation retains returned Booleans, explicit aborts, and
unfinished prefixes; `law_univ` proves unit observation mass. `ContextualWithin` requires
explicit admission of each constructed residual context. `ReactiveWorld` wires separate honest,
adversarial, and environment backchannel interfaces. Its named simulators are executable
assemblies chosen before the environment and horizon. These statistical statements do not
certify uniformity across security parameters, resource closure, or a dummy-adversary theorem.
`VCVioTest/ReactiveSecurity.lean` proves an executed fixed-error transitivity counterexample;
`VCVioTest/ReactiveWorld.lean` tests a three-component relay/backchannel exchange, including
its four additional forwarding activations.

`Examples/OneTimePad/Separated.lean` gives six actual actors: environment, private setup,
sender, public authenticated channel, delivery adversary, and receiver. Setup shares travel
only on internal routes; every local interpreter remains stateless outside its declared
sampling computation. `Separated/Execution.lean` derives the complete conversation from
29 token activations, including one ciphertext/advice backchannel round. `Separated/Security.lean`
proves OTP simulation with advice depending on the environment's private input and memory.
`Separated/Aggregate.lean` relates this execution to the earlier 9-activation aggregate model
when advice depends only on ciphertext. The different costs remain explicit.
`VCVioTest/SeparatedOTP.lean` separates short prefixes, ignored advice, and incorrect receivers
at the level of actual observation laws. This is still a fixed single-use conversation;
arbitrary context composition, static multisession execution, and computational admission
require the subsequent campaign results.

`Examples/OneTimePad/UC.lean` remains an observation-interface smoke test. Its chosen observer
makes arbitrary systems indistinguishable, so its `ObservedCompEmulates 0` theorem is not
evidence of network execution adequacy.
For lower-level probabilistic and oracle examples, see `docs/agents/probability.md` and `docs/agents/oracle-comp.md`.

## Import Guide

Choose the smallest import matching the task:

```lean
-- Generic interaction APIs from PolyFun
import PolyFun.Interaction.Basic.TypeTree
import PolyFun.Interaction.Basic.Strategy
import PolyFun.Interaction.Basic.Sampler           -- nodewise monadic choices
import PolyFun.Interaction.Basic.TypeTreeFintype   -- finite/nonempty branching ornaments
import PolyFun.Interaction.Concurrent.Process
import PolyFun.Interaction.UC.OpenProcess
import PolyFun.Interaction.UC.OpenProcessModel

-- VCV-specific runtime and security interpretation
import VCVio.Interaction.UC.Runtime
import VCVio.Interaction.UC.ProportionalScheduler
import VCVio.Interaction.UC.AsyncRuntime
import VCVio.Interaction.UC.Computational
import VCVio.Interaction.UC.Standard
```

When editing VCVio, prefer importing the specific PolyFun module you need rather than re-exporting large generic surfaces through VCVio.

For explicit FIFO oracle clients, `OracleNetwork.run` consumes a finite list of client and delivery
activations. `run_serialSchedule` proves that an all-branch bound of `n` queries suffices for
`3 * n` activations and preserves the complete traced oracle result. The PRF tag/reader consumer
is `Examples/PRFTagReader/Network.lean`. This runtime treats each service computation atomically;
it does not assume fairness or provide raw open-syntax contextual factorization.

`Examples/PRFTagReader/Network/Kernel.lean` transports that packet reduction under joint local
response/state laws. It retains the bad-world state event and all three original loss terms.
The shared adaptive-oracle theorem is `evalDist_simulateQ_run_congr` in
`VCVio/OracleComp/SimSemantics/StateT/Measure.lean`. Measurable state spaces and discrete
response/state products are explicit premises. `VCVioTest/PRFNetworkKernel.lean` admits handlers
that draw extra discarded randomness, demonstrating semantic preservation without claiming
unchanged implementation cost. `VCVioTest/ReactiveKernel.lean` refutes response-only replacement:
equal immediate replies can store different bits which a later call reveals.

## Reactive execution and observations

The canonical semantic direction is [the reactive UC contract](../design/uc-semantics.md).
PolyFun's `ReactiveProcess`/`ReactiveNetwork` modules supply actual typed input reactions,
token passing and FIFO delivery, prefix and identity-transport laws, and exact cofree-behavior
adequacy. The existing `OpenProcess` model has a different, activation/output-only scope.

[`ReactiveRuntime`](../../VCVio/Interaction/UC/ReactiveRuntime.lean) samples shared setup and
reads the actual environment outcome after finite execution. Its Measure equations and
behavior-adequacy theorems are the downstream entry points. Returned values, explicit abort,
and an unfinished prefix are separate observations. Defining an experiment does not establish
UC composition or computational admissibility; see the
[implementation ledger](../design/polynomial-composition-evidence.md).
