# Reactive UC semantics over polynomial interfaces

Status: accepted implementation direction, September 13, 2026. The implementation ledger is
[polynomial-composition-evidence.md](polynomial-composition-evidence.md); unchecked milestones
there remain obligations. This document consolidates the semantic review of VCVio #494 and #633.

## Semantic contract

The common foundation is typed reactive components, explicit execution disciplines, and proved
observation laws. Token-passing execution and bounded FIFO execution are equal targets. They
share components and routing theory, but need not produce equal observations or consume equal
fuel. A comparison theorem names the supported fragment and the correspondence of schedules.

Four layers must remain distinct:

1. A **presentation** supplies a typed machine, its private state, and initialization.
2. **Exact behavior** hides the presentation of state while retaining the complete interaction.
3. An **execution discipline** supplies activation, routing, delivery, and control transfer.
4. A **security observation** supplies allowed environments, output laws, simulators, and bounds.

Finality supports the second layer. It does not justify forgetting packets, samplers, delays,
or resource use. The implication from activation equivalence to distributional equality is false:
activation equivalence deliberately forgets information that execution can observe.

Likewise, a universal fold into an arbitrary effectful handler is not a literal cofree-matter
run. Deterministic or explicitly reified presentations can be related to pattern-runs-on-matter
by adequacy. Effectful handler composition uses the existing fold/fusion laws directly.

## Ownership

| Responsibility | Owner |
| --- | --- |
| Polynomial interfaces, handlers, programs, resumptions, machines, displayed contracts | PolyFun |
| Typed routing, generic reactive execution, token/FIFO disciplines, exact simulation | PolyFun |
| Abstract observation and error algebra, structural admissibility, generic resource witnesses | PolyFun |
| Measures, kernels, measurable iteration and trajectory mathematics | Mathlib / ToMathlib |
| Cryptographic setup, private randomness, leakage, adversary access and security observations | VCVio |
| Concrete machine realizations and costs | Existing backend libraries and their PolyFun adapters |

Generic operation, exact replacement, routing invariants, and contextual composition do not need
probability. Distributional adequacy does. Generic computational complexity also makes sense
without probability; cryptographic PPT classes instantiate that theory with an access model.

## Execution requirements

- Incoming packets must actually drive the receiver's transition. An activation marker and an
  output trace cannot supply this missing input behavior through a generic adapter.
- Initialize related executions with related states or initial laws. A relation on arbitrary
  machine states does not establish a relation between the chosen initial states.
- Preserve residual computation, queues, tickets, and public observations after every finite
  prefix. An exhausted budget is different from a returned value, an explicit abort, or divergence.
- Count administrative execution. Where a service is atomic, its internal work is a separate
  resource obligation; atomicity does not certify a constant-time implementation.
- Model shared services once. Disjoint-state frames justify independent updates; shared-oracle
  commutation requires a contract preserving replies as well as the resulting state.
- A scheduler receives only its declared view. Metadata naming visibility is insufficient if its
  implementation receives the entire private state. Fix adversary/scheduler families before
  sampling hidden setup, allowing only correlations supplied by the security notion.
- Token passing transfers control to the recipient on send; a non-environment halt returns
  control to the environment. FIFO enqueues sends and delivers the oldest packet on an explicit
  delivery activation. No-op activations retain their cost.
- Rebracketing a network must transport the scheduler and routing state. Repeated binary fair
  choices are not invariant under reassociation. Reuse the existing mass-aware scheduler laws
  where their hypotheses apply.
- Keep interface coproduct, choice of one component to advance, simultaneous advancement, and
  protocol parallel composition distinct. Publish the laws connecting their interpretations.

The first execution model uses static finite networks. Typed internal feedback is allowed, but
every executed cycle consumes a step; zero-cost normalization must not hide infinite work.

## Observations and security

Prove observation-relative factorization before requiring strict monoidal/traced/compact-closed
laws on runtime objects. PolyFun's `Observation.RespectsFactorization` already identifies the
needed observation equations. Error grades support additive composition; a fixed nonzero error
relation is not an equivalence.

The concrete observation is derived from the runner, its initial law, and the permitted output
projection. An arbitrary closed-system observer remains a useful abstract API, but its presence
does not establish that it observes protocol execution. In particular, the existing OTP
observation example makes arbitrary systems indistinguishable and is not the network-adequacy
pilot. Its local XOR/uniform argument is valid and reusable.

The first substantive UC pilot is single-use OTP message transmission with private shared-key
setup and an authenticated public channel. An environment supplies messages and receives actual
outputs; the simulator receives the specified public leakage. The theorem retains
`∀ adversary, ∃ simulator, ∀ environment`, with a simulator implemented by an admissible program.
A context-transforming function does not become an operational simulator just by giving it that
name. Constant-zero and constant-one services must be distinguishable, and leaking plaintext must
invalidate the OTP security claim.

Fixed total-variation bounds are statistical. Computational UC restricts adversaries, simulators,
and environments by proved resource witnesses and uses their Boolean observations. Unrestricted
total variation of an exposed transcript is a stronger statistical requirement. Structural
`SubTheory` closure under every boundary map must not silently be read as computational closure:
an executable adapter also needs a realization and its cost bound.

New semantics use `Measure` and `Kernel`. There is no global `Monad Measure` hiding measurability
obligations. Almost-everywhere couplings and all-branch displayed invariants remain separate.
Existing continuous-state wiring has countable query-answer interfaces; it does not certify
arbitrary continuous continuations.

## Literature and design provenance

- [Niu–Spivak, Polynomial Functors](https://arxiv.org/abs/2312.00990): polynomial dynamics,
  lenses, cofree behavior, and comonoid/bicomodule structure. These do not choose a scheduler or
  cryptographic observation.
- [Libkind–Spivak, Pattern Runs on Matter](https://arxiv.org/abs/2404.16321): the free/cofree
  interaction and module laws. Arbitrary effectful handlers need an additional interpretation.
- [Libkind–Spivak, Dynamic Task Delegation](https://arxiv.org/abs/2410.08373): adaptive invocation
  of selected components and different internal/external timescales. This is the direct
  asynchronous-delegation reference. The number 2112.11518 in the old suite instead identifies
  Niu–Spivak's *Collectives*.
- [Aberlé, Compositional Program Verification](https://arxiv.org/abs/2604.01303): displayed
  contracts and operational semantics for polynomial implementations. The dependency-tree
  construction is not a theorem about arbitrary cyclic probabilistic UC networks.
- [Katsumata–Rivas–Uustalu, Interaction Laws](https://arxiv.org/abs/1912.13477): residual
  effects and stateful runners; a full Kleisli lifting needs additional laws.
- [Farshim et al., UC, Categorically](https://arxiv.org/abs/2608.04521): static UC, token passing,
  composition-compatible indistinguishability and translation requirements. The efficiency and
  network-simulation hypotheses are part of its comparison with conventional UC.
- [VCVio #494 review](https://github.com/Verified-zkEVM/VCVio/pull/494#issuecomment-5080569976),
  [later supersession recommendation](https://github.com/Verified-zkEVM/VCVio/pull/494#issuecomment-5503184414),
  [UC follow-ups #633](https://github.com/Verified-zkEVM/VCVio/issues/633), and
  [probability roadmap #532](https://github.com/Verified-zkEVM/VCVio/issues/532).

## Extensions and evidence gates

After finite execution, construct measurable infinite trajectory laws and prove truncation error
bounds. Ordinary M-types do not supply measurable probability spaces automatically. Dynamic
sessions and corruption need initialization, access, and resource laws in addition to indexed
interfaces; cartesian reindexing alone is not probability preservation. Coordinate quantum
interfaces with [#706](https://github.com/Verified-zkEVM/VCVio/issues/706), without treating ordinary
classical polynomial interfaces as a coherent quantum semantics.

Bicomodules and dynamic operads are research directions until a named consumer benefits from
their formalization. The immediate evidence target is a checked chain from local polynomial
contracts to direct-handler, token-passing, and FIFO execution, and then to contextual security.
No paper claim advances ahead of that chain's proved links.
