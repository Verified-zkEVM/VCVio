# Quantum guide

This guide explains VCVio's quantum layer file by file: what each definition means, why it has
the form it has, and how to check that it says what it should. It assumes the basics covered by the
[tutorial](../tutorial/1-coins-to-qubits.md) (amplitudes, density matrices, instruments, complete
positivity, quantum queries), and VCVio's classical `OracleComp`. Readers who already know quantum
information can start here directly and use the [conventions](../reference/conventions.md) page for
VCVio's choices of tensor order, Choi matrix and so on.

The guide combines worked examples with explanations of the general Lean definitions.
The reference pages
([conventions](../reference/conventions.md), [glossary](../reference/glossary.md),
[classical and quantum side by side](../reference/classical-quantum.md),
[sources](../reference/literature.md)) are for looking things up.

The Mathlib-only base of the layer (matrix maps, instruments, registers, observation, pure states
and oracle unitaries) is the
[QuantumFoundations](https://github.com/lean-crypto-foundations/QuantumFoundations) dependency,
shared with CatCrypt-core; paths below that start with `QuantumFoundations/` are in that
repository. `VCVio/Quantum/Foundations/Parallel.lean` stages generic coordinate and subinstrument
batching facts for that dependency and imports only QuantumFoundations and Mathlib.
The layer is the subject of issue #706. Open questions and planned work are in
[`docs/design/quantum-layer.md`](../../design/quantum-layer.md).

* [1-states-and-instruments](1-states-and-instruments.md) — States, measurements, failure,
  instruments, outcome-dependent outputs, infinite outcomes and final observation.
* [2-vectors-and-hybrid-bound](2-vectors-and-hybrid-bound.md) — Vectors, interference, the
  density-matrix bridge and the hybrid bound.
* [3-choi-kraus-stinespring](3-choi-kraus-stinespring.md) — Choi matrices, Kraus operators and
  Stinespring form.
* [4-programs-and-runtimes](4-programs-and-runtimes.md) — Adaptive programs, runtimes, parallel
  query budgets, sequentialization and combs.
* [5-qrom](5-qrom.md) — Classical queries, Deutsch's algorithm and the QROM; parallel rounds,
  private uniform coins, classical and compressed execution bridges, parallel reprogramming,
  marked search, fixed-target preimage search, complete raw-table encodings, exact finite-window
  rank security.
* [6-instability](6-instability.md) — The classical instability calculus and its role in quantum
  proofs.
* [7-time-lock-puzzles](7-time-lock-puzzles.md) — Quantum preprocessing, honest generation,
  shared oracle memory and key-only recovery experiments.

## The layers

| Layer | Files | What it provides |
|---|---|---|
| [States and measurements](1-states-and-instruments.md) | `QuantumFoundations/MatrixMap*`, `SubInstrument`, `DSubInstrument`, `Observe`; `VCVio/Quantum/Semantics` | Quantum operations, measurements with classical outcomes, failure, composition, outcome measures. |
| [Vectors](2-vectors-and-hybrid-bound.md) | `QuantumFoundations/Pure/*` | State vectors and operator norms, with theorems that they agree with the density-matrix semantics. |
| [Three descriptions of one map](3-choi-kraus-stinespring.md) | `QuantumFoundations/MatrixMap/Kraus.lean`, `MatrixMap/Stinespring.lean`, `MatrixMap/Dual.lean` | Choi matrices, Kraus operators, Stinespring form and its unitary version, the trace dual. |
| [Oracles and programs](4-programs-and-runtimes.md), [QROM](5-qrom.md) | `VCVio/Quantum/Comp/*`, `VCVio/Quantum/Oracle/*` | Quantum programs, oracle implementations, the quantum random-oracle model, classical algorithms inside it. |
| [Instability](6-instability.md) | `VCVio/OracleComp/QueryTracking/Instability/*` | The classical quantity that compressed-oracle proofs bound quantum queries by. |
| [Time-lock puzzles](7-time-lock-puzzles.md) | `VCVio/CryptoFoundations/TimeLockPuzzle/Quantum.lean`, `QuantumClassical.lean` | Quantum preprocessing, shared oracle state across phases, and joint laws for classical honest generators. |

The layer introduces no additional quantum axioms. Its formal results are Lean theorems, and
the examples are in `VCVioTest/Quantum/`.

## Seeing that it is right

The definitions are checked in three ways.

The agreement rows and exact-example checks now appear under **Checks** in
[states and instruments](1-states-and-instruments.md#checks),
[vectors](2-vectors-and-hybrid-bound.md#checks),
[representations](3-choi-kraus-stinespring.md#checks),
[programs and runtimes](4-programs-and-runtimes.md#checks), [QROM](5-qrom.md#checks),
[instability](6-instability.md#checks) and [time-lock puzzles](7-time-lock-puzzles.md#checks).
The textbook comparison is in
[states and instruments](1-states-and-instruments.md#checks), with page references in the
[literature table](../reference/literature.md).

## Scope

Covered: finite-dimensional systems, operations and measurements with failure as missing mass;
adaptive oracle programs and the QROM; classical algorithms with private uniform coins;
variable-width parallel rounds and exact sequentialization at the point budget; parallel
compressed-runtime output-law equivalence; parallel reprogramming and marked/fixed-target
preimage bounds with adaptive round/point budgets; scheduled hybrids, retained-state finishers
and two-phase time-lock experiments; complete raw-table encodings and exact honest algorithms in
finite byte windows; rank frontiers and the exact pointer-chain programmed-oracle coupling;
exact finite-window pointer-chain quantum delay security with query-bounded preprocessing.

Not covered: infinite-dimensional systems, continuous measurement outcomes, nonterminating loops,
coherent choice of oracle port, or a general converse putting programs into comb form.
Exact square-root-sum bounds for deterministic width profiles and the CFHL compressed-oracle track remain separate.
Auxiliary-input preprocessing with unbounded queries and bounded advice remains separate.
Serialized public puzzles, unrestricted-length hash queries and early-success quantum truncation
need additional interface or execution results. See
[the design obligations](../../design/quantum-layer.md).
