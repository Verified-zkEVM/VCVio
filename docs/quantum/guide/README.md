# Quantum guide

This guide explains VCVio's quantum layer file by file: what each definition means, why it has
the form it has, and how to check that it says what it should. It assumes the basics covered by the
[tutorial](../tutorial/1-coins-to-qubits.md) (amplitudes, density matrices, instruments, complete
positivity, quantum queries), and VCVio's classical `OracleComp`. Readers who already know quantum
information can start here directly and use the [conventions](../reference/conventions.md) page for
VCVio's choices of tensor order, Choi matrix and so on.

Each guide file starts from a small example worked by hand, with the Lean declaration beside each
step, and ends with the general definition. The reference pages
([conventions](../reference/conventions.md), [glossary](../reference/glossary.md),
[classical and quantum side by side](../reference/classical-quantum.md),
[sources](../reference/literature.md)) are for looking things up.

The layer is the subject of issue #706. Open questions and planned work are in
[`docs/design/quantum-layer.md`](../../design/quantum-layer.md).

* [1-states-and-instruments](1-states-and-instruments.md) — States, measurements, failure,
  instruments, outcome-dependent outputs, infinite outcomes and final observation.
* [2-vectors-and-hybrid-bound](2-vectors-and-hybrid-bound.md) — Vectors, interference, the
  density-matrix bridge and the hybrid bound.
* [3-choi-kraus-stinespring](3-choi-kraus-stinespring.md) — Choi matrices, Kraus operators and
  Stinespring form.
* [4-programs-and-runtimes](4-programs-and-runtimes.md) — Adaptive programs, runtimes and combs.
* [5-qrom](5-qrom.md) — Classical queries, Deutsch's algorithm, the QROM runtime and classical
  algorithms in the QROM.
* [6-instability](6-instability.md) — The classical instability calculus and its role in quantum
  proofs.

## The layers

| Layer | Files | What it provides |
|---|---|---|
| [States and measurements](1-states-and-instruments.md) | `VCVio/Quantum/MatrixMap*`, `SubInstrument`, `DSubInstrument`, `Observe`, `Semantics` | Quantum operations, measurements with classical outcomes, failure, composition, outcome measures. |
| [Vectors](2-vectors-and-hybrid-bound.md) | `VCVio/Quantum/Pure/*` | State vectors and operator norms, with theorems that they agree with the density-matrix semantics. |
| [Three descriptions of one map](3-choi-kraus-stinespring.md) | `VCVio/Quantum/MatrixMap/Kraus.lean` | Choi matrices, Kraus operators and Stinespring form. |
| [Oracles and programs](4-programs-and-runtimes.md), [QROM](5-qrom.md) | `VCVio/Quantum/Comp/*`, `VCVio/Quantum/Oracle/*` | Quantum programs, oracle implementations, the quantum random-oracle model, classical algorithms inside it. |
| [Instability](6-instability.md) | `VCVio/OracleComp/QueryTracking/Instability/*` | The classical quantity that compressed-oracle proofs bound quantum queries by. |

Nothing in the layer is axiomatized: every statement below is a Lean theorem, and the examples are
in `VCVioTest/Quantum/`.

## Seeing that it is right

The definitions are checked in three ways.

The agreement rows and exact-example checks now appear under **Checks** in
[states and instruments](1-states-and-instruments.md#checks),
[vectors](2-vectors-and-hybrid-bound.md#checks),
[representations](3-choi-kraus-stinespring.md#checks),
[programs and runtimes](4-programs-and-runtimes.md#checks), [QROM](5-qrom.md#checks) and
[instability](6-instability.md#checks). The textbook comparison is in
[states and instruments](1-states-and-instruments.md#checks), with page references in the
[literature table](../reference/literature.md).

## Scope

Covered: finite-dimensional systems; quantum operations that may fail; measurements with any number
of outcomes, countably many of nonzero weight; outputs that depend on the outcome; adaptive programs
with several oracles and stateful oracle implementations; the QROM; classical algorithms in the
QROM; the representation theorems for CP maps; the classical instability calculus.

Not covered: infinite-dimensional systems; measurements with continuous outcomes; loops that may not
terminate; coherent choice of oracle port; classical algorithms with private randomness; putting
general programs in comb form; the compressed oracle itself. The plans for these are in
[`docs/design/quantum-layer.md`](../../design/quantum-layer.md).
