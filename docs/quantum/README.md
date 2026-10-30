# Quantum computation in VCVio

VCVio has a quantum layer: quantum states, measurements and operations, quantum programs that call
oracles, and the quantum random-oracle model (QROM). These pages explain it. Pick a starting point
by what you already know.

| You know | Start with |
|---|---|
| no quantum computing at all | the [tutorial](tutorial/1-coins-to-qubits.md): six short chapters, assuming only discrete probability and matrices |
| quantum basics (Nielsen–Chuang level), but not VCVio | the [guide](guide/README.md), which explains the Lean definitions file by file |
| quantum information well, and want VCVio's exact choices | the [conventions](reference/conventions.md), then the guide |
| VCVio's classical layer, and want the analogies | [classical and quantum side by side](reference/classical-quantum.md) |

## The tutorial

1. [From coins to qubits](tutorial/1-coins-to-qubits.md): amplitudes, measurement, the Born rule.
2. [Gates and interference](tutorial/2-gates-and-interference.md): unitary gates, the Hadamard
   gate, why amplitudes can cancel.
3. [Several qubits](tutorial/3-several-qubits.md): tensor products, CNOT, entanglement.
4. [States you do not fully know](tutorial/4-states-you-do-not-fully-know.md): density matrices,
   measuring and forgetting, partial trace, failure as missing trace.
5. [Everything a quantum computer can do](tutorial/5-what-a-quantum-computer-can-do.md): Kraus
   operators, quantum operations and instruments, complete positivity.
6. [Quantum queries and the QROM](tutorial/6-quantum-queries.md): the query gate, Deutsch's
   algorithm, and why classical random-oracle proofs need new tools.

## The guide

One file per part of the library, each starting from a worked example with the Lean declarations
beside it: [states and instruments](guide/1-states-and-instruments.md),
[vectors and the hybrid bound](guide/2-vectors-and-hybrid-bound.md),
[Choi, Kraus and Stinespring](guide/3-choi-kraus-stinespring.md),
[programs and runtimes](guide/4-programs-and-runtimes.md), [the QROM](guide/5-qrom.md),
[instability](guide/6-instability.md).

## Reference

[Conventions](reference/conventions.md), [glossary](reference/glossary.md),
[classical and quantum side by side](reference/classical-quantum.md), and
[definitions and theorems against the literature](reference/literature.md).

Design decisions and open problems are in
[`docs/design/quantum-layer.md`](../design/quantum-layer.md). The tracking issue is #706.
