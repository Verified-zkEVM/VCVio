# 5. The quantum random-oracle model

Covers: Classical queries, Deutsch's algorithm, the QROM runtime, classical algorithms in the
QROM and parallel oracle rounds. See [conventions](../reference/conventions.md). Read first: tutorial
[chapter 6](../tutorial/6-quantum-queries.md); builds on [guide 4](4-programs-and-runtimes.md).

## A classical query inside a quantum experiment

In the quantum random-oracle model (QROM), a function $H : X \to Y$ is sampled uniformly before the
experiment, and a quantum algorithm may query it through the unitary

$$U_H\,|x, y\rangle = |x,\; y + H(x)\rangle .$$

Here $Y$ is a finite additive group; for bitstrings, $+$ is XOR. A classical query is the special
case of a basis-state input: prepare $|t, 0\rangle$, apply $U_H$ to get $|t, H(t)\rangle$, measure
in the computational basis, which reports $H(t)$ with certainty, and discard the register. That is
`Quantum.classicalQuery t`.

Replacing each query of a classical algorithm `oa : OracleComp (X →ₒ Y) α` by this program, with
VCVio's `simulateQ`, gives `oa.toQuantum`. Its distribution in the QROM is its distribution under
VCVio's lazily sampled random oracle (`qromEvalDist₂_toQuantum_eq_randomOracle`), with no query
bound. So the QROM restricted to classical algorithms is the classical random-oracle model. Tests:
`queryZero` returns $H(0)$; the adaptive `queryTwice` returns $H(H(0))$.

## Deutsch's algorithm

One quantum query can do what needs two classical ones. Take $X = Y = $ `Fin 2` and start in
$|+\rangle|-\rangle$, where $|-\rangle = \tfrac{1}{\sqrt2}(|0\rangle - |1\rangle)$. Since
$U_H|x\rangle|-\rangle = (-1)^{H(x)}|x\rangle|-\rangle$, one query gives

$$\tfrac{1}{\sqrt 2}\big((-1)^{H(0)}|0\rangle + (-1)^{H(1)}|1\rangle\big) \otimes |-\rangle,$$

which is $\pm|+\rangle|-\rangle$ if $H(0) = H(1)$ and $\pm|-\rangle|-\rangle$ otherwise. Measuring
the first qubit in the basis $\{|+\rangle, |-\rangle\}$ reports $H(0) + H(1)$ with certainty
(`VCVioTest.QuantumOracle.outcomeMeasure_deutsch`). A classical algorithm must query both points.

## The QROM as a runtime

`additiveOracleRuntime H` answers every call with $U_H$ and has no private memory. The QROM
distribution of a program is the average over all functions:

$$\texttt{qromEvalDist}\;I\;x\;\rho\;(S) = |Y|^{-|X|} \sum_{H} \Pr[\,x \text{ against } U_H
\text{ from } \rho \text{ reaches a leaf in } S\,] \qquad (\texttt{qromEvalDist\_eq\_sum}).$$

$H$ is sampled once per run, not once per call. Two consequences that justify the definition:

* A program that makes no calls runs in the same way against every $H$, so it guesses a pair
  $(x, H(x))$ with probability exactly $1/|Y|$ (`qromEvalDistMap_guess_zero_of_trace_eq_one`).
* If every call receives inputs in a set $S$, the run cannot tell $H$ from any $H'$ that agrees with
  it on $S$ (`evalDist_additiveOracleRuntime_eq_of_eqOn`).

## Parallel oracle rounds

The ports of `qromBatchSpec X Y` are natural numbers. Port `k` acts on
`Fin k → X × Y`, applying the same `H` to each input/response pair. The basis permutation is
`parallelOracleEquiv H k`, and `parallelOracleUnitary H k` is its matrix. Slots may be
entangled and their inputs may repeat, including when the width exceeds the domain cardinality.

`QuantumRuntime.batch` batches ports with the same input and output register and no classical
result, in increasing slot order with one shared private register. Generic stateful steps need
not commute. For the additive oracle,
`batch_oracleQuery` proves equality with the simultaneous operation
`parallelOracleQuery H k`, including an arbitrary untouched private register.
`parallelOracleRuntime_step` gives that law for a variable-width runtime.
`intertwines_batch_step` transports private-memory simulations through batching. If the
simulation preserves trace and maps one initial private state to the other,
`evalDist_batch_eq_of_simulation` gives agreement of output laws for adaptive programs.

`qromBatchEvalDist` samples one function from `X → Y` for the entire run. Its mixture formula,
`qromBatchEvalDist_eq_sum`, uses the original function space, so different slots and rounds
receive answers from the same random oracle. Identifying the parallel oracle with an oracle for
`xs ↦ H ∘ xs` is algebraic: sampling `H` induces a generally correlated law on these derived
functions, rather than the uniform law on all functions between the product spaces.
A width-zero call is the identity. Program-level translation into sequential queries,
point-budget transfer, the classical batch bridge, the concrete parallel compressed-runtime
equivalence, and depth-sensitive security bounds remain open.

## Checks

**They agree with each other.** Wherever the library offers two descriptions of the same thing, a
theorem says they agree:

| Two descriptions | Agreement |
|---|---|
| the QROM on classical algorithms and the classical random oracle | `qromEvalDist₂_toQuantum_eq_randomOracle` |
| ordered calls on disjoint slots and the simultaneous additive oracle | `batch_oracleQuery` |
| the parallel oracle matrix and an ordinary oracle on product registers | `parallelOracleUnitary_eq_oracleUnitary_submatrix` |

**They compute the right numbers.** The tests work small examples to exact values: Deutsch's
algorithm. `VCVioTest/Quantum/Parallel.lean` checks cyclic ranges of orders three and five,
repeated inputs, zero-width calls, coherent two-slot inputs, and noncommuting shared-memory steps.
