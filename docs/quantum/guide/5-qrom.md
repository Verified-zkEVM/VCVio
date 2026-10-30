# 5. The quantum random-oracle model

Covers: Classical queries, Deutsch's algorithm, the QROM runtime and classical algorithms in the
QROM. See [conventions](../reference/conventions.md). Read first: tutorial
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

## Checks

**They agree with each other.** Wherever the library offers two descriptions of the same thing, a
theorem says they agree:

| Two descriptions | Agreement |
|---|---|
| the QROM on classical algorithms and the classical random oracle | `qromEvalDist₂_toQuantum_eq_randomOracle` |

**They compute the right numbers.** The tests work small examples to exact values: Deutsch's
algorithm.
