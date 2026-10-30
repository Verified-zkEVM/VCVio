# 2. Vectors, interference and the hybrid bound

Covers: Vectors, interference, the density-matrix bridge and the hybrid bound. See
[conventions](../reference/conventions.md). Read first: tutorial
[chapter 2](../tutorial/2-gates-and-interference.md),
[chapter 4](../tutorial/4-states-you-do-not-fully-know.md); builds on
[guide 1](1-states-and-instruments.md).

## Hadamard, measure, forget

The Hadamard gate is the unitary
$H = \tfrac{1}{\sqrt 2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$
(`VCVioTest.QuantumPure.hadamard`). On vectors, $H|0\rangle = |+\rangle$
(`hadamard_applyVec_ket0`), and measuring gives outcome $a$ with probability
$\|K_a H|0\rangle\|^2 = \tfrac12$. The test file computes this twice, once with vectors and once
with density matrices, and proves the two agree (`outcomeMeasure_hadamardThenMeasure_ket0`).

Vectors carry interference. $H|+\rangle = |0\rangle$, so applying $H$ twice and measuring gives
$0$ with certainty. If instead we measure in between and forget the outcome, the state after the
measurement is $\tfrac12 \cdot 1$, then $H(\tfrac12 \cdot 1)H^\dagger = \tfrac12 \cdot 1$, and the
final measurement gives each outcome with probability $\tfrac12$. The measurement destroyed the
interference, and the state that remains is mixed, so it has no vector description.

So the library uses both. Vectors are the language of interference and of errors that accumulate
over queries. Density matrices handle forgotten outcomes and the composition of measurements with
later steps.

## The bridge

A vector $\psi$ with $\|\psi\| \le 1$ gives the pure substate $|\psi\rangle\langle\psi|$
(`SubState.ofVector`), of trace $\|\psi\|^2$. A branch with one Kraus operator sends
$|\psi\rangle\langle\psi|$ to $|K\psi\rangle\langle K\psi|$, so:

* outcome $a$ has probability $\|K_a\psi\|^2$ (`outcomeMeasure_ofKraus_ofVector`);
* the state left is described by the unnormalized vector $K_a\psi$ (`post_ofKraus_ofVector`);
* changing the input moves the probability of every event by at most
  $(\|\psi\| + \|\phi\|)\,\|\psi - \phi\| \le 2\,\|\psi - \phi\|$
  (`abs_outcomeMeasure_real_ofKraus_ofVector_sub_le`).

Operators are the same `Matrix B A ℂ` in both descriptions, acting on `EuclideanSpace ℂ A` by
`K •ᵥ ψ`, with the operator norm `Matrix.Norms.L2Operator`.

## The hybrid bound

Run the same operators $U_0, \dots, U_q$ with two different oracles $O$ and $O'$:
$\psi_0 = U_0\psi$ and $\psi_{i+1} = U_{i+1} O_i \psi_i$ (`queryState`). If the later operators
are contractions, then

$$\|\psi_q - \psi'_q\| \le \sum_{i<q} \|(O_i - O'_i)\,\psi_i\|
\qquad (\texttt{norm\_queryState\_sub\_queryState\_le}),$$

where $\psi_i$ is the state before call $i$ in the run with $O$. Each call adds its own discrepancy,
and the rest of the computation does not enlarge it. This is the step behind the hybrid argument of
Bennett, Bernstein, Brassard and Vazirani: if the oracles differ only on inputs the algorithm puts
little weight on, the final states are close, and by the bridge so are all output probabilities.

In the test, $\psi = H|0\rangle = |+\rangle$, one call to $O = Z$ or $O' = 1$, then $H$. The bound
is $\|(Z - 1)|+\rangle\| = \sqrt2$, and the final states are $|1\rangle$ and $|0\rangle$, at
distance exactly $\sqrt2$.

## Checks

**They agree with each other.** Wherever the library offers two descriptions of the same thing, a
theorem says they agree:

| Two descriptions | Agreement |
|---|---|
| vectors and density matrices | `outcomeMeasure_ofKraus_ofVector`, `post_ofKraus_ofVector` |
