# 4. States you do not fully know

Chapters 1–3 described a quantum system by a single vector of amplitudes. That is not enough in
three situations a cryptographer meets constantly:

* the state was chosen at random (a random key, a random oracle);
* a measurement happened and its outcome was not recorded (or was recorded somewhere we ignore);
* we look at one part of a larger system, such as the adversary's register, while the rest is
  entangled with it (chapter 3 showed such a part has no vector).

This chapter introduces the description that handles all three, the **density matrix**. It is the
description VCVio uses by default, and it is the quantum counterpart of a probability
distribution.

## A random choice of vector

Suppose someone prepares $|0\rangle$ or $|1\rangle$, each with probability $\tfrac12$, and does not
say which. We could describe this by the list "$|0\rangle$ w.p. $\tfrac12$, $|1\rangle$ w.p.
$\tfrac12$". But a different preparation, "$|+\rangle$ w.p. $\tfrac12$, $|-\rangle$ w.p.
$\tfrac12$", turns out to give exactly the same statistics in every experiment. (Measuring directly
gives a fair coin in both cases; applying $H$ first swaps the two lists.) A good description should
not distinguish situations that no experiment can tell apart.

## Density matrices

For a state vector $\psi$, form the matrix $\psi\psi^\dagger$: entry $(i, j)$ is
$\psi_i\,\overline{\psi_j}$ (the bar is complex conjugation; for real amplitudes it does nothing).
Physicists write it $|\psi\rangle\langle\psi|$. For a random choice of vectors, average these
matrices with the probabilities:

$$\rho = \sum_k p_k\, \psi_k \psi_k^\dagger .$$

This matrix $\rho$ is the **density matrix**. Some examples:

$$|0\rangle\langle 0| = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}, \qquad
|+\rangle\langle +| = \tfrac12\begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}, \qquad
\tfrac12|0\rangle\langle 0| + \tfrac12|1\rangle\langle 1|
= \tfrac12|+\rangle\langle +| + \tfrac12|-\rangle\langle -|
= \tfrac12\begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}.$$

The two preparations above give the same matrix, $\tfrac12 \cdot 1$, as they should.

How to read a density matrix:

* **The diagonal is the measurement distribution.** Measuring gives outcome $a$ with probability
  $\rho_{aa}$. For $|+\rangle\langle +|$ that is $\tfrac12, \tfrac12$.
* **The off-diagonal entries record what interference needs.** $|+\rangle\langle +|$ and
  $\tfrac12 \cdot 1$ have the same diagonal, but only the first has off-diagonal entries, and only
  the first turns into $|0\rangle$ under $H$.
* **The trace (the sum of the diagonal) is the total probability**, here $1$.

A **diagonal** density matrix is just a probability distribution written on the diagonal. So
density matrices contain ordinary randomness as a special case, which is what lets one framework
describe classical and quantum steps together.

The matrices that arise this way are exactly the **positive semidefinite** matrices of trace one.
Positive semidefinite (PSD) means $v^\dagger \rho\, v \ge 0$ for every vector $v$; informally,
"every measurement, in every basis, gives nonnegative probabilities".

## Gates and measurements on density matrices

A gate $U$ sends $\psi$ to $U\psi$, so it sends $\psi\psi^\dagger$ to
$U\psi\psi^\dagger U^\dagger$, and by averaging:

$$\rho \;\longmapsto\; U \rho\, U^\dagger .$$

Measuring and **forgetting** the outcome erases the off-diagonal entries:

$$\tfrac12\begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}
\;\xrightarrow{\text{measure, forget}}\;
\tfrac12\begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}.$$

This is the third experiment of chapter 2 in one line: after the middle measurement the state is
$\tfrac12 \cdot 1$, and $H(\tfrac12 \cdot 1)H^\dagger = \tfrac12 \cdot 1$ is still a fair coin.
Measuring and forgetting is not the same as doing nothing, and density matrices show the
difference.

## Keeping the probability inside the state

When we do **record** the outcome, the textbook rule is: outcome $a$ happens with probability
$\rho_{aa}$, and afterwards the state is $|a\rangle\langle a|$. VCVio stores both facts in one
matrix, by not rescaling: after outcome $a$ it keeps

$$\rho_a = \rho_{aa}\, |a\rangle\langle a| ,$$

a matrix whose trace is the probability of $a$. For $|+\rangle\langle +|$, each outcome leaves
$\tfrac12|a\rangle\langle a|$. There is no division, so an outcome of probability zero needs no
special case, and the probability of a sequence of outcomes is simply the trace of the final
matrix.

Matrices of trace less than one are called **subnormalized**. They also describe computations that
may **fail**: if the traces of all possible results add up to less than one, the missing amount is
the probability of failure. This is exactly how VCVio's classical layer treats failure, as missing
probability mass in a subdistribution, so the quantum and classical layers compose in the same way.

## Throwing away part of a system

For two systems, the density matrix has rows and columns indexed by pairs $(a, r)$. To describe the
first system alone, sum over the second index on the diagonal of the second system:

$$\big(\operatorname{tr}_R\,\rho\big)_{a a'} = \sum_r \rho_{(a, r),\,(a', r)} .$$

This is the **partial trace**. It is what "ignore register $R$" means, and it gives the same
predictions for every experiment on the first system as the full state does.

For the Bell state $\tfrac{1}{\sqrt2}(|00\rangle + |11\rangle)$, the partial trace over the second
qubit is $\tfrac12 \cdot 1$. That explains chapter 3: for any gate $U$,
$U(\tfrac12 \cdot 1)U^\dagger = \tfrac12 \cdot 1$, so the first qubit of a Bell pair is a fair coin
whatever gate is applied to it. Its information is entirely in the correlation with the other
qubit.

## So far

| Situation | Description |
|---|---|
| known vector $\psi$ | $\psi\psi^\dagger$ |
| random choice of vectors | the average $\sum_k p_k\, \psi_k\psi_k^\dagger$ |
| after a gate $U$ | $U\rho\, U^\dagger$ |
| after measuring and forgetting | off-diagonal entries erased |
| after outcome $a$ (VCVio's convention) | unnormalized; trace is the probability of $a$ |
| one part of a pair | partial trace |
| failure | missing trace |

> **In VCVio.** A state is a `SubState A` (`VCVio/Quantum/Observe.lean`): a PSD matrix with trace at
> most one, so failure can be represented. The state after outcome `a` is `p.post ρ a`, unnormalized
> as above. The partial trace is `MatrixMap.traceRight A R` (`VCVio/Quantum/MatrixMap.lean`), with
> `traceRight_kronecker` saying that throwing away the second factor of a product state leaves the
> first. The measurement of `|+⟩⟨+|` is `measureZ` applied to `plus` in
> `VCVioTest/Quantum/Basic.lean`.

Next: [chapter 5, everything a quantum computer can do](5-what-a-quantum-computer-can-do.md).
