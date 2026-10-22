# 2. Gates and interference

Chapter 1 described a qubit as a vector of amplitudes and said that measuring it gives outcome $0$
with probability $|\alpha|^2$. This chapter is about what you can do to a qubit *before* measuring
it, and shows the first real difference from coins: amplitudes can cancel.

## Steps are matrices that keep the length

As with coins, a step that changes a qubit is a matrix $U$ applied to the vector of amplitudes:
$\psi \mapsto U\psi$. For coins, the matrix had to turn distributions into distributions (columns
that add up to one). For qubits, it has to turn valid states into valid states, so it must keep
$|\alpha|^2 + |\beta|^2 = 1$ for every input. A matrix that keeps this length for every input is
called **unitary**, and a step of this kind is called a **gate**.

For real matrices, unitary means that the columns are perpendicular vectors of length one: the
matrix is a rotation or a reflection. (For complex matrices the condition is $U^\dagger U = 1$,
where $U^\dagger$, the **conjugate transpose**, is the transpose with every entry replaced by its
complex conjugate. For real matrices $U^\dagger$ is just the transpose.)

Three gates are enough for this tutorial:

$$X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}, \qquad
Z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}, \qquad
H = \tfrac{1}{\sqrt2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}.$$

* $X$ swaps the two amplitudes: $X|0\rangle = |1\rangle$ and $X|1\rangle = |0\rangle$. It is the
  classical NOT gate.
* $Z$ flips the sign of the amplitude of $|1\rangle$. It turns $|+\rangle$ into $|-\rangle$ and
  back. Measuring right after $Z$ shows nothing, because a sign disappears when squared.
* $H$, the **Hadamard gate**, is the interesting one.

## The Hadamard gate

Applied to the basis states, $H$ gives the two states of chapter 1:

$$H|0\rangle = \tfrac{1}{\sqrt2}\,|0\rangle + \tfrac{1}{\sqrt2}\,|1\rangle = |+\rangle,
\qquad
H|1\rangle = \tfrac{1}{\sqrt2}\,|0\rangle - \tfrac{1}{\sqrt2}\,|1\rangle = |-\rangle .$$

So "apply $H$ to $|0\rangle$, then measure" gives a fair coin, just like the coin flip $F$ of
chapter 1. Now apply $H$ a second time instead of measuring. Because $H$ is a matrix, it acts on
each part of the sum separately:

$$H|+\rangle = \tfrac{1}{\sqrt2}\big(H|0\rangle + H|1\rangle\big)
= \tfrac12\big(|0\rangle + |1\rangle\big) + \tfrac12\big(|0\rangle - |1\rangle\big)
= |0\rangle .$$

The two contributions to the amplitude of $|1\rangle$ are $+\tfrac12$ and $-\tfrac12$, and they
cancel. The two contributions to $|0\rangle$ add up to $1$. This cancellation is called
**interference**. It is impossible with probabilities, which are never negative and so can only
add up. In the same way $H|-\rangle = |1\rangle$, which settles the question from chapter 1: to
tell $|+\rangle$ from $|-\rangle$, apply $H$ and then measure. $|+\rangle$ always gives $0$ and
$|-\rangle$ always gives $1$.

## Three experiments

Start each time from $|0\rangle$:

| Experiment | Result |
|---|---|
| $H$, then measure | fair coin |
| $H$, then $H$, then measure | $0$ with certainty |
| $H$, measure (and ignore the result), $H$, measure | fair coin |

The first two rows show that the first $H$ did not make the qubit random, even though measuring
right after it looks random: the second $H$ undoes it exactly ($HH = 1$). Compare coins, where
$FF = F$ and randomness cannot be undone.

The third row shows what measuring in the middle does. After the middle measurement the qubit is
$|0\rangle$ or $|1\rangle$, each with probability $\tfrac12$, and the second $H$ turns either one
into a fair coin. The measurement destroyed the interference. Looking at a quantum computation
while it runs changes what it does, and this will matter for cryptographic proofs in chapter 6.

## Reversible steps

Every gate can be undone: the inverse of $U$ is $U^\dagger$, which is again a gate. So a
computation made only of gates is reversible, and measurement is the only irreversible step so
far. Classical reversible operations are gates too: any permutation of the basis states, such as
$X$, is a unitary matrix with entries $0$ and $1$. So deterministic computation fits inside quantum
computation, provided it is done reversibly. Chapter 6 uses this to turn a classical function into
a quantum oracle.

## So far

* A gate is a unitary matrix; it keeps the length of the amplitude vector and can be undone.
* Amplitudes can be negative, so contributions can cancel (interference). Probabilities cannot.
* Measuring in the middle destroys interference.

> **In VCVio.** A gate on a system `A` is a matrix `Matrix A A ℂ`, and applying it to a state
> vector `ψ` is written `U •ᵥ ψ` (`VCVio/Quantum/Pure/Vector.lean`). The Hadamard gate and the
> first two experiments are in `VCVioTest/Quantum/Pure.lean`: `hadamard`,
> `hadamard_mem_unitaryGroup`, `hadamard_applyVec_ket0` ($H|0\rangle = |+\rangle$), and
> `outcomeMeasure_hadamardThenMeasure_ket0` (the fair coin, computed both with vectors and with the
> density matrices of chapter 4).

Next: [chapter 3, several qubits](3-several-qubits.md).
