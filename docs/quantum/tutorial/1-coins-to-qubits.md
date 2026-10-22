# 1. From coins to qubits

This tutorial assumes no physics and no quantum computing. You need discrete probability (a
distribution on a finite set) and a little linear algebra (vectors, matrices, multiplying a matrix
by a vector). Everything else is explained when it first appears.

## A random bit is a vector

A coin that lands heads with probability $p$ and tails with probability $1-p$ can be written as a
vector with one entry per outcome:

$$\text{coin} = \begin{pmatrix} p \\ 1-p \end{pmatrix}.$$

The entries are nonnegative and add up to $1$. A *deterministic* bit is a vector with a single
$1$: the bit $0$ is $\begin{pmatrix} 1 \\ 0 \end{pmatrix}$ and the bit $1$ is
$\begin{pmatrix} 0 \\ 1 \end{pmatrix}$.

A randomized step is a matrix. Flipping a fair coin, whatever the bit was before, is

$$F = \begin{pmatrix} \tfrac12 & \tfrac12 \\ \tfrac12 & \tfrac12 \end{pmatrix},
\qquad F \begin{pmatrix} 1 \\ 0 \end{pmatrix} = \begin{pmatrix} \tfrac12 \\ \tfrac12 \end{pmatrix}.$$

Column $j$ of the matrix is the distribution you get when the input is the bit $j$, so each column
is itself a distribution. Notice that $F F = F$: once the bit is random, flipping again does not
make it less random. Randomness, once added, cannot be removed by another randomized step. This is
the first thing quantum computation changes.

## A qubit is also a vector

A **qubit** (quantum bit) is described by a vector of two numbers too, but with different rules:

$$\psi = \begin{pmatrix} \alpha \\ \beta \end{pmatrix}, \qquad |\alpha|^2 + |\beta|^2 = 1 .$$

The entries $\alpha$ and $\beta$ are called **amplitudes**. They may be negative, and in general
they are complex numbers. For this tutorial you only need one fact about complex numbers: for
$z = a + bi$, the quantity $|z|^2 = a^2 + b^2$ is a nonnegative real number. Most examples use real
amplitudes, where $|z|^2$ is just $z^2$. What matters is that amplitudes can be **negative**; the
next chapter shows why that changes everything.

Physicists write the two deterministic vectors with a special bracket, called a **ket**:

$$|0\rangle = \begin{pmatrix} 1 \\ 0 \end{pmatrix}, \qquad
|1\rangle = \begin{pmatrix} 0 \\ 1 \end{pmatrix}, \qquad\text{so}\qquad
\psi = \alpha\,|0\rangle + \beta\,|1\rangle .$$

A ket is nothing more than a name for a column vector: $|0\rangle$ is "the vector for bit $0$".
A state like $\alpha|0\rangle + \beta|1\rangle$ with both amplitudes nonzero is called a
**superposition** of $|0\rangle$ and $|1\rangle$.

## Looking at a qubit: measurement

You cannot read the amplitudes of a qubit. The only way to get classical information out is to
**measure** it, and measuring $\alpha|0\rangle + \beta|1\rangle$ gives

$$\text{outcome } 0 \text{ with probability } |\alpha|^2, \qquad
\text{outcome } 1 \text{ with probability } |\beta|^2 .$$

This is the **Born rule**: probabilities are squared magnitudes of amplitudes. (That is why the
amplitudes must satisfy $|\alpha|^2 + |\beta|^2 = 1$: the two probabilities must add up to one.)

Measuring also changes the qubit. After outcome $0$ the qubit is $|0\rangle$, after outcome $1$ it
is $|1\rangle$; the superposition is gone. Measuring again gives the same outcome with certainty.
So one copy of a qubit yields one bit of information, no matter what $\alpha$ and $\beta$ were.

## Two states that look the same

Here are two qubit states:

$$|+\rangle = \tfrac{1}{\sqrt2}\,|0\rangle + \tfrac{1}{\sqrt2}\,|1\rangle, \qquad
|-\rangle = \tfrac{1}{\sqrt2}\,|0\rangle - \tfrac{1}{\sqrt2}\,|1\rangle .$$

Measuring either one gives $0$ or $1$ with probability $\big(\tfrac{1}{\sqrt2}\big)^2 = \tfrac12$
each. As far as this measurement can tell, both are a fair coin. Yet they are different vectors,
differing only in a sign that measurement squares away. Chapter 2 applies one operation before
measuring, and then $|+\rangle$ always gives $0$ while $|-\rangle$ always gives $1$. The sign is
real information; measuring right away just cannot see it.

## So far

| | Random bit | Qubit |
|---|---|---|
| state | vector of probabilities $(p, 1-p)$ | vector of amplitudes $(\alpha, \beta)$ |
| entries | nonnegative reals, sum $1$ | any complex numbers, $\lvert\alpha\rvert^2+\lvert\beta\rvert^2 = 1$ |
| looking at it | read the bit; the distribution is $(p, 1-p)$ | measure; outcome $0$ w.p. $\lvert\alpha\rvert^2$ |
| after looking | unchanged | becomes $\lvert 0\rangle$ or $\lvert 1\rangle$ |

Up to this point a qubit with nonnegative amplitudes behaves like a coin with $p = \alpha^2$. The
differences come from three places, one per chapter: amplitudes can cancel (chapter 2), several
qubits can be correlated in ways no joint distribution describes (chapter 3), and the steps a
quantum computer takes are reversible rotations rather than mixing (chapters 2 and 5).

> **In VCVio.** A system is named by a finite type listing its basis states, so a qubit is
> `Fin 2`, and a state vector is an element of `EuclideanSpace ℂ (Fin 2)`: one amplitude per
> basis state, with the usual length, so that $|\alpha|^2 + |\beta|^2$ is the squared length.
> VCVio mostly works with a different description of states, density matrices, which chapter 4
> introduces; the files are `VCVio/Quantum/Observe.lean` (states and measurement) and
> `VCVio/Quantum/Pure/Vector.lean` (vectors). The measurement of `|+⟩` above is worked out in
> Lean in `VCVioTest/Quantum/Basic.lean`.

Next: [chapter 2, gates and interference](2-gates-and-interference.md).
