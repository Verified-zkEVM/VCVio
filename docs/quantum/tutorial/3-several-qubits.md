# 3. Several qubits

So far there was one qubit. Cryptographic algorithms work on many: an input register, an output
register, the adversary's memory. This chapter puts qubits together, and meets the second
difference from coins: **entanglement**, correlation that no list of probabilities describes.

## Two coins

Two random bits are described by a distribution on the four outcomes $00, 01, 10, 11$, so by a
vector of length four. If the coins are independent, with probabilities $(p, 1-p)$ and
$(q, 1-q)$, the joint vector is the list of products:

$$(pq,\; p(1-q),\; (1-p)q,\; (1-p)(1-q)).$$

Coins can also be correlated. Two coins that always agree, each fair, have the joint vector
$(\tfrac12, 0, 0, \tfrac12)$, which is not a list of products. But there is a simple story behind
it: with probability $\tfrac12$ both are $0$, otherwise both are $1$.

## Two qubits

Two qubits are described by four amplitudes, one per basis state
$|00\rangle, |01\rangle, |10\rangle, |11\rangle$ (the first symbol is the first qubit). The
squared magnitudes add up to one, and measuring both qubits gives outcome $ab$ with probability
the squared magnitude of the amplitude of $|ab\rangle$.

If the qubits were prepared separately, in states $\alpha|0\rangle + \beta|1\rangle$ and
$\gamma|0\rangle + \delta|1\rangle$, the joint amplitudes are again the products:

$$\alpha\gamma\,|00\rangle + \alpha\delta\,|01\rangle + \beta\gamma\,|10\rangle +
\beta\delta\,|11\rangle .$$

This way of combining two vectors is the **tensor product**, written
$\psi \otimes \chi$, and the joint state of separately prepared qubits is always a tensor product.
For basis states it just concatenates: $|a\rangle \otimes |b\rangle = |ab\rangle$.

## Gates on one qubit of two, and gates on two

To apply a one-qubit gate $U$ to the first qubit and leave the second alone, apply $U$ to the
first symbol of every basis state: for example $X$ on the first qubit sends $|01\rangle$ to
$|11\rangle$. The $4 \times 4$ matrix that does this is written $U \otimes 1$ (the **Kronecker
product** of $U$ with the identity).

Some gates act on both qubits at once. The most useful is the **controlled NOT**:

$$\mathrm{CNOT}\,|a, b\rangle = |a,\; b \oplus a\rangle ,$$

which flips the second bit when the first is $1$ ($\oplus$ is addition mod 2, i.e. XOR). It only
permutes the four basis states, so it is a gate. If the second bit starts at $0$, CNOT copies the
first bit into it. Its pattern, keep $x$ and add something computed from $x$ to the second
register, is exactly the shape of a quantum oracle query in chapter 6.

## The Bell state

Start from $|00\rangle$, apply $H$ to the first qubit, then CNOT:

$$|00\rangle \;\xrightarrow{\;H \otimes 1\;}\; \tfrac{1}{\sqrt2}\big(|00\rangle + |10\rangle\big)
\;\xrightarrow{\;\mathrm{CNOT}\;}\; \tfrac{1}{\sqrt2}\big(|00\rangle + |11\rangle\big) .$$

This is the **Bell state**. Measuring both qubits gives $00$ or $11$, each with probability
$\tfrac12$: two fair coins that always agree.

It is not a tensor product. If it were, we would need $\alpha\gamma = \tfrac{1}{\sqrt2}$,
$\alpha\delta = 0$, $\beta\gamma = 0$ and $\beta\delta = \tfrac{1}{\sqrt2}$. The middle two force
one of $\alpha, \delta$ and one of $\beta, \gamma$ to be zero, and then one of the outer two is
zero as well. A two-qubit state that is not a tensor product is called **entangled**.

## Not just correlated coins

Is the Bell state simply the correlated coins in disguise, "both qubits are secretly $|00\rangle$
or secretly $|11\rangle$"? Apply $H$ to both qubits and then measure.

* If the qubits were secretly $|00\rangle$, then $H \otimes H$ makes each a fair coin
  independently, and the four outcomes are equally likely. The same holds for $|11\rangle$. So
  the outcomes would be uncorrelated.
* For the Bell state, a short calculation (expand $H|0\rangle$ and $H|1\rangle$ and collect terms;
  the $|01\rangle$ and $|10\rangle$ contributions cancel) gives

  $$(H \otimes H)\,\tfrac{1}{\sqrt2}(|00\rangle + |11\rangle) = \tfrac{1}{\sqrt2}(|00\rangle + |11\rangle).$$

  The outcomes still always agree.

So the correlation of the Bell state survives a change of basis, and no hidden "secretly $00$ or
$11$" explains it. Interference, once more, is what tells the two situations apart.

## Half of an entangled pair

What is the state of the first qubit of a Bell pair, on its own? Measured directly it is a fair
coin; measured after $H$ it is still a fair coin (from the calculation above, ignoring the second
qubit). In fact, whatever gate you apply to it before measuring, you get a fair coin; chapter 4
shows why. No single-qubit vector behaves like that: for every state vector $\psi$ there is a gate
that rotates it to $|0\rangle$, and measuring after that gate gives $0$ with certainty. (For
$|+\rangle$ the gate is $H$.) So **a part of an entangled system has no state vector**. Describing
it needs the density matrices of the next chapter.

This is also why operations on part of a system need care. An operation is applied to one register
while other registers, possibly entangled with it, are left alone. Chapter 5 asks what an
operation must satisfy to be safe in that situation.

## So far

* $n$ qubits are described by $2^n$ amplitudes; separately prepared qubits combine by the tensor
  product.
* A gate on one register is $U \otimes 1$; CNOT adds one bit into another.
* Entangled states are not tensor products; their correlations survive a change of basis.
* A part of an entangled system has no state vector of its own.

> **In VCVio.** A joint system is the product type `A × R`, so two qubits are `Fin 2 × Fin 2`,
> listed as `00, 01, 10, 11` with the first factor first. The tensor product of vectors is
> `tensorVec` (`VCVio/Quantum/Pure/Tensor.lean`), and of matrices Mathlib's Kronecker product
> `⊗ₖ`, with `(X ⊗ₖ Y) (a, r) (b, s) = X a b * Y r s`. Running an operation on the first
> factor while leaving `R` untouched is `frame R` (`VCVio/Quantum/SubInstrument.lean`). The Bell
> state is `bell` in `VCVioTest/Quantum/Basic.lean`, where `frame_measureZ_bell` measures its
> first qubit.

Next: [chapter 4, states you do not fully know](4-states-you-do-not-fully-know.md).
