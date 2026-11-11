# 1. States, measurements and failure

Covers: States, measurements, failure, instruments, outcome-dependent outputs, infinite outcomes and
final observation. See [conventions](../reference/conventions.md). Read first: tutorial
[chapter 1](../tutorial/1-coins-to-qubits.md), [chapter 3](../tutorial/3-several-qubits.md),
[chapter 4](../tutorial/4-states-you-do-not-fully-know.md),
[chapter 5](../tutorial/5-what-a-quantum-computer-can-do.md); builds on no earlier guide.

## A first example: measuring `|+⟩`

A qubit has two basis states, $|0\rangle$ and $|1\rangle$. In Lean its basis is `Fin 2`, and
its state space is $\mathbb{C}^2$. The state

$$|+\rangle = \tfrac{1}{\sqrt 2}\,(|0\rangle + |1\rangle)$$

is an equal superposition. We describe states by **density matrices**: the density matrix of
$|+\rangle$ is

$$\rho = |+\rangle\langle +| = \tfrac12 \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}
\qquad (\texttt{VCVioTest.QuantumBasic.plus}).$$

Measuring in the computational basis has one **Kraus operator** per outcome,
$K_0 = |0\rangle\langle 0|$ and $K_1 = |1\rangle\langle 1|$. Outcome $a$ leaves the matrix

$$\Phi_a(\rho) = K_a \rho K_a^\dagger = \tfrac12\, |a\rangle\langle a| ,$$

and the probability of $a$ is its trace, $\operatorname{tr}\Phi_a(\rho) = \tfrac12$. This is the
**Born rule**.

| Step | Mathematics | Lean |
|---|---|---|
| the measurement | $\Phi_a(\rho) = K_a\rho K_a^\dagger$ | `measureZ := SubInstrument.ofKraus proj …` |
| completeness | $K_0^\dagger K_0 + K_1^\dagger K_1 = 1$ | `sum_conjTranspose_proj_mul_proj` |
| probability of $a$ | $\operatorname{tr}\Phi_a(\rho) = 1/2$ | `measureZ.outcomeMeasure plus {a} = 1/2` |
| state after $a$ | $\tfrac12\,\lvert a\rangle\langle a\rvert$ | `measureZ.post plus a` |
| no loss | $\sum_a \operatorname{tr}\Phi_a(\rho) = \operatorname{tr}\rho$ | `lossless_measureZ` |

Two features of this example run through the whole library.

**The state after an outcome is not renormalized.** `post` returns $\tfrac12|a\rangle\langle a|$,
not $|a\rangle\langle a|$: its trace is the probability of $a$. Textbooks usually divide by that
probability to get the conditional state. Keeping the weight inside the state means that an
outcome of probability zero needs no special case, and that composing measurements multiplies
probabilities automatically. Measuring again gives
$\Phi_b(\tfrac12|a\rangle\langle a|) = \tfrac12\,\delta_{ab}\,|a\rangle\langle a|$: the two
outcomes agree, and the probability $\tfrac12$ of the pair $(a, a)$ is already there, with no
second factor.

**Failure is missing trace.** A computation that may fail is described by maps whose traces add up
to *at most* the trace of the input. The deficit is the probability of failure. This is how
`OracleComp` treats failure as missing probability mass; there is no failure outcome.

## Why density matrices

Measuring $|+\rangle$ in the computational basis and forgetting the outcome leaves
$\Phi_0(\rho) + \Phi_1(\rho) = \tfrac12 \cdot 1$, a fair coin. No vector $\psi$ has
$|\psi\rangle\langle\psi| = \tfrac12 \cdot 1$, since that matrix has rank two. Forgetting an outcome
*can* produce such a **mixed state** (it need not: the same measurement on $|0\rangle$ leaves
$|0\rangle\langle 0|$), and density matrices describe mixed states as well as pure ones
([tutorial chapter 4](../tutorial/4-states-you-do-not-fully-know.md)).
[Guide 2](2-vectors-and-hybrid-bound.md) shows when vectors suffice and how the two descriptions are
connected.

## Why *completely* positive

A density matrix is **positive semidefinite** (PSD) with trace one; a `SubState` relaxes the trace
to at most one. A map that sends PSD matrices to PSD matrices is **positive**. Positivity is not
enough, because the system a map acts on may be entangled with a system it leaves alone
([tutorial chapter 5](../tutorial/5-what-a-quantum-computer-can-do.md)).

The transpose $T(\rho) = \rho^{\mathsf T}$ is positive. Take the normalized Bell state
$|\Omega\rangle = \tfrac{1}{\sqrt2}(|00\rangle + |11\rangle)$ and transpose only the first qubit:

$$(T \otimes \mathrm{id})(|\Omega\rangle\langle\Omega|) = \tfrac12 \sum_{a,a'} E_{a'a} \otimes E_{aa'}
= \tfrac12\,\mathrm{SWAP},$$

where $E_{aa'} = |a\rangle\langle a'|$. The swap has the eigenvector $|01\rangle - |10\rangle$ with
eigenvalue $-1$, so the result has eigenvalue $-\tfrac12$ and is not a state. A map $\Phi$ is
**completely positive** (CP) when $\Phi \otimes \mathrm{id}_R$ is positive for every finite
reference system $R$ (`MatrixMap.IsCP`, with $R = $ `Fin k`; `IsCP.amplify_posSemidef` covers every
finite $R$). The reference is always the right tensor factor: `amplify Φ R` is
$\Phi \otimes \mathrm{id}_R$.

| Term | Condition | Lean |
|---|---|---|
| quantum operation | CP and trace nonincreasing | `IsCP`, `IsTNI` |
| quantum channel | CP and trace preserving | `IsCP`, `IsTP` |
| Kraus map | $\rho \mapsto K\rho K^\dagger$, always CP | `MatrixMap.conj K`, `isCP_conj` |

`IsTNI` alone is not a physicality condition: $-\mathrm{id}$ satisfies it. Physical maps are
always required to be CP as well.

## Instruments: one operation per outcome

A computation that reports classical outcomes is an **instrument**: one CP map per outcome, whose
sum is a channel. We allow failure, so we use **subinstruments**: CP maps
$\Phi_a : M_A \to M_B$, one per $a \in \alpha$, such that

$$\sum_{a \in s} \operatorname{tr}\Phi_a(\rho) \le \operatorname{tr}\rho
\quad\text{for every finite } s \text{ and every PSD } \rho$$

(`SubInstrument A B α`). A subinstrument is `Lossless` when the sum of its branches preserves
trace. On one register `M`, `SubInstrument M M` is a lawful monad, and its operations read as they
do for `OracleComp`, with CP maps in place of probabilities:

| Operation | Classical (`OracleComp`) | Quantum (`SubInstrument M M`) |
|---|---|---|
| `pure a` | return `a` | return `a`, leave the state unchanged |
| `p.bind k` | run `p`, then `k` on its result | run `p`, then `k a` on the state `p` left after `a`: $(p \mathbin{>\!\!>\!\!=} k)_b(\rho) = \sum_a (k\,a)_b(p_a(\rho))$ |
| `map f p` | relabel the result | relabel; outcomes with the same label have their maps added |
| `fail` | probability mass zero | every branch zero |
| `frame R p` | — | run `p` beside an untouched system `R`: $p_a \otimes \mathrm{id}_R$ |

The difference from the classical case is in `bind`: the continuation receives a quantum state, not
just a value. So a quantum computation cannot be summarized by the probabilities of its outcomes.
`map` merges outcomes by adding their CP maps; this forgets classical information and creates no
interference.

## Outputs that depend on the outcome

A measurement may keep the qubit on one outcome and discard it on the other. In
`VCVioTest.QuantumBasic.measureKeep`, outcome $0$ keeps the qubit ($K_0 = |0\rangle\langle 0|$)
and outcome $1$ discards it ($K_1 = \langle 1|$, a $1 \times 2$ matrix). The output system on
outcome $1$ is `Unit`, which is one-dimensional, not empty: the state there is the $1 \times 1$
matrix $\langle 1|\rho|1\rangle = \tfrac12$, which carries only the weight of the branch.

Such families are **dependent subinstruments** (`DSubInstrument A ι B`), with output system `B i`
on outcome `i`. A subinstrument is the case of a constant output system: `SubInstrument A B α` is
an abbreviation of `DSubInstrument A α (fun _ ↦ B)`, so the operations above and their laws are
the dependent ones, applied to a constant family. Different outcomes are classical alternatives:
there are no off-diagonal blocks between them.

## Infinitely many outcomes

The outcome type may be infinite, even uncountable; only countably many branches can then be
nonzero, and their traces converge (`IsCPTNIFamily.summable_apply`, `countable_support_branch`). For
example `VCVioTest.QuantumBasic.geometric` reports $n \in \mathbb{N}$ with probability $2^{-(n+1)}$
and leaves the state otherwise unchanged; it is lossless because $\sum_n 2^{-(n+1)} = 1$.

The reason for allowing this is loops. The loop "prepare a fresh $|+\rangle$, measure it, stop on
$0$" stops after round $n$ with probability $2^{-n}$, so every positive $n$ is an outcome. Loops are
not defined yet, but a definition as the limit of finite unrollings will need infinitely many
outcomes, and the model already has them.

## Observing once, at the end

`p.outcomeMeasure ρ` is the distribution of the outcome: a Mathlib measure giving
outcome $a$ the weight $\operatorname{tr}p_a(\rho)$. States may be subnormalized (`SubState`: PSD
with trace at most one), so the measure has total mass at most one, and the missing mass is failure.

The chain rule `outcomeMeasure_bind` composes outcome measures through the unnormalized post-states:

$$\Pr[p \mathbin{>\!\!>\!\!=} k \text{ reports } b] = \sum_a \operatorname{tr}\,(k\,a)_b\big(p_a(\rho)\big).$$

`SubInstrument.semanticsVia ρ₀` packages this as a VCVio `SemanticsVia`, observing from a fixed
initial state. Its interpretation is a monad morphism, but its observation is not: the distribution
of the outcome of `p.bind k` depends on the quantum state `p` leaves, which the distribution of `p`
forgets.

## Checks

**They match the textbook.** Each definition is stated as in Watrous's *The Theory of Quantum
Information*, with the differences explained where they occur: subinstruments allow failure and
countably many outcomes, and dependent subinstruments allow the output system to vary. The table
[against the literature](../reference/literature.md) gives page references.

**They agree with each other.** Wherever the library offers two descriptions of the same thing, a
theorem says they agree:

| Two descriptions | Agreement |
|---|---|
| trace bound on finite sets of outcomes, and trace nonincrease of every finite sum of branches | `DSubInstrument.isTNI_sum`, `SubInstrument.ofIsTNISum` |
| losslessness, and the total map being a channel | `DSubInstrument.lossless_iff_isTP_total` |

**They compute the right numbers.** The tests work small examples to exact values: the Born
probabilities above; a measurement with outcomes in $\mathbb{N}$.
