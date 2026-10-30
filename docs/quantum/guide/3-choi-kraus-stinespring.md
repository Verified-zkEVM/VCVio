# 3. Three descriptions of one quantum operation

Covers: Choi matrices, Kraus operators and Stinespring form. See
[conventions](../reference/conventions.md). Read first: tutorial
[chapter 3](../tutorial/3-several-qubits.md),
[chapter 5](../tutorial/5-what-a-quantum-computer-can-do.md); builds on
[guide 1](1-states-and-instruments.md), [guide 2](2-vectors-and-hybrid-bound.md).

The **completely dephasing channel** keeps the diagonal of a matrix and erases the rest:
$\Delta(\rho) = \operatorname{diag}(\rho_{00}, \rho_{11})$ (`VCVioTest.QuantumKraus.dephase`). It
is what happens to a qubit when its computational-basis value leaks to an environment. Here are its
three descriptions.

**Choi matrix.** Apply $\Delta$ to each matrix unit and arrange the results in one matrix on
output $\otimes$ input:

$$C_\Delta = \sum_{a,a'} \Delta(E_{aa'}) \otimes E_{aa'} = \sum_a E_{aa} \otimes E_{aa}
= \operatorname{diag}(1, 0, 0, 1) \qquad (\texttt{choi\_dephase}).$$

It is PSD, as the Choi matrix of every CP map is (`isCP_iff_posSemidef_choi`), and it determines
$\Delta$ (`ofChoi_choi`). The convention is output first and unnormalized, Watrous's $J(\Phi)$.

**Kraus operators.** $\Delta(\rho) = \sum_a K_a\rho K_a^\dagger$ with $K_a = |a\rangle\langle a|$
(`dephase_eq_sum_conj`). Completeness $\sum_a K_a^\dagger K_a = 1$ is the same as trace
preservation (`isTP_sum_conj_iff`). Every CP map has Kraus operators (`isCP_iff_exists_kraus`):
factor its PSD Choi matrix as $Y^\dagger Y$, and read one operator off each row of $Y$.

**Stinespring operator.** Stack the Kraus operators into one map into a larger system,
$S\psi = \sum_a (K_a\psi) \otimes |a\rangle$. Here $S|a\rangle = |a\rangle \otimes |a\rangle$: $S$
copies the basis value into an environment. Then
$\Delta(\rho) = \operatorname{tr}_E(S\rho S^\dagger)$ (`sum_conj_eq_traceRight_comp_conj`), and
$S^\dagger S = 1$, so $S$ is an isometry (`exists_stinespring_of_isTP` gives this for every
channel).

For contrast, the identity channel has Choi matrix $|\Omega\rangle\langle\Omega|$, of rank one, and
the single Kraus operator $1$ (`choi_id`, `id_eq_sum_conj`). The Choi matrix of the transpose map
from [guide 1](1-states-and-instruments.md#why-completely-positive) is the swap, which is not PSD;
this is another way to see that the transpose is not CP.

Kraus operators are what connect the general semantics to vector arguments. A branch of a program
is a CP map, and its Kraus decomposition turns it into a sum over operators, each acting on vectors.
Along two successive steps the operators multiply (`branch_bind_eq_sum_conj_mul`). Different Kraus
paths are classical alternatives: their output matrices add, not their vectors.

## Checks

**They agree with each other.** Wherever the library offers two descriptions of the same thing, a
theorem says they agree:

| Two descriptions | Agreement |
|---|---|
| CP maps, Choi matrices, Kraus operators, Stinespring operators | `isCP_iff_posSemidef_choi`, `isCP_iff_exists_kraus`, `sum_conj_eq_traceRight_comp_conj` |

**They compute the right numbers.** The tests work small examples to exact values: the Choi
matrices of the identity and dephasing channels.
