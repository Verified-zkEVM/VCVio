# Glossary

This glossary collects the mathematical terms and Lean names used in the
[guides](../guide/README.md); the [conventions](conventions.md) fix their notation.

**Basis, register.** A finite type `A` whose elements label an orthonormal basis of
$\mathbb{C}^A$. A register of a program is such a type, bundled as `QReg`.

**Bra, ket.** $|\psi\rangle$ is a column vector, $\langle\psi|$ its conjugate transpose, and
$|\psi\rangle\langle\phi|$ the matrix `ketBra ψ φ`.

**Born rule.** Outcome $a$ of an instrument on $\rho$ has probability
$\operatorname{tr}\Phi_a(\rho)$; on a vector, $\|K_a\psi\|^2$.

**Channel.** A CP, trace-preserving map: a quantum operation that cannot fail.

**Choi matrix.** The matrix $\sum_{a,a'}\Phi(E_{aa'}) \otimes E_{aa'}$ that determines $\Phi$; PSD
exactly when $\Phi$ is CP.

**Completely positive (CP).** $\Phi \otimes \mathrm{id}_R$ is positive for every finite $R$.

**Density matrix.** A PSD matrix of trace one; a state. `SubState` allows trace below one.

**Dependent subinstrument.** A subinstrument whose output system depends on the outcome.

**Entanglement.** A state of a product system that is not a mixture of product states, such as
$|00\rangle + |11\rangle$.

**Instrument.** One CP map per classical outcome, summing to a channel.

**Kraus operators.** Operators $K_i$ with $\Phi(\rho) = \sum_i K_i\rho K_i^\dagger$.

**Lossless.** The sum of the branches preserves trace: nothing is lost to failure.

**Mixed and pure states.** A pure state is $|\psi\rangle\langle\psi|$; a mixed state is any other
density matrix, such as $\tfrac12 \cdot 1$.

**Partial trace.** Discarding a subsystem: `traceRight`.

**Port.** One operation of an oracle signature, with input and output registers and a classical
result.

**Positive semidefinite (PSD).** Hermitian with nonnegative eigenvalues; Mathlib's
`Matrix.PosSemidef`.

**Post-state.** The unnormalized state left after an outcome; its trace is the outcome's
probability.

**Program.** A tree of local operations and oracle calls (`QuantumComp`).

**Quantum operation.** A CP, trace-nonincreasing map: it may fail.

**QROM.** The quantum random-oracle model: a uniformly random function queried through $U_H$.

**Runtime.** An implementation of an oracle signature, with private quantum memory.

**Stinespring operator.** A single operator into system $\otimes$ environment that, followed by a
partial trace, gives the map.

**Subinstrument.** An instrument whose branches may lose trace; the loss is failure.

**Unitary, isometry, contraction.** $U^\dagger U = UU^\dagger = 1$; $V^\dagger V = 1$;
$\|K\| \le 1$, equivalently $K^\dagger K \le 1$.
