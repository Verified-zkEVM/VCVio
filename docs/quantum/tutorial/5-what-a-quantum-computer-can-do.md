# 5. Everything a quantum computer can do

We now have states (density matrices) and some steps: gates, measurements, throwing a register
away. This chapter collects all the steps a quantum computer can take, finds the single form they
all share, and explains the condition, **complete positivity**, that VCVio uses to say which maps
on density matrices are allowed.

## Four kinds of step, plus classical control

Every quantum algorithm is built from these:

1. **Add a fresh register** in a fixed state, say $|0\rangle$:
   $\rho \mapsto \rho \otimes |0\rangle\langle 0|$.
2. **Apply a gate** $U$: $\rho \mapsto U\rho\, U^\dagger$.
3. **Measure** a register and record the outcome: outcome $a$ leaves the unnormalized
   $\rho_a$ of chapter 4.
4. **Throw away a register**: the partial trace.

On top of these, the next step may depend on outcomes already recorded, exactly as a classical
program branches on a value it computed. Ordinary randomness fits in too: a coin flip is "add a
fresh qubit, apply $H$, measure".

## One form for all of them

Take any sequence of such steps and fix the record of outcomes $a$. The map from the initial
density matrix to the final, unnormalized one always has the same shape:

$$\rho \;\longmapsto\; \sum_k K_k\, \rho\, K_k^\dagger$$

for some matrices $K_k$ (which depend on $a$). These are the **Kraus operators** of the step.

* A gate has one Kraus operator, $U$ itself.
* Measuring outcome $a$ has one, the projection $|a\rangle\langle a|$:
  $|a\rangle\langle a|\,\rho\,|a\rangle\langle a| = \rho_{aa}\,|a\rangle\langle a|$, which is
  chapter 4's $\rho_a$.
* Throwing away a qubit has two, one per value $r$ of the discarded qubit ("keep the part of the
  state where it is $r$"); adding their contributions is the partial trace.
* Adding a fresh register has one, the matrix that appends $|0\rangle$.

The $K_k$ may be rectangular, since the output system can differ from the input system.

Probabilities can only be lost along the way, never created: summed over all outcomes, the traces
of the outputs add up to at most the trace of the input. When nothing can fail they add up to
exactly that.

## The standard names

* A map $\rho \mapsto \sum_k K_k \rho K_k^\dagger$ that does not increase the trace is a **quantum
  operation**; one that preserves the trace is a **quantum channel**. Measuring and forgetting is
  a channel; "measure and keep only outcome $0$" is an operation that loses probability.
* A family of operations, one per outcome, whose total does not increase the trace is an
  **instrument**. It describes one step with a classical outcome *and* a quantum state left
  behind. Gates (one outcome), measurements, and whole algorithms with an output are all
  instruments.

VCVio calls its instruments **subinstruments**: "sub" because the total may lose trace, which is
failure, just as a subdistribution may lose probability mass.

## Which maps are allowed? Complete positivity

VCVio does not define operations by "has Kraus operators". It uses an equivalent condition that
says directly what a step must do: **turn states into states, even when it acts on part of a
larger system.** Here is why the second half matters.

A map $\Phi$ on matrices is **positive** if it sends PSD matrices to PSD matrices, so states to
(unnormalized) states. That is clearly necessary, but it is not enough. The **transpose**
$T(\rho) = \rho^{\mathsf T}$ is positive: transposing does not change eigenvalues, so a state stays
a state. Now apply it to the first qubit of a Bell pair (chapter 3), leaving the second qubit
alone. The Bell state's density matrix is
$\tfrac12 \sum_{a,b} |aa\rangle\langle bb|$, and transposing the first factor of each term
$|a\rangle\langle b| \otimes |a\rangle\langle b|$ gives
$|b\rangle\langle a| \otimes |a\rangle\langle b|$. The result is

$$\tfrac12 \sum_{a,b} |ba\rangle\langle ab| = \tfrac12\,\mathrm{SWAP},$$

the matrix that swaps the two qubits, times $\tfrac12$. It has the eigenvector
$|01\rangle - |10\rangle$ with eigenvalue $-\tfrac12$, so some measurement would get a "probability"
of $-\tfrac12$. The transpose is fine on a qubit alone and nonsense on half of an entangled pair.

So the right condition is: $\Phi$ is **completely positive** (CP) if $\Phi \otimes \mathrm{id}_R$,
which applies $\Phi$ to the first system and leaves a second system $R$ alone, is positive for
every finite system $R$. A cryptographic experiment always has such an $R$, the registers the
current step does not touch, so CP is exactly the guarantee needed.

Two theorems tie the threads together:

* every map of the form $\rho \mapsto \sum_k K_k \rho K_k^\dagger$ is CP, and every CP map on finite
  systems has this form (the **Kraus** or **Choi** theorem);
* every CP trace-nonincreasing map can be built from the four kinds of step above: append a fresh
  register, apply one operator, throw a register away (the **Stinespring** form).

So "CP and trace nonincreasing", "has Kraus operators with $\sum_k K_k^\dagger K_k \le 1$", and
"built from the four steps" all describe the same maps.

## Steps in sequence

Running one instrument, then choosing the next one from the outcome, is again an instrument. This
is sequencing, the same idea as `bind` for VCVio's classical computations: an `OracleComp`
produces a value and the rest of the program depends on it. The probability of a sequence of
outcomes is the trace of the final unnormalized state, which multiplies the probabilities step by
step with no division (chapter 4).

## So far

* All steps share one form, $\rho \mapsto \sum_k K_k \rho K_k^\dagger$, per outcome.
* Operation = trace nonincreasing; channel = trace preserving; instrument = one operation per
  outcome.
* Allowed steps are the completely positive ones: they stay valid on part of an entangled system.
  The transpose is positive but not CP.
* Instruments compose like classical programs, with the probability carried in the trace.

> **In VCVio.** A linear map on matrices is a `MatrixMap A B` (`QuantumFoundations/MatrixMap.lean`).
> `IsCP`, `IsTNI` and `IsTP` are complete positivity, trace nonincreasing and trace preserving;
> `conj K` is $\rho \mapsto K\rho K^\dagger$, CP by `isCP_conj`. A subinstrument `SubInstrument A B
> α` has a CP branch for each outcome in `α` and a total that does not increase the trace
> (`QuantumFoundations/SubInstrument.lean`). On a fixed system, `SubInstrument M M` is a lawful
> monad in the outcome type, so `do` notation sequences instruments as it sequences `OracleComp`
> programs. The Kraus, Choi and Stinespring theorems are `isCP_iff_exists_kraus`,
> `isCP_iff_posSemidef_choi` and `IsCP.exists_stinespring_of_isTNI`
> (`QuantumFoundations/MatrixMap/Kraus.lean`).

Next: [chapter 6, quantum queries and the QROM](6-quantum-queries.md).
