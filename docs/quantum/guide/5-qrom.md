# 5. The quantum random-oracle model

Covers: Classical queries, Deutsch's algorithm, the QROM runtime, classical algorithms in the
QROM and parallel oracle rounds. See [conventions](../reference/conventions.md). Read first: tutorial
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

For a classical algorithm that also samples private coins,
`oa : OracleComp (unifSpec + (X →ₒ Y)) α`, use `oa.toQuantumRandomized` from
`Oracle/ClassicalRandomized.lean`. Uniform samples become local operations via `QComp.coinImpl`;
function queries become ordinary `classicalQuery` calls. `run_toQuantumRandomized` preserves the
complete fixed-function run, and `qromEvalDist₂_toQuantumRandomized_eq_randomOracle` identifies
its law with execution under one lazy random-oracle cache. The budget theorem
`IsQueryBoundP.isQueryBound_toQuantumRandomized` counts the right-hand function queries and leaves
all private samples uncharged. The source and result types lie in `Type`.

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

## Parallel oracle rounds

`qromBatchSpec X Y` is `uBatchSpec Unit (fun _ ↦ QReg.of (X × Y))`. Its classical ports are
pairs `((), k)`, whose second component is the width; programs may vary it between calls.
Port `((), k)` acts on `Fin k → X × Y`, applying the same `H` to each
input/response pair. The basis permutation is
`parallelOracleEquiv H k`, and `parallelOracleUnitary H k` is its matrix. Slots may be
entangled and their inputs may repeat, including when the width exceeds the domain cardinality.

`QuantumRuntime.batch` batches ports with the same input and output register and no classical
result, in increasing slot order with one shared private register. Generic stateful steps need
not commute. This API requires equal `In` and `Out` and `Result = Unit`, so it does not cover the
classical-result checked/read ports of vector commitments. For the additive oracle,
`batch_oracleQuery` proves equality with the simultaneous operation
`parallelOracleQuery H k`, including an arbitrary untouched private register.
`parallelOracleRuntime_step` gives that law for a variable-width runtime.
`intertwines_batch_step` transports private-memory simulations through batching. If the
simulation preserves trace and maps one initial private state to the other,
`evalDist_batch_eq_of_simulation` gives agreement of output laws for adaptive programs.
`parallelOracleRuntime H` is `(additiveOracleRuntime H).batch`, so these generic transport laws
apply directly to the same `qromBatchSpec X Y` signature.

The coordinate subsystems and ordered subinstrument operations live in
`VCVio/Quantum/Foundations/Parallel.lean`. It imports only QuantumFoundations and Mathlib and is
staged for upstreaming to QuantumFoundations; runtime signatures and simulations live in
`VCVio/Quantum/Comp/Parallel.lean`.

`qromBatchEvalDist` samples one function from `X → Y` for the entire run. Its mixture formula,
`qromBatchEvalDist_eq_sum`, uses the original function space, so different slots and rounds
receive answers from the same random oracle. Identifying the parallel oracle with an oracle for
`xs ↦ H ∘ xs` is algebraic: sampling `H` induces a generally correlated law on these derived
functions, rather than the uniform law on all functions between the product spaces.
A width-zero call is the identity. Program-level translation into sequential queries,
with exact point-budget transfer, is provided by `Comp/Sequentialize.lean` as described in
[guide 4](4-programs-and-runtimes.md#sequentializing-batches).

`Oracle/Sequentialize.lean` connects that translation to the QROM. For an arbitrary source
local interpretation `I`, `qromEvalDist_sequentialize` states

```lean
qromEvalDist .instruments (x.sequentialize I) ρ = qromBatchEvalDist I x ρ
```

`qromEvalDistMap_sequentialize` also preserves every observation `f H leaf` of the sampled
function and the classical leaf together. A challenger can therefore check a relation between
the output and the same hidden function that answered every slot and round.
`IsPointBound.qrom_sequentialize` supplies the matching single-port query certificate from the
parallel program's point bound. The adapter is a separate module; `Oracle/Parallel.lean` does
not depend on sequentialization.

## Classical rounds with private coins

`OracleComp.toQuantumBatch` embeds
`oa : OracleComp (unifSpec + (X →ₒ Y).batch) α`. Each list `ts` prepares the register
`Fin ts.length → X × Y` with slot `j` in `|ts[j], 0⟩`, makes one batch call of width `ts.length`,
and measures every response slot. Uniform samples use `QComp.coinImpl` as local operations, so
they spend no oracle budget. Lists preserve order and duplicate positions. An empty list still
makes one width-zero call: one round and zero points.

`run_toQuantumBatch` identifies the full fixed-function run with classical execution against
that table, followed by the coin-only quantum embedding. Adaptive continuations and private
randomness are retained. `sampledEvalDist₂_toQuantumBatch` averages over one function;
`sampledEvalDist₂_toQuantumBatch_eq_randomOracle` gives the same law using the classical lazy
random oracle, with one cache shared across every slot and round. These APIs take `X`, `Y` and
`α` in `Type`, finite `X` and `Y`, and an additive commutative group on `Y`; the sampling laws
also require the corresponding `SampleableType` instances.

The classical budget `IsOnlineQueryBound oa (r, q)` yields the quantum round bound `r` and point
bound `q` by `IsOnlineQueryBound.isTotalQueryBound_toQuantumBatch` and
`IsOnlineQueryBound.isPointBound_toQuantumBatch`. A point-only classical bound transfers by
`IsPointQueryBound.isPointBound_toQuantumBatch`.
`qromEvalDistMap_sequentialize_toQuantumBatch_eq_unbatch` closes the semantic square: embed then
sequentialize, or classically unbatch in list order and run the lazy oracle, and the observed
output laws agree. This is a law equality; the placements of measurements in the two quantum
descriptions differ.

## Parallel compressed execution

`Oracle/Compressed/Parallel.lean` relates `(compressedRuntime X Y).batch` to the parallel QROM.
One private database persists throughout all slots and adaptive rounds. Compression is an isometry
from the purified function register into the compressed database register.
`intertwines_purifiedRuntime_compressedRuntime_batch_step` lifts its intertwining law to each batch;
`matrix_jointPost_compressedRuntime_batch` maps the complete purified joint post-state to the
compressed joint post-state at every leaf, including private memory. The isometry preserves trace,
and `reducedPost_compressedRuntime_batch` identifies the states after discarding private memory.

The purified-to-sampled-function leg uses `trace_jointPost_purifiedRuntime_batch`, a uniform sum
over the fixed functions. It follows the sequential purified row decomposition through exact
stateful sequentialization. Individual `evalRow H` maps need not preserve trace, so this leg
requires the row sum rather than the trace-preserving simulation theorem.

`outcomeLaw_compressedRuntime_batch` identifies the output law with `qromBatchEvalDist`, and
`outcomeLawWith_compressedRuntime_batch` identifies every classical observation `f leaf` with
its parallel QROM law. The results cover arbitrary adaptive local signatures and interpretations,
outcome-dependent final registers, and mixed or subnormalized input states, for finite `X` and
finite abelian `Y`. The compressed observation reads the leaf only. A function-dependent
observation `f H leaf` needs an explicit joint-oracle read, beyond this theorem.

Depth-sensitive security bounds remain open. Exact sequentialization and runtime equivalence
provide the model and transports; direct parallel hybrid/search and changing-property bounds
require separate proofs.

## Checks

**They agree with each other.** Wherever the library offers two descriptions of the same thing, a
theorem says they agree:

| Two descriptions | Agreement |
|---|---|
| the QROM on classical algorithms and the classical random oracle | `qromEvalDist₂_toQuantum_eq_randomOracle` |
| classical private coins and ordinary queries under one lazy random oracle | `qromEvalDist₂_toQuantumRandomized_eq_randomOracle` |
| ordered calls on disjoint slots and the simultaneous additive oracle | `batch_oracleQuery` |
| the parallel oracle matrix and an ordinary oracle on product registers | `parallelOracleUnitary_eq_oracleUnitary_submatrix` |
| parallel and sequential QROM programs, including observations of the sampled function | `qromEvalDistMap_sequentialize` |
| randomized classical rounds and the lazy cached random oracle | `sampledEvalDist₂_toQuantumBatch_eq_randomOracle` |
| quantum sequentialization of the classical embedding and classical unbatching | `qromEvalDistMap_sequentialize_toQuantumBatch_eq_unbatch` |
| compressed parallel execution and the parallel QROM output law | `outcomeLaw_compressedRuntime_batch` |

**They compute the right numbers.** The tests work small examples to exact values: Deutsch's
algorithm. `VCVioTest/Quantum/Parallel.lean` checks cyclic ranges of orders three and five,
repeated inputs, zero-width calls, coherent two-slot inputs, and noncommuting shared-memory steps.
`VCVioTest/Quantum/ParallelBridges.lean` checks joint compression and leaf observations on
subnormalized mixed inputs, adaptive widths and private coins, ordered repeated inputs, cross-round
cache correlation, empty-round accounting and the semantic classical-unbatch endpoint.
