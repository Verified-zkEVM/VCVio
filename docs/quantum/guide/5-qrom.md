# 5. The quantum random-oracle model

Covers: Classical queries, Deutsch's algorithm, one shared random oracle, parallel rounds,
private uniform coins and classical/compressed execution bridges. Also covers parallel reprogramming, marked search and fixed-target inversion. See
[conventions](../reference/conventions.md). Read first: tutorial
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

* A lossless program starting from a normalized state and making no calls guesses a pair
  $(x, H(x))$ with probability exactly $1/|Y|$
  (`qromEvalDistMap_guess_zero_of_trace_eq_one`). More generally, success is the successful run
  mass divided by $|Y|$ (`qromEvalDistMap_guess_zero`). In both statements, the program, initial
  state and guessing rule are fixed independently of $H$.
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

## Reprogramming a parallel round

Suppose `H` and `H'` agree outside `S`. `parallelInputProjector k S` projects onto the basis
tuples with at least one input in `S`. Repeated inputs belong to this union once.
`parallelOracleUnitary_sub_eq_mul_projector` says the unitary difference is supported on the
union, and `re_trace_parallel_disagreement_le` bounds its squared Kraus weight by four times
the union's input weight. Both statements allow width zero; the latter retains an arbitrary
spectator register and a positive semidefinite input operator.

`rpow_inv_two_parallel_reprogramming_le` compares square roots of acceptance weights after a
common CP, trace-nonincreasing finishing map `Φ`. The oracle changes; the input operator and
`Φ` are shared. After fixing hidden classical challenge data, `Φ` may include subsequent
oracle-dependent computation and verification using those same data. This keeps their
correlation with the final event.

An expected union-weight estimate needs explicit sampling hypotheses.
`sum_mul_re_trace_conj_parallelInputProjector_frame_le` takes a finite challenge family,
nonnegative weights `w ω`, sets `S ω` and the incidence assumption

$$\forall x,\quad \sum_\omega w_\omega\,\mathbf{1}_{x\in S_\omega}\leq\delta.$$

For one common positive semidefinite input `ρ`, independent of `ω`, it bounds the weighted
union mass by `k * δ * trace ρ`. The weights need not sum to one. For example, an incidence
bound `δ = s / N` gives `k * s / N` times the trace. A size bound on each set alone does not
establish the required incidence or independence.

## Adaptive hybrids and marked search

`rpow_inv_two_evalDistMap_parallel_le_support` compares an event under `H` and `H'` by the
square-root hybrid argument. Its query-union weights come from the reference execution under
`H'`. The local interpretation, adaptive program, initial substate and final observation are
the same on both sides. Arbitrary measurements and trace loss are allowed.
The search proofs use `Comp/ChargeWeight.lean` for total point weights and the analytic
cutoff and square-root aggregation helpers in `Foundations/Hybrid.lean`. The latter imports
only QuantumFoundations and is staged for that dependency. `Comp/HybridBudget.lean` supplies
additional total-call and width-cap estimates; the search proofs do not depend on that API.
Its cutoff counts all ports together, avoiding a sum of separate per-port maxima.

`Comp/ChargeWeight.lean` exposes `IsQueryChargeBound` for natural-number port charges.
If a query weight is at most its port charge times its input trace,
`totalWeight_le_of_isQueryChargeBound` bounds all query weights together by the pathwise budget
times the initial trace. Local steps cost zero. Zero-charge calls are allowed, and calls with
no possible answer still spend their charge before aborting. Charging each port one recovers
the total call budget; charging batch widths recovers `IsPointBound` and
`totalWeight_le_of_isPointBound`. The proof follows residual budgets through adaptive branches,
including trace loss, without adding per-port maxima.

For search, sample one uniform `y : X` and answer every slot and round with
`markedFunction y : X → ZMod 2`, which is one at `y` and zero elsewhere. Fix the interpretation
`I`, program `x`, initial substate `ρ` and leaf-to-input guessing rule independently of `y`.
`markedSearchAdvantage` measures the unconditional probability that the guess equals the same
mark used by the oracle. For a finite nonempty domain of cardinality `N`,
`markedSearchAdvantage_le_of_isPointBound` states

$$\Pr[\mathrm{guess}=y]\ \leq\ \min\!\left(1,\frac{(1+2\sqrt{qQ})^2}{N}\right)$$

under `x.IsTotalQueryBound q` and `x.IsPointBound Q`. Widths may depend on earlier outcomes;
`Q` bounds their sum on every branch, including outcomes of weight zero. No width cap is needed.
For example, adaptive two-round profiles `(0, 2)` and `(1, 1)` both have `q = Q = 2`.
The width-cap theorem `markedSearchAdvantage_le` follows by taking `Q = k * q`, recovering
`min 1 ((1 + 2 * q * sqrt k)^2 / N)`. The result allows entangled
query slots, duplicate inputs, mixed states, subnormalized states and width-zero calls. At
`q = 0` or `Q = 0`, the guessing term gives `1 / N`. Failure and postselection retain their missing mass;
the success probability is never renormalized on survival.
The proof sums singleton union weights over all marks in the mark-independent zero-oracle
reference execution before aggregating the square-root errors.

This is the unique-mark oracle experiment. Exact sums of square roots for deterministic width
profiles and changing-property compressed-oracle bounds remain separate work.

## Fixed-target preimage search

`preimageSearchAdvantage target I x ρ guess` samples one uniform function `H : X → Y`
and checks whether `H (guess leaf) = target` after the program finishes. The same `H` answers
every slot and round and supplies this final check. The target, program, local operations,
initial substate and guessing rule are fixed before `H` is sampled. They may depend on the
fixed target. The experiment neither samples the target as `H(x*)` nor conditions it to have
any preimage; those are different games.

`preimageSearchAdvantage_le_of_isPointBound` proves

\[
 p \le \min\left(1,\;\frac{(1+2\sqrt{qQ})^2}{|Y|}\right)
\]

under `x.IsTotalQueryBound q` and `x.IsPointBound Q`. The width-cap corollary,
`preimageSearchAdvantage_le`, gives `min 1 ((1 + 2q * sqrt k)^2 / |Y|)`.
The denominator is the response-space size, whereas unique-mark search uses the input-space
size. Both results permit adaptive widths, repeated inputs, mixed or subnormalized states
and empty rounds. Missing mass counts as failure.

The reference execution must be independent of the sampled preimage set. To ensure this,
`ToMathlib/MeasureTheory/Measure/UniformTable/Target.lean` decomposes a uniform function into
an independent avoiding table and a label table. The avoiding table contains no target values;
the patched function returns the target exactly at target-labelled inputs. A permutation of
the complete tables proves the joint law, including the target preimage set. Each input is
labelled with probability `1 / |Y|`. A uniformly random unrestricted reference would introduce
extra target values and would not give this decomposition. Singleton response spaces use the
trivial probability cap, without sampling an empty target complement.

`Oracle/ParallelFinding.lean` supplies the common argument for both search games.
`sum_mul_evalDistMap_mem_parallel_le_of_isPointBound` bounds a weighted family of hidden-set
finding experiments from a fixed reference oracle and a pointwise incidence bound `δ`.
Each challenge's oracle agrees with the reference outside that challenge's set. The weights
need not normalize: the conclusion is a weighted sum at most
`δ * (1 + 2 * sqrt (q * Q))^2`. The reference runtime, input state, program and guess are held
fixed across the sampled sets; each final event retains its own set. Marked search uses
singleton sets, unit weights and `δ = 1`, then divides the resulting sum by `|X|` for the
uniform hidden mark. Preimage search uses normalized target-label weights and `δ = 1 / |Y|`.

The exact zero-point law, `preimageSearchAdvantage_eq_of_isPointBound_zero`, gives the successful
execution mass at any reference function divided by `|Y|`, even with empty rounds and without
a round bound. For lossless local execution,
`preimageSearchAdvantage_eq_of_isPointBound_zero_of_lossless` gives initial trace divided by
`|Y|`. In particular, a lossless normalized no-query guess succeeds with probability `1 / |Y|`.

## Raw encodings and full-table completion

An encoded oracle can expose less data than the underlying raw hash. For example, leanSeal
uses only the first bytes of a mask hash, but an adversary querying the raw hash receives
all 32 bytes. Raw inputs outside the six typed domains are also valid oracle queries.
Both kinds of data must persist across repeated quantum queries.

`Equiv.tableSplit` gives a complete table decomposition for an injective input encoding
and a response equivalence at each encoded cell. A raw table corresponds to three tables:
the visible typed answers, their complementary tails, and all outside-image answers.
The inverse reconstructs the raw function exactly. Uniform sampling transports through
this bijection, so these tables can be sampled independently without losing a correlation
with the raw function.

`sampledEvalDistMap_tableSplit` applies that decomposition to every program over the
original raw parallel-oracle signature. The program still has coherent access to every
raw input and the full response register. Only the sampled parameter changes; the runtime
uses the same reconstructed function throughout. The observer may inspect that function
jointly with the final leaf. Rounds, points, adaptive branches and missing mass are preserved.
`uniformOn_univ_bind_equiv` gives the corresponding measure-valued reparameterization for
complete experiments, including the three-phase puzzle law.

A prefix-only marginal would be insufficient. Consider two inputs whose raw answers have
the same prefix and different tails. Computing these answers into a zero tail and then
discarding that tail distinguishes the inputs and destroys their coherence. The complete
table decomposition retains the tail and does not perform that discard.

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

`VCVioTest/Quantum/ParallelSearch.lean` checks union mass and coherence with repeated inputs,
nonbinary spectator and common-finisher comparisons, weighted incidence, exact no-query and
width-zero guessing, and full-domain two-slot search. Its adaptive, potentially lossy example
uses a rank-two subnormalized input and the unsaturated bound `9 / 16`.
Two-round adaptive profiles `(0, 2)` and `(1, 1)` give the round/point bound `25 / 64`,
and their total weighted mass is at most one from a half-trace input.
`VCVioTest/Quantum/ChargeWeight.lean` checks prefix charges and exact pre-answer query weight
for a call with no possible answer, including zero-charge calls at budget zero.

`VCVioTest/Quantum/ParallelPreimage.lean` checks fixed-target guessing, singleton responses,
empty domains, unnormalized input mass, adaptive total-point budgets and the avoiding-table
coupling.
