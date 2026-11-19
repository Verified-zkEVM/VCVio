# Quantum layer: design and open obligations

This page records why VCVio's quantum layer has the shape it has and what remains to be proved or
built. For an explanation of the layer itself, read [`docs/quantum/`](../quantum/README.md)
first. The original plan is in #706. Open work is tracked in #964 (execution model), #965
(reductions and cost) and #966 (remaining quantum random-oracle results).

## Status

The Mathlib-only base (completely positive maps, subinstruments, Choi–Kraus and Stinespring forms,
observation, pure states and oracle unitaries) lives in
[QuantumFoundations](https://github.com/lean-crypto-foundations/QuantumFoundations), shared with
CatCrypt, and VCVio imports it since #921. The rest of the layer is in `VCVio/Quantum/`.

Merged:

| PR | Content |
|---|---|
| #850 | Quantum operations, subinstruments, dependent subinstruments, outcome measures, partial trace |
| #851 | The classical instability calculus on query caches |
| #852 | State vectors, operator norms and the bridge to density matrices; the hybrid bound |
| #853 | Quantum programs, runtimes, the QROM, classical algorithms in the QROM, combs |
| #854 | Choi matrices, Kraus operators and Stinespring form |
| #855 | The compressed random oracle as a quantum runtime |
| #856 | How much one compressed-oracle query can disturb a database property |
| #857 | Query mass and the hybrid argument for general quantum programs |
| #858 | Vector commitments, multi-extractors and salted Merkle trees |
| #859 | The optimal constant 24 for compressed-oracle commutator bounds, including checked reads |
| #860 | Emulated quantum oracles, classical reads and total call budgets |
| #861, #862, #864, #871, #873–#875, #877 | Multi-extractable vector commitments against quantum adversaries |
| #878 | The tutorial, guide and reference in [`docs/quantum/`](../quantum/README.md) |
| #882 | Subsystems and lifting programs along them |
| #903, #916, #917 | Sequencing, budgets and execution through PolyFun's indexed bind and fold |
| #904 | Existing Mathlib and VCVio lemmas in place of local copies |
| #921 | The Mathlib-only base taken from QuantumFoundations |

## Decisions

**Programs and runtimes are the definition.** A quantum oracle algorithm is a program
(`QuantumComp`) run against a runtime (`QuantumRuntime`). Fixed-slot forms, such as the comb
$U_q O \cdots O U_0$, are derived: they embed as programs (`QuantumComb.run_toComp`), and theorems
about them apply to the programs they embed as. Taking a normal form as the definition would make
adaptive measurement, outcome-dependent registers, several oracles and stateful oracle
implementations into encodings that each theorem has to undo.

**Failure is missing trace.** Subinstruments are trace nonincreasing, so failure needs no outcome
and composes as `OracleComp`'s missing probability mass does. Lossless subinstruments are a
predicate, not a separate type.

**Post-states are unnormalized.** The state after an outcome carries the outcome's probability as
its trace. Zero-probability outcomes need no case split, and the chain rule
(`outcomeMeasure_bind`) has no division.

**Outputs may depend on the outcome.** `DSubInstrument A ι B` has output system `B i` on outcome
`i`, which is how programs allocate and discard registers. `SubInstrument A B α` is the constant
case, defined as an abbreviation of `DSubInstrument A α (fun _ ↦ B)` in the way Mathlib's `FunLike`
specializes `DFunLike`, so every dependent definition and theorem applies to it directly. Only what
needs one output system lives on `SubInstrument`: the total map, `ofMap`, and the monad on
`SubInstrument M M` (`DSubInstrument` is an indexed monad, since `ret` changes the input system).

**Outcomes may be infinite.** Outcome types are arbitrary, and only countably many branches of
an instrument are nonzero. This is needed before loops can be defined as limits of finite
unrollings, and costs nothing in the finite case.

**Registers are finite and live in `Type`.** `QReg` bundles a finite type in `Type`. Every finite
type is equivalent to some `Fin n`, so nothing is lost, and register-indexed families stay in
`Type 1`. Outcome and result types may live in any universe.

**One semantic primitive per call.** A port call acts on (port input $\times$ untouched rest) and
the runtime's private register, through basis equivalences supplied by the program. The program
cannot read the private register except through calls.

## Coverage and remaining obligations

### 1. Putting programs in comb form

`run_toComp` proves that every comb is a program. The converse, that a program has an equivalent
comb, is not proved, and the following shows it needs hypotheses.

**Candidate statement.** Suppose the runtime has a single port, that its classical result is trivial
(`Result = Unit`), and that it has an *idle input*: a state on which a call changes nothing, the
private register included. Then every lossless program making at most $q$ calls on every path should
have a $q$-slot comb with the same joint distribution of output and private register. The comb would
pad short paths with idle calls and carry the classical history of the program in a register.

**Each hypothesis is needed.**

* *Trivial results.* A comb discards the classical result of each call (`combQuery`). Against a
  port that measures a private uniform bit and returns it, a one-call program outputs a bit
  correlated with the private register, and no comb does.
* *Losslessness.* The steps of a comb are lossless. Take a private bit $d$ that starts uniform,
  and a port that, on control $1$, adds $d$ to a target bit and, on control $0$, does nothing; no
  call changes $d$. Every operation of a comb against this runtime is lossless and preserves $d$,
  so the marginal of $d$ stays uniform. A program that copies $d$ with one call and fails when the
  copy is $1$ leaves weight only on $d = 0$. (The invariant belongs to this runtime: a port that
  resets $d$ to $0$ on control $1$ lets a lossless comb make $d$ deterministic.)
* *An idle input.* Against a runtime that counts its calls, a program whose paths make different
  numbers of calls leaves the counter in a mixture that a comb, which always makes $q$ calls,
  does not produce. The test `coinCounterDist_eq` computes the program side; the statement over all
  combs is not formalized.
* *One port.* With several ports, a comb fixes the order of its calls in advance.

**The history register.** The literal construction stores the outcomes so far in a classical
register $H$. Outcome types may be infinite, and later registers may depend on earlier outcomes with
no uniform bound on their dimension, so $H$ need not be a finite register. A converse therefore
needs one of: finitely many outcomes on every path; a uniform bound on the registers reached; or a
compression argument showing that a finite register suffices for the joint distribution. Which of
these to adopt should follow the first application that needs the converse.

### 2. Coherent choice of port

The port of a call is chosen by a classical outcome. A circuit that queries "oracle $b$" for $b$
in superposition is not expressible directly. Two routes: a port whose input register includes the
selector, implemented by a runtime that dispatches coherently; or an isometric program layer with
controlled calls. The first needs no change to the program syntax; the second is more faithful to
circuit diagrams.

### 3. Loops

Programs are well-founded trees: every path is finite, although with infinite branching path
lengths need not have a common bound (sample $n$, then make $n$ steps). What is missing is
executions that may not terminate, such as "repeat until success", whose infinite path has
probability zero. The plan is a coinductive program type whose semantics is the supremum of finite
unrollings; subinstruments with countably many outcomes already provide the limits. Expected cost
needs separate treatment.

### 4. Classical algorithms with private randomness

`OracleComp.toQuantumAt` with `QComp.coinImpl` runs a classical sampler `oa : ProbComp α`
inside any quantum runtime. `branch_run₂_toQuantumAt_coinImpl` proves that its branch at `a` is
exactly `Pr{let x ← oa}[x = a]` (converted to a complex scalar) times the identity on both the
held register and the runtime's private register. `outcomeMeasure_run₂_toQuantumAt_coinImpl`
identifies the full outcome measure with `𝒟[oa]` scaled by the trace of the joint input substate,
including correlated inputs. Its `…_apply_singleton` corollary gives each `a` its classical
probability times that trace.

`OracleComp.toQuantumBatch` embeds algorithms over `unifSpec + (X →ₒ Y).batch`: private uniform
samples become local coins, and each list round becomes one parallel basis call. Its fixed-function
run and its law averaged over one random function agree with the corresponding classical
execution, including the lazy cached random oracle. The source and result types lie in `Type`.
`OracleComp.toQuantumRandomized` embeds the single-port source
`OracleComp (unifSpec + (X →ₒ Y)) α` with ordinary basis calls and local coins.
`qromEvalDist₂_toQuantumRandomized_eq_randomOracle` proves agreement with the lazy random oracle.
Its query-bound transfer counts only function queries, leaving private samples uncharged.
Both the single-port and batch APIs therefore cover classical algorithms with private uniform
randomness. Their result-universe restriction is the separate obligation below.

### 5. Result universes of the classical embedding

`OracleComp.toQuantum` takes `α : Type`, while combs and programs take results in any universe.
Generalizing it needs universe generalizations in the classical layer first: `simulateQ`,
`evalWithAnswerFn`, `IsTotalQueryBound` and `randomOracle`.

### 6. One Stinespring operator for an instrument

`exists_kraus_branch` gives Kraus operators for each branch separately. For finitely many outcomes
these assemble into one isometry into (output $\times$ outcome $\times$ environment). For infinitely
many outcomes the outcome register is infinite-dimensional, so a single Stinespring operator is
outside the finite-dimensional setting; branchwise operators are what the current applications
need.

### 7. Kraus operators of whole programs

`branch_bind_eq_sum_conj_mul` gives the Kraus operators of a bind of two stages with finitely many
intermediate outcomes, as products along paths. Extending this to whole programs, by induction on
the tree and with countable sums of paths, gives every run a path expansion, which vector-level
arguments such as the hybrid bound need.

### 8. Signature morphisms and compilation

A map from one local signature to programs over another (compiling gates to a gate set, or one
oracle signature to another) should act on programs by substitution, with a theorem that execution
commutes with it. This is the quantum analogue of `simulateQ`, and makes cost bounds relative to a
gate set.

### 9. Cost

`IsCostBound` counts invocations of named local operations. Classical computation between steps
and the basis equivalences supplied to calls are not charged, and those equivalences are arbitrary
basis permutations. So a cost bound is a bound on named gate invocations, not a circuit-size or
polynomial-time certificate. A gate-level account needs item 8 and a charge for the equivalences.

### 10. The compressed oracle

Zhandry's compressed oracle is a runtime with the same law as the QROM for every program (#855),
and the Chiesa–Manohar–Spooner bound and its successors are proved on top of it (#856, #859, #862,
#864, #873–#875, #877). The general final-measurement lemma and compressed-oracle output bounds for collision
and zero-preimage events remain open (#966).

### 11. Parallel oracle rounds

`Foundations/Parallel.lean` holds coordinate subsystems and ordered subinstrument batching facts.
It imports only QuantumFoundations and Mathlib and is staged for upstreaming to QuantumFoundations.
`Comp/Parallel.lean` constructs runtime batches with a shared private register. Its current API
requires equal `In` and `Out` and `Result = Unit`; classical-result checked/read ports of vector
commitments are outside this scope. General stateful batches carry no implicit commutation assumption.

`Oracle/Parallel.lean` specializes `uBatchSpec` to base port `Unit`, so a classical port is
`((), k)` with width in its second component. It proves that ordered additive calls agree with a
simultaneous query on all slots and defines the parallel QROM law by sampling one function for
the entire program. Repeated inputs and entangled query registers are allowed.
`parallelOracleRuntime H` is `(additiveOracleRuntime H).batch`, so the generic private-memory
simulation transport applies directly with the same signature. A trace-preserving simulation
that maps the initial private states gives output-law agreement for adaptive programs.

`Comp/RoundBound.lean` separates the number of rounds (`IsTotalQueryBound`), the per-batch width
cap (`IsWidthBound`) and the sum of widths on each path (`IsPointBound`). These bounds constrain
all branches, including zero-weight outcomes. A width-zero batch spends one round and zero points;
a round bound `r` and width cap `k` imply a point bound `k * r`.

`Comp/Sequentialize.lean` defines the named command substitution `sequentializeHandler I` and
the program translation `x.sequentialize I`. An arbitrary source local signature is interpreted
into `LocalSig.instruments`, which also supplies public register relabellings. For every stateful
base runtime `R`, `run_sequentialize` identifies its full run with `R.batch.run I x`, including
private memory and outcome-dependent final registers. The calls retain their order and one shared
private register. `IsPointBound.sequentialize` transfers the same point budget to a total query
budget; `IsTotalQueryBound.sequentialize` gives the `k * r` form. A zero-width translation makes
no oracle calls but can retain a public relabelling. These are oracle-query certificates;
local-operation and gate costs are not preserved by the statement.

The separate adapter `Oracle/Sequentialize.lean` proves `qromEvalDist_sequentialize` and
`qromEvalDistMap_sequentialize`. The latter preserves observations depending jointly on the sampled
function `H` and the returned leaf, retaining their correlation. `Oracle/Parallel.lean` remains
independent of the translation.

`Oracle/ClassicalParallel.lean` supplies the classical bridge. `OracleComp.toQuantumBatch` prepares
one slot per list position, makes one call, and measures the responses. Private uniform coins use
`QComp.coinImpl` without oracle calls. `run_toQuantumBatch` identifies the complete fixed-function
run, and `sampledEvalDist₂_toQuantumBatch_eq_randomOracle` identifies its averaged law with the
classical lazy oracle using one cache. Input order and duplicates are retained; an empty list
spends one round and zero points. `IsOnlineQueryBound.isTotalQueryBound_toQuantumBatch` and
`IsOnlineQueryBound.isPointBound_toQuantumBatch` transfer the classical round and point budgets;
`IsPointQueryBound.isPointBound_toQuantumBatch` transfers a point-only bound.
`qromEvalDistMap_sequentialize_toQuantumBatch_eq_unbatch` connects quantum sequentialization to
classical list-order unbatching through their observed laws. The program trees need not coincide:
their measurements occur at different stages.

`Oracle/Compressed/Parallel.lean` supplies the concrete compressed bridge. The compression
isometry intertwines purified and compressed batch steps and maps their complete joint
post-states, including private memory (`matrix_jointPost_compressedRuntime_batch`). Discarding
private memory gives equal reduced post-states and leaf weights. The purified-to-sampled-function
comparison uses the sequential row decomposition through exact sequentialization. The `evalRow H`
maps need not preserve trace, so that leg uses the sum over functions rather than trace-preserving
simulation transport. `outcomeLaw_compressedRuntime_batch` gives the parallel QROM output law,
and `outcomeLawWith_compressedRuntime_batch` gives every classical observation of the leaf.
These results allow arbitrary adaptive local signatures and interpretations, mixed or
subnormalized input states, finite domains and finite abelian response groups. A plain compressed
leaf observation does not read `H`; observations `f H leaf` require an explicit joint-oracle read.

The M2a model and transport obligations are complete.

### 12. Parallel reprogramming, hybrids and search

`Oracle/ParallelReprogramming.lean` defines `parallelInputProjector`, the union of slots whose
inputs lie in a disagreement set. The difference of two parallel oracle unitaries is supported
on this union; its squared Kraus weight is at most four times the union's input weight.
`rpow_inv_two_parallel_reprogramming_le` compares acceptance weights after a common completely
positive trace-nonincreasing finishing map, with arbitrary spectator memory. Both sides use
the same input operator and fixed classical challenge data; the finishing map may depend on
those data, preserving their correlation with the acceptance event.

The expected-mass lemmas assume a finite challenge family with explicit nonnegative weights and
a pointwise weighted incidence bound `δ` for the disagreement sets. They use the same positive
semidefinite input operator for every challenge. Under these hypotheses a width-`k` union has
expected weight at most `k * δ` times the input trace; the weights need not be normalized.
Merely bounding the number of reprogrammed points does not supply these independence and
incidence hypotheses.

`Oracle/ParallelHybrid.lean` lifts the comparison to adaptive programs, charging union-query
weights to a designated reference execution. The interpretation, program, initial state and
final observation are shared. `Comp/HybridBudget.lean` uses a total call cutoff across all ports
and a width cap, avoiding a sum of separate per-port maxima. The analytic cutoff and
square-root aggregation lemmas in `Foundations/Hybrid.lean` import only QuantumFoundations and
are staged for that dependency.

`Comp/ChargeWeight.lean` gives the pathwise natural-number port budget `IsQueryChargeBound`.
`totalWeight_le_of_isQueryChargeBound` bounds total query weight by the budget times the input
trace when each call's weight is bounded by its port charge times its input trace. Local steps
are free; zero-charge calls remain present, and a call with no possible answer still spends its
prefix charge. Unit charges recover total calls, and width charges recover `IsPointBound`.
`totalWeight_le_of_isPointBound` retains the actual adaptive sum of widths without per-port maxima.

`Oracle/ParallelSearch.lean` applies this hybrid to one uniformly hidden marked input in a finite
nonempty domain, using the additive `ZMod 2` oracle `markedFunction`.
`markedSearchAdvantage_le_of_isPointBound` bounds success by
`min 1 ((1 + 2 * sqrt (q * Q))^2 / N)`, where `N` is the domain cardinality, `q` bounds rounds
and `Q` bounds the sum of widths along every branch. It requires no maximum width.
`markedSearchAdvantage_le` is the width-cap corollary with `Q = k * q`, giving
`min 1 ((1 + 2 * q * sqrt k)^2 / N)`. The interpretation,
program, initial substate and guessing rule are fixed independently of the mark. Adaptive widths,
measurements, mixed or subnormalized states, duplicate inputs and width zero are allowed.
The bound includes zero-query guessing; loss and postselection remain missing mass without
renormalization.

These results implement the direct reprogramming, adaptive hybrid and round/point unique-mark
search part of M3a. Exact sums of square roots for deterministic width profiles remain open. The changing-property directional recurrence and its adaptive
mixed-state and total-budget transports (M−1), the general final-measurement lemma (M0), and CFHL
compressed-oracle bounds are separate obligations.

`Oracle/ParallelFinding.lean` packages the shared search argument. A fixed reference execution
and pointwise weighted incidence `δ` bound a weighted family of hidden-set finding experiments
by `δ * (1 + 2 * sqrt (q * Q))^2`. The weights need not normalize. The final event keeps the
same hidden set as its answering oracle; the reference state, program and guess are independent
of the sampled set. Both marked search and random-function preimage search instantiate this theorem.

`Oracle/ParallelPreimage.lean` completes M3b for a fixed target chosen independently of the uniform
function. `preimageSearchAdvantage_le_of_isPointBound` gives
`min 1 ((1 + 2 * sqrt (q * Q))^2 / |Y|)`; its width-cap corollary uses `Q = k * q`.
One function answers every round and the endpoint verifier. The target is neither obtained by
evaluating that function at a hidden input nor conditioned to lie in its image.
`ToMathlib/MeasureTheory/Measure/UniformTable/Target.lean` supplies the exact joint decomposition
into independent target labels and a reference table avoiding the target. Their incidence is
`1 / |Y|`; singleton responses are handled separately by the probability cap. Exact zero-point
laws retain successful mass divided by `|Y|`, permitting empty rounds and subnormalized inputs.
No compressed-oracle result is used by this argument.

### 13. Quantum delay experiments

`CryptoFoundations/TimeLockPuzzle/Quantum.lean` defines the two-phase quantum adversary and
honest puzzle interface. The generator returns the public puzzle, key and auxiliary secret;
the online adversary receives only the public puzzle and its own retained preprocessing state.
`delayInstrument` composes preprocessing, framed honest generation and online execution with
one persistent runtime-private register. `delayLawWith` initializes the joint state once and
observes the full transcript, retaining correlations with hidden challenger data. Lost mass
counts as failure. `DelayBudget` separates preprocessing rounds and points from online rounds,
points and maximum width; honest generation is outside the online clock. Retained memory is
unrestricted. These are query-bounded preprocessing resources, not auxiliary-input advice bounds.

`CryptoFoundations/TimeLockPuzzle/QuantumClassical.lean` embeds classical generators retaining
arbitrary hidden data. Its observed-law equality is an exact classical generator average of
quantum preprocessing followed by online execution for the same fixed function. Each online
branch receives its actual preprocessing post-state. The observer may inspect the preprocessing
branch, key and secret jointly with the leaf. The scalar-generation specialization uses the
trivial private register of a fixed-function runtime; the underlying instrument factorization
preserves private memory for general runtimes.

### 16. Auxiliary-input security remains separate

Auxiliary-input security allows an unbounded preprocessing computation on the oracle and
limits the advice retained for the online attack. It is a different model from query-bounded
preprocessing with unrestricted retained memory. See Chung–Guo–Liu–Qian,
[*Tight Quantum Time-Space Tradeoffs for Function Inversion*](https://arxiv.org/abs/2006.05650v2),
§3.1, Definition 3.1: the first algorithm is an arbitrary function of the oracle and outputs
an `S`-qubit advice state; the second algorithm has a query bound. Classical advice and quantum
advice require distinct statements.

An advice budget must count all retained
information, including the classical branch state, rather than only the quantum register's
dimension. Bit-fixing, presampling and their quantum variants are a separate proof track.
Guo–Li–Liu–Zhang,
[*Unifying Presampling via Concentration Bounds*](https://eprint.iacr.org/2020/1589), Definition 1,
specifies unbounded preprocessing with bounded classical advice; its discussion of barriers
to classical presampling against quantum queries is relevant when choosing that track's
intermediate model. Neither this model nor bounded quantum advice is currently implemented.

### 17. Exact pointer-chain encoding prerequisites

The exact pointer-chain puzzle has six oracle families with different state and link widths,
ordinary iterated hash chains, an accumulator,
and a published key commitment. Even with one chain and no public masked links, obtaining the
key requires the internal chain, accumulator and key hash. leanSeal §4.4 states that its
exact-encoding theorem is classical, and §8.3 item 4 leaves the quantum extension open in
that paper. A round-bounded quantum recovery theorem requires additional analysis.

The first encoding step retains the entire raw oracle table. An injective encoding of typed
inputs and a per-cell response split give a bijection between raw tables and typed-answer,
tail and outside-image tables (`Equiv.tableSplit`). Uniform table reparameterization preserves
the joint law of any raw quantum program, including observations of the hidden oracle.
The query signature stays unchanged, so coherent superpositions across labels and arbitrary
outside-image inputs remain available. This does not use the classical lazy-cache adapter
as a quantum simulation or discard the unused mask bytes.

The current homogeneous QROM model requires a finite input type. `ByteArray.Bounded`
contains every byte string up to a stated maximum length, including malformed and unlabelled
inputs. Honest leanSeal hash inputs have lengths `52` (steps), `54+b` (starts), `81` (masks),
`80` (accumulator and key), and `83` (commitments). A window of at least `max(54+b,83)` includes
them all; `86` suffices for valid link widths. An exact theorem in that window must retain
its explicit input-length scope. It is not a theorem for arbitrary-length byte queries.
The honest algorithms use structured public puzzles and agree with the source `gen` and
`solve` for every fixed byte-answer function restricted to the window. A serialized public
puzzle interface and a theorem for arbitrary serialized solver inputs remain separate.

`PointerChainPuzzle.PathValue.rankPrefix` supplies a separate prerequisite for the quantum delay
argument. Values beyond rank `r+1` have a predecessor beyond rank `r`; their inputs have
incidence at most `hitBound = [n≥2]/|L| + solvePoints(n,m)/|S|` when unreached labels are
resampled. Next-round inputs depend only on the preceding rank prefix.

### 18. Rank-ordered programming coupling

`PointerChainPuzzle.LeanSeal.programPath` programs a complete raw oracle using one independent
32-byte response for each path node. The typed path labels take the mask prefix and retain
the full state response at every other node. Their distribution is the uniform typed-label
distribution; all complementary raw bytes remain in the sampled path words.

`Equiv.tableLabelExchangeList` exchanges table cells with auxiliary labels. Its addresses
depend on predecessor labels, independently of the label being exchanged and of the table.
Reverse execution writes the supplied labels in reverse rank order. The generic inverse-table
identity requires a causal order and distinct nodes, but permits repeated oracle inputs.
It preserves the complete joint uniform law, including displaced values and current response
tails. The resulting programmed raw oracle has the uniform oracle marginal even on collisions.

Distinct path inputs let the honest generator recover the prescribed labels. The event being
charged is two different path nodes sharing an oracle input, rather than equal output labels.
For one chain with one step, equal labels are harmless because its query families are distinct;
with two steps, repeating an intermediate state can cause two queries to the same step cell.

`PointerChainPuzzle.LeanSeal.real_le_programmed_add_collision` proves the resulting game hop
for every observer `F(H, puzzle, key) ≤ 1`, retaining the completed oracle and hidden key jointly.
The collision allowance is `solvePoints(n,m)^2 / |Bytes 32|`, charged once after averaging the
salt, first link and masked links. The programmed experiment samples its path words
unconditionally. Conditioning those words on collision-freedom would invalidate the freshness
argument needed by the later quantum hybrid.

`qromDelayAdvantage_quantumWindowScheme_le_programmed` transfers this bound to the actual
quantum scheme experiment, with a separate `min 1` corollary. In its programmed game, both
preprocessing and online execution use the same completed programmed oracle; the actual
retained preprocessing register and classical state persist. No query budget or losslessness
assumption is needed for this comparison. Replacing preprocessing by a run against the base oracle requires a separate
query-dependent comparison; no such cost is hidden in the collision term.

The collision allowance is independent of the finite byte-window length. The adversary still
has the explicit window scope and structured public puzzles. Resource-bounded quantum analysis of the programmed game remains a separate obligation.
