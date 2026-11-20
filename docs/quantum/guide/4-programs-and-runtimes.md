# 4. Programs and runtimes

Covers: Adaptive programs, runtimes, parallel query budgets and combs. See
[conventions](../reference/conventions.md). Read first: tutorial
[chapter 5](../tutorial/5-what-a-quantum-computer-can-do.md),
[chapter 6](../tutorial/6-quantum-queries.md); builds on [guide 1](1-states-and-instruments.md),
[guide 3](3-choi-kraus-stinespring.md).

## Programs and runtimes

[Deutsch's algorithm](5-qrom.md#deutschs-algorithm) is a fixed sequence of steps. General quantum
algorithms branch on measurement outcomes, change their registers, and may call several oracles. The
library's definition is a **program** run against a **runtime**:

* A program `QuantumComp L spec X A` is a tree. Each node applies a local operation named by a
  signature `L`, or calls a port of an oracle signature `spec` on part of its register. The
  classical outcome selects the subtree. A leaf returns data on its own final register.
* An interpretation `I : L.Interp` gives each local operation its dependent subinstrument.
* A runtime `R : QuantumRuntime spec` implements the ports. Its private register
  (`QuantumRuntime.D`) persists across calls, so it can be stateful, and the program cannot touch
  it except through calls.
* `R.run I x` is the execution: a dependent subinstrument on (program register) $\times$ (private
  register). `evalDist` is the distribution of the leaf reached; `jointPost` and `reducedPost` keep
  the final quantum state.

| Type | Use it when |
|---|---|
| `QuantumComp L spec X A` | different branches may end on different registers |
| `QuantumComp₂ L spec A B α` | every branch ends on `B` and returns a value in `α` |
| `QComp spec A B α` | local steps are arbitrary subinstruments (`QComp.act`) |

Examples in `VCVioTest/Quantum/Oracle.lean`: `callIfOne` measures a bit and calls the oracle only
on `1`; `queryWithAncilla` allocates a qubit, calls the oracle with it alongside, and discards it;
`countRuntime` is a runtime that counts its calls in its private register.

The port of a call is chosen classically. Programs are well-founded trees: every path is finite,
although with infinite branching path lengths need not have a common bound. Coherent choice of port
and loops that may not terminate are planned ([design page](../../design/quantum-layer.md)).

## Rounds, widths and points

A batch port `(p, k)` of `uBatchSpec P In` makes `k` ordered calls to the single base port `p`.
A round cannot mix base ports. To model several additive oracles queried in one round, encode
those oracles as one port on a sum input domain. The QROM uses one base port already.
For example, two rounds of widths two and three use five points. These are three separate
syntactic bounds:

| Bound on a batch program `x` | Meaning |
|---|---|
| `x.IsTotalQueryBound r` | at most `r` batch calls on every path |
| `x.IsWidthBound k` | every batch has width at most `k` |
| `x.IsPointBound n` | the sum of batch widths on every path is at most `n` |

Local operations spend no oracle budget. A width-zero batch spends one round and zero points.
The bounds cover every continuation, including outcomes of weight zero, and permit later widths
and register sizes to depend on earlier outcomes. `IsTotalQueryBound.isPointBound` combines a
round bound `r` and width cap `k` into the point bound `k * r`. A direct point bound may be
smaller: if two adaptive paths use widths `(2, 1)` and `(3, 2)`, their point budget is five,
while a width cap of three and two-round bound give six.

`Comp/RoundBound.lean` defines point budgets with PolyFun's `IFreeM.IsChargeBound` and width caps
with `IFreeM.IsRollBound`. `IsPointBound.bind` adds the budgets of consecutive programs;
`IsWidthBound.bind` keeps a cap shared by both.

## Sequentializing batches

`x.sequentialize I` translates a program over `uBatchSpec P In` into one over `uSpec P In`.
Each batch becomes single-point calls in increasing slot order. The source may use any local
signature `L`, interpreted by `I`; the target uses `LocalSig.instruments` to express those
operations and the public register relabellings needed between calls.
`sequentializeHandler I` is the named command substitution defining this translation.

For any base runtime `R`, `QuantumRuntime.run_sequentialize` states

```lean
R.run .instruments (x.sequentialize I) = R.batch.run I x
```

This is equality of the full dependent instruments on arbitrary joint inputs, including
correlations with the runtime's private register (`QuantumRuntime.D`). Calls retain that register
and their order across slots and rounds. `jointPost_sequentialize`, `evalDist_sequentialize` and
`evalDistMap_sequentialize` give the corresponding joint post-state and output-law equalities.
`Lossless.sequentialize` transports `x.Lossless I` to losslessness of the translated program.

`IsPointBound.sequentialize` turns a point bound `n` into the same total query bound `n`.
`IsTotalQueryBound.sequentialize` combines a round bound `r` and width cap `k` directly into
a sequential query bound `k * r`. Together with the law equality, these certificates let a
sequential theorem over `LocalSig.instruments` apply at the flattened point budget. A theorem
restricted to a particular gate signature or local-operation cost bound needs a separate
transport for those restrictions. The certificates count oracle queries; they do not account
for the local operations or relabellings introduced by the translation. A width-zero batch
emits no oracle queries, but may still relabel the public register into the caller's remainder
(`sequentialize_queryBind_zero`).

## Combs

The textbook quantum adversary alternates fixed unitaries with oracle calls:
$U_q\,O\,U_{q-1}\cdots O\,U_0$. `QuantumComb` is this form, with channels in place of unitaries.
`QuantumComb.toComp` turns a comb into a program, and `run_toComp` proves that the program runs as
the comb does against every runtime, so theorems about combs apply to programs of that shape. The
converse, putting a general program into comb form, is not proved, and needs hypotheses: for
instance, a comb makes the same number of calls on every path, while a program need not. The [design
page](../../design/quantum-layer.md) records the hypotheses a converse needs.

## Checks

**They agree with each other.** Wherever the library offers two descriptions of the same thing, a
theorem says they agree:

| Two descriptions | Agreement |
|---|---|
| combs and programs | `QuantumComb.run_toComp` |
| fixed-register and general programs | `QuantumRuntime.branch_run₂` |
| a batch program and its ordered single-point translation | `QuantumRuntime.run_sequentialize` |

**They compute the right numbers.** The tests work small examples to exact values: one half of a
Bell state passed through an oracle call, with its coherences intact.
`VCVioTest/Quantum/Sequentialize.lean` checks adaptive budgets and register changes, zero-weight
branches, zero-width relabellings, and ordered calls that exchange public slots with shared private
memory.
