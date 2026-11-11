# 4. Programs and runtimes

Covers: Adaptive programs, runtimes and combs. See [conventions](../reference/conventions.md). Read
first: tutorial [chapter 5](../tutorial/5-what-a-quantum-computer-can-do.md),
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
* A runtime `R : QuantumRuntime spec` implements the ports. It has a private register `R.D` that
  persists across calls, so it can be stateful, and the program cannot touch it except through
  calls.
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

**They compute the right numbers.** The tests work small examples to exact values: one half of a
Bell state passed through an oracle call, with its coherences intact.
