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

## Open obligations

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

`OracleComp.toQuantum` embeds algorithms whose only oracle is the random function. Algorithms that
also sample their own coins (`OracleComp (unifSpec + (X →ₒ Y)) α`) need a classical sampling
command or a second runtime that samples, with the agreement theorem extended accordingly.

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
#864, #873–#875, #877). The general final-measurement lemma and collision and zero-preimage
bounds on the adversary's output are open (#966).
