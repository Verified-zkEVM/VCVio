# 6. Quantum queries and the quantum random-oracle model

This chapter connects the tutorial to cryptography. In the classical random-oracle model (ROM), a
hash function is modelled as a uniformly random function $H : X \to Y$ that the adversary can only
query. A quantum adversary runs on a quantum computer, so it can evaluate a public hash function on
a superposition of inputs. The **quantum random-oracle model** (QROM) gives it that power. This
chapter says what a quantum query is, shows that it really is more powerful, and explains why the
usual ROM proof techniques stop working.

## A query must be a gate

A classical query sends $x$ to $H(x)$. A quantum computer can only apply gates, which are
reversible (chapter 2), and $x \mapsto H(x)$ is usually not reversible: many inputs can have the
same hash. The fix is the CNOT pattern from chapter 3: keep $x$, and add $H(x)$ into a second
register:

$$U_H\,|x, y\rangle = |x,\; y + H(x)\rangle .$$

Here $Y$ is a finite group under $+$; for bitstrings, $+$ is XOR. $U_H$ only permutes basis states,
so it is a gate, and it can be undone by adding $-H(x)$ (for XOR, by applying $U_H$ again).

A classical query is the special case where the input is a basis state: start with $|x, 0\rangle$,
apply $U_H$ to get $|x, H(x)\rangle$, and measure, which reports $H(x)$ with certainty. So nothing
is lost: a quantum adversary can do everything a classical one can.

## Querying in superposition

The new possibility is to query on a superposition of inputs:

$$\sum_x \alpha_x\, |x, 0\rangle \;\xrightarrow{\;U_H\;}\; \sum_x \alpha_x\, |x, H(x)\rangle .$$

One query touches every input with nonzero amplitude. That does not mean one query reveals all of
$H$: measuring the result gives a single pair $(x, H(x))$. The advantage comes, as always, from
interference, as the next example shows.

## Deutsch's algorithm: one query instead of two

Take $X = Y = \{0, 1\}$ and ask: is $H(0) = H(1)$? Classically this needs two queries. Quantumly one
suffices.

Put the output register in the state $|-\rangle = \tfrac{1}{\sqrt2}(|0\rangle - |1\rangle)$. Adding
$H(x)$ to it either does nothing (if $H(x) = 0$) or swaps $|0\rangle$ and $|1\rangle$, which flips
the sign of $|-\rangle$. So

$$U_H\,|x\rangle|-\rangle = (-1)^{H(x)}\,|x\rangle|-\rangle :$$

the answer appears as a sign on the input register (this is called *phase kickback*). Now query on
$|+\rangle|-\rangle$:

$$U_H\,|+\rangle|-\rangle = \tfrac{1}{\sqrt2}\big((-1)^{H(0)}|0\rangle + (-1)^{H(1)}|1\rangle\big)
\otimes |-\rangle .$$

If $H(0) = H(1)$ the first qubit is $\pm|+\rangle$; otherwise it is $\pm|-\rangle$. Chapter 2
showed how to tell these apart with certainty: apply $H$ and measure. One query, and the answer
$H(0) + H(1)$ is certain.

## The QROM

In the QROM, $H : X \to Y$ is drawn uniformly at random **once**, before the experiment, and the
adversary may apply $U_H$ as often as it likes, on any states it likes, between its own gates and
measurements. Its success probability is averaged over $H$, exactly as in the ROM.

Two sanity checks hold, and VCVio proves both:

* A classical algorithm, run in the QROM through classical queries, succeeds with exactly the same
  probability as in the ROM.
* An algorithm that never queries cannot guess $H(x)$ for any $x$ better than with probability
  $1/|Y|$.

## Why the classical proof techniques break

ROM security proofs lean on three tricks. Each relies on the reduction seeing the adversary's
queries.

1. **Recording queries.** The reduction keeps a list of the inputs the adversary asked about, and
   samples $H(x)$ only when $x$ is first asked (lazy sampling). In the QROM a query has no single
   input: it is a superposition over all of them.
2. **Looking at the query** to extract information, such as the preimage the adversary must have
   asked about. Looking means measuring, and chapter 2 showed that measuring in the middle of a
   computation can destroy interference and change the adversary's behaviour.
3. **Programming** the oracle at a chosen point, which requires knowing the adversary has not
   already queried there.

QROM proofs replace these with new tools:

* **The hybrid argument** (Bennett, Bernstein, Brassard and Vazirani). If two oracles differ only on
  inputs to which the adversary's queries give little amplitude, the final states are close, and
  so are all output probabilities. Each query adds at most its own discrepancy.
* **The compressed oracle** (Zhandry). The random function is replaced by a quantum register that
  holds a superposition of *partial tables* (called databases), to which each query adds, updates
  or removes an entry. It behaves exactly like the random oracle, yet it records queries without
  disturbing them, which brings back a quantum version of trick 1.
* **Instability** (Chiesa, Manohar and Spooner). To bound how fast an adversary can make the
  database reach a property such as "contains a collision", it is enough to bound a *classical*
  quantity: the chance that adding one random entry to a small table changes whether it has the
  property. For collisions among $n$ possible values with fewer than $t$ entries, that chance is at
  most $(t-1)/n$. A classical bound on this quantity becomes a quantum bound with one extra factor
  of $t$.

## So far

* A quantum query is the gate $U_H|x, y\rangle = |x, y + H(x)\rangle$; classical queries are the
  basis-state case.
* Superposition queries plus interference beat classical queries (Deutsch).
* The QROM samples $H$ once; the adversary queries $U_H$ freely.
* Reading, recording and programming queries no longer work directly; QROM proofs use the hybrid
  argument, the compressed oracle and instability instead.

> **In VCVio.** A quantum adversary is a program, `QuantumComp`, that alternates its own steps with
> calls to an oracle; how calls are answered is a separate `QuantumRuntime`, just as a classical
> `OracleComp` is separate from the `QueryImpl` that answers its queries
> (`VCVio/Quantum/Comp/`). The oracle of a fixed $H$ is `additiveOracleRuntime H`, and the QROM
> distribution of a program is `qromEvalDist` (`VCVio/Quantum/Oracle/Model.lean`). The classical
> query is `classicalQuery`; a classical algorithm `oa` becomes `oa.toQuantum`, and
> `qromEvalDist₂_toQuantum_eq_randomOracle` is the first sanity check above. Deutsch's algorithm is
> `outcomeMeasure_deutsch` in `VCVioTest/Quantum/Oracle.lean`. The hybrid argument's core
> inequality is `norm_queryState_sub_queryState_le` (`QuantumFoundations/Pure/`), and instability is
> `QueryCache.instability`, with the collision bound `instability_cacheHasCollision_le`
> (`VCVio/OracleComp/QueryTracking/Instability/`). The compressed oracle itself is future work.
>
> Next: the [guide](../guide/README.md) explains these definitions in full, file by file.
