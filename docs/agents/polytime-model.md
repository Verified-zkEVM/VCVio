# The Turing-Machine-Grounded Polynomial-Time Adversary Model

This guide explains the machine-adversary polynomial-time layer: what the model is,
why each piece exists, which file owns what, and how the layer is positioned relative
to upstream cslib. Read it before touching anything under
`VCVio/OracleComp/Coinductive/PolyTime*.lean` or `ToMathlib/Computability/`.

## The Model In One Paragraph

`OracleComp.IsPolyTime bd oa` says: the program family
`oa : (n : ℕ) → α n → OracleComp (spec n) (β n)` is implemented, at pinned boundary
encodings `bd : BoundaryData spec α β`, by a family of oracle machines
(`MachineAdversary`) whose four step functions (initialization, query selection,
flattened update, readout) are each computed by concrete Cslib single-tape Turing
machines under **single polynomials, uniform across the family**, bounding running
time, round count, state-encoding length, and machine description size. This is
**non-uniform P/poly relative to a fixed canonical representation**: nothing computes
the `n`-th machine from `n`, and the description-size bound (`MachineAdversary.descBound`)
is the advice bound. A uniform variant (one machine reading `n`) is deliberately out of
scope rather than stubbed.

## Main Files

| File | Role |
|------|------|
| `ToMathlib/Computability/CslibPolyTime.lean` | `EncPolyTime`: encoded poly-time witness over cslib machines; adds the description-size measure (`PolyTimeComputable.size`, pinned to the `Bool` alphabet) that cslib lacks |
| `ToMathlib/Computability/PolyTimeTM.lean` | Base machines: `constComputer`, `tableComputer`; `EncPolyTime.const` / `.ofFintype` (finite tables) with size bounds |
| `ToMathlib/Computability/BitEncoding.lean` | `StrEncFam` (variable-width, injective, length-bounded), `BitEncFam` (fixed-width refinement), `EncPolyTimeFam` (uniform time + advice bounds across a family) |
| `ToMathlib/Computability/MachineCounting.lean` | `TMTable d`, the machine count `B d`, `RealizableLE`, the covering and diagonal lemmas — the counting core of non-triviality |
| `VCVio/OracleComp/Coinductive/PolyTime.lean` | `BoundaryData`, `MachineAdversary`, `PolyTimeWitness`, `OracleComp.IsPolyTime`, total-run-time accounting (`detTotalTime`) |
| `VCVio/OracleComp/Coinductive/PolyTimeClosure.lean` | Closure under input precomposition and output maps; `OracleMachine.setInit` |
| `VCVio/OracleComp/Coinductive/CoinFold.lean` | The bounded coin-fold combinator and its assembled witnesses |
| `VCVio/OracleComp/Coinductive/PolyTimeConstructions.lean` | `isPolyTime_coin`, `uniformBitVec`, `isPolyTime_pure_ofFintype` |
| `VCVio/OracleComp/Coinductive/PolyTimeNontrivial.lean` | The non-triviality certificates (see below) |
| `VCVio/CryptoFoundations/Asymptotics/PolyTime.lean` | `SecurityGame.secureAgainstPolyTime` / `secureAgainstMachines` |

The machine carrier itself (`DynComputation`, `unroll`, `ImplementsWithin`,
`ResolvesIn`, `runWith`) lives upstream in the PolyFun package
(`PolyFun/PFunctor/Dynamical/DynComputation/`), read through
`VCVio/OracleComp/Coinductive/Machine.lean`.

## Why Each Piece Exists

- **Pinned canonical boundaries (`BoundaryData`).** "Poly-time relative to *some*
  encoding" is vacuous: `enc x := std x ++ block (f x)` caches any `f` inside the
  representation and every machine degenerates to a projection. The input, output, and
  oracle-interface encodings are therefore explicit parameters of every security
  statement.
- **The description-size (advice) bound.** Time bounds alone admit lookup tables with
  one state per input — unbounded advice, and the class would contain every function
  on encodable domains. `EncPolyTimeFam.size` bounds each witness machine's state
  count by one polynomial across the family; over the fixed `Bool` alphabet the state
  count measures the transition table up to a constant factor, which is exactly what
  `MachineCounting.B` counts.
- **The `1^n` convention.** Boundary widths are polynomially bounded by definition
  (`BitEncFam.widBound`), so "polynomial in the input length" and "polynomial in `n`"
  agree — the width bound *is* the Katz–Lindell `1^n` convention.
- **Machine-internal freedom.** The state representation (`StrEncFam`) is existential
  in the bundle: every bit entering it was produced by a witnessed machine from
  canonical inputs and answers, so a crafted state encoding can only cache what was
  already computed within budget.

## Canonicity Is Discipline, Not Structure

`BitEncFam` is structurally only *injective + fixed polynomial width*. The caching
attack above is still expressible as a `BitEncFam`; nothing in the type requires the
encoding to be computable, let alone efficiently decodable. What closes the channel is
the **statement-site discipline**:

1. `bd : BoundaryData …` is always an explicit, pinned parameter of a security
   definition — **never existentially quantified and never adversary-chosen**. A
   theorem of the form `∃ bd, IsPolyTime bd oa` is meaningless; a hypothesis
   `∀ bd, …` is fine.
2. Boundaries are built from the small structural constructor registry
   (`BitEncFam.const/bool/fin/bitVec/bitVecX/pair/option/pad`, `StrEncFam.pairVar/sum`),
   so "secure against poly-time" reads "…relative to the standard representation".
3. The sole exemption is a multi-phase adversary's own cross-phase state, which its
   phases share (machine-internal data, covered by the freedom argument above).

A structural refinement (bundling a poly-time decoder into `BitEncFam`, making
canonicity a property rather than a convention) is recorded future work; it was not
needed for the non-triviality certificates because those pin concrete boundaries.

## What Is Proven, What Is Deferred

Proven (all sorry-free, axioms `propext`, `Classical.choice`, `Quot.sound` only):

- **Non-triviality**: `exists_not_isPolyTime_pure` — the class at the canonical
  coin/bitvector boundaries does not contain every predicate family, by counting
  (`B d`-many `d`-state machines vs `2^(2^n)` predicates) plus diagonalization. The
  round-free sentinel `exists_not_implements_pure_of_steps_eq_zero` isolates the
  counting core. Both were **false** before boundary canonicalization.
- **Hypothesis-free total time**: `MachineAdversary.exists_polynomial_detTotalTime_le`
  — every adversary's deterministic-run machine time (including the final readout at
  the budget state) is bounded by one polynomial in `n`, with no side conditions.
- **Query bound as a theorem**: `PolyTimeWitness.queryBound` derives
  `IsTotalQueryBound (oa n x) (steps.eval n)` from `implements` via
  `DynComputation.implementsWithin_iff_implements_and_bound` (`IsTotalQueryBound` is
  definitionally `PFunctor.FreeM.IsTotalRollBound`). Resolution and readout stability
  are likewise theorems, not bundle fields.
- **Closure** under input precomposition (finite-table and machine-witnessed) and
  output maps; the coin-fold combinator with fully-discharged table witnesses for
  polynomially-small accumulators.

Deferred, deliberately:

- **`bind` closure** (needs the two-phase machine construction; the statement is
  well-formed now that the mid boundary is shared by construction).
- **An end-to-end compiled single machine** for a whole run: `detTotalTime` is
  component-cost accounting over the four witnesses, not a constructed oracle TM
  (needs machine iteration on top of cslib's composition).
- **A uniform (single-machine) variant** of the class.
- **The `PolyQueries` bridge** (needs the per-`n` index-family generalization of
  `OracleComp.PolyQueries`).
- Hypothesis-free machine witnesses for superpolynomially-large-accumulator folds
  (e.g. `uniformBitVec`) — pending a base-machine combinator library
  (relabelings/projections on unbounded domains in `PolyTimeTM.lean`'s skeleton).

Nothing elsewhere in the repo currently depends on this layer: `secureAgainstPolyTime`
has no call sites by design until the deferred items land (the #460 review's staging).

## Semantics Notes (Read Before Changing Definitions)

- `ImplementsWithin` is **syntactic**: fuel-`k` unroll equality
  `M.run k x = FreeM.map some (oa x)` in the free monad — the machine makes literally
  the same queries in the same order along every typed answer path. Distributional
  agreement under every lawful handler (including stateful challengers at
  `StateT σ SPMF`) is a corollary (`MachineAdversary.exec_eq_of_implements`), not the
  definition. Complexity is intensional; this is the right strength.
- `ResolvesIn` and `IsTotalQueryBound` are worst-case, all-typed-answer-paths,
  handler-free.
- Machines are deterministic; all randomness enters through the oracle (the coin
  oracle is the random tape). There is no machine-internal sampling.
- `EncPolyTime`/`EncPolyTimeFam` impose nothing on their encoding arguments — their
  certifying power comes from call sites pinning `BitEncFam`/`StrEncFam`. Never accept
  an existentially-quantified encoding.
- `EncPolyTime(-Fam).comp` composes time bounds by substitution (degrees multiply):
  fixed-depth composition only. Polynomial-length runs are accounted additively per
  step (`detTotalTime`); only description size composes additively, which is what the
  non-triviality iterate (`EncPolyTime.exists_iterate`) uses.

## cslib Positioning And Upstream Watch

The layer builds on `Cslib.Turing.SingleTapeTM` (single tape, `Bool` alphabet,
`TimeComputable`/`PolyTimeComputable`), which arrives transitively through the PolyFun
package's cslib pin. Assessment as of 2026-07:

- cslib has **no complexity layer** and its whitepaper defers complexity theory to
  2027, naming RAM/query models and Boole cost semantics as the heavyweight targets.
  The de-facto RFC (cslib issue #611) treats single-tape TMs as the bottom rung of a
  simulation ladder; a multi-tape machine with time+space measures merged 2026-07
  (cslib PR #384) in a different namespace with different conventions. cslib is
  converging on model-independence via simulation relations, not one canonical
  machine.
- Everything upstream is **Prop-valued uniform complexity** (existentially quantified
  machines); none of it can express description-size/advice bounds. The non-uniform
  P/poly layer here has no upstream home and stays local — per the repo decision,
  nothing in `ToMathlib/Computability/` is aimed at upstream Mathlib/cslib PRs.
- **Stable under any upstream outcome**: the `List Bool` boundary encodings and the
  `timeBound : ℕ → ℕ` + `Polynomial ℕ` pair — every upstream proposal keeps both.
- **Model-welded, quarantined**: `PolyTimeComputable.size = Fintype.card State`
  (meaningful only at a fixed alphabet — hence pinned to `Bool` at the definition) and
  `MachineCounting.lean`'s hand-computed table count `B d`. A machine-model swap means
  re-deriving `MachineCounting.lean` and re-instantiating the `EncPolyTime.polyTime`
  field; `EncPolyTimeFam` is the interface the adversary layer consumes and is the
  natural swap point. Keep it that way: nothing outside `CslibPolyTime.lean` /
  `PolyTimeTM.lean` / `MachineCounting.lean` should reach into `tm.State`.
- **Name-collision watch**: cslib draft PR #192 (single-tape complexity classes)
  independently defines `PolyTimeComputable.normalize` and `readState` in the same
  namespace this repo extends. If a future cslib bump lands #192, drop the local
  `normalize` in favor of upstream and rename/reconcile `readState`
  (`PolyTimeTM.lean`).

## Statement-Site Checklist For New Security Definitions

1. Take `bd : BoundaryData spec α β` as an explicit parameter; build it from the
   canonical constructor registry at the final instantiation.
2. Use `SecurityGame.secureAgainstPolyTime bd g` (programs + `IsPolyTime`) or
   `SecurityGame.secureAgainstMachines g` (bundled `MachineAdversary`, `isPPT` slot
   trivially `True`).
3. Per-query-loss bounds compose via
   `secureAgainstPolyTime_of_advantage_le_mul_totalQueries`, consuming the derived
   `PolyTimeWitness.queryBound`.
4. To certify a concrete sampler poly-time, reach for the combinators first:
   `isPolyTime_coinFold` (poly-small accumulator), `isPolyTime_pure_ofFintype`
   (poly-small domain), the `IsPolyTime.precomp/.precompComp/.map` closures, and
   `IsPolyTime.congr` to bridge to the combinator's canonical program form.
