# Probability notation, computability, and migration

`Pr{do-items}[event]` is the single proof-facing notation for the probability of
a successful event in a monadic computation. It elaborates an ordinary Lean `do`
block returning the event and applies that computation's `evalDist` measure to
`{True}`. This generalizes the existing syntax without introducing a second
probability parser or an Arklib-style notation family.

The notation is a semantic expression, not an evaluation algorithm. For a
measurable predicate `p`, `prEvent_eq_evalDist` identifies
`Pr{let x ← mx}[p x]` with `𝒟[mx] {x | p x}`. The discrete variant needs no
separate measurability proof. For `OptionT`, the semantics discards `none` mass,
so a failed branch contributes zero; a computation that explicitly returns an
`Option` can instead observe `none` as ordinary data.

## What can be computed

| Computation and event | Result | Needed evidence |
|---|---|---|
| `FinRatPMF.Raw` with finite rational branches | Exact rational mass via `Raw.prob` | `DecidableEq` on outputs; a decidable predicate can be compiled to a Boolean output |
| `OracleComp` with finite, enumerable oracle answers | Exact rational mass after `simulateQ finRatImpl` | `FinEnum` and inhabited answer types, plus an executable event |
| General discrete `OracleComp` with PMF-backed queries | Measure statement, not necessarily an algorithm | A probability specification; infinite sums need not reduce |
| Continuous `FreeM` queries | Measure statement and measurable-event proofs | A measure specification and measurable continuation or event; numerical integration is separate |
| Resumptions or possibly infinite interaction | Finite-fuel observations and limit theorems | No generic exact termination decision procedure |

`Raw.evalDist_apply_singleton_eq_prob` is the checkable boundary: the measure
of `{x}` equals the coercion of the executable `Raw.prob x`. The notation test
instantiates this result for `Raw.coin` and checks its exact `1/2` mass.
Thus parsing can select the same expression in finite and continuous proofs,
while computation is requested explicitly through an executable representation.

The parser cannot infer decidability of an arbitrary proposition, turn an
arbitrary real-valued measure into a computable integral, or establish
measurability of a continuation. Making those claims implicitly would make
`Pr{...}[...]` look executable where it is not. A future elaborator can detect
a `Raw` computation and offer a diagnostic or a tactic that rewrites through
the bridge, but it should require the same decidability evidence and preserve
the measure meaning of the notation.

The current event expression returns `Prop` or `Bool`, both in `Type 0`.
Accordingly, its monad and the binding theorem operate at that input universe;
this is sufficient for the repository's `OracleComp` and `FreeM` examples.
Higher-universe result monads would need a separate event representation or a
universe-polymorphic observation interface, not a parser trick.

## Migration order

1. State new theorems with `Pr{...}[...]`, `𝒟[...]`, or `Kernel`. Keep finite
   `Raw` calculations in executable code and bridge them to the measure statement.
2. Move client proofs from `Pr[...]` and `𝒮[...]` through the public measure
   equations. The one-time-pad UC observation theorem is a concrete example:
   its main equality is now between measures, with a finite `SPMF` corollary.
3. Replace legacy program-logic and coupling statements in coherent families.
   `SPMF`, `evalSPMF`, and the scalar `Pr[...]` functions are deprecated; the
   `usesRetiredProbability` environment linter tracks direct uses of those and
   Mathlib's imported `PMF` by declaration in `scripts/nolints.json`.
4. Once the remaining finite adapters have measure-level equivalents, remove
   the compatibility notation and declarations. The exception ledger should
   then become empty for this linter.

Oracle machines beyond well-founded `OracleComp` are a separate semantic
extension. The notation needs only an `EvalDistSemantics` instance and will
apply to such machines if a sound returned-output measure is defined; this
migration does not assert that every machine terminates or has an executable
probability evaluator.
