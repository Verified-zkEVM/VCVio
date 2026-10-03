# Probability notation, computability, and migration

Status: implemented. This note describes the event notation `Pr{…}[…]`, which of its events can
be evaluated exactly, and the order in which code written against the removed discrete API
converts.

`Pr{do-items}[event]` is the single proof-facing notation for the probability of a successful
event in a monadic computation. Its braces hold an ordinary Lean `do` sequence. It elaborates to
nested core weakest preconditions `wp⟦…⟧` of the event's indicator, reading each draw in the
expectation interpretation `ExpectationWP` of its monad, so the probability of an event is the
expectation of its indicator. `prEvent_eq_evalDist_map` identifies `Pr{let x ← mx}[p x]` with
`𝒟[p <$> mx] {True}`, the mass that the `evalDist` measure of the mapped computation puts on
`True`. There is no second probability parser or Arklib-style notation family.

The notation is a semantic expression, not an evaluation algorithm. For a
measurable predicate `p`, `prEvent_eq_evalDist` identifies
`Pr{let x ← mx}[p x]` with `𝒟[mx] {x | p x}`. The discrete variant,
`prEvent_eq_evalDist_of_discrete`, needs no measurability proof. For `OptionT`, the semantics
discards `none` mass, so a failed branch contributes zero; a computation that explicitly returns
an `Option` can instead observe `none` as ordinary data.

## What can be computed

| Computation and event | Result | Needed evidence |
|---|---|---|
| `FinRatPMF.Raw` with finite rational branches | Exact rational mass via `Raw.prob` | `DecidableEq` on outputs; a decidable predicate can be compiled to a Boolean output |
| `OracleComp` with finite, enumerable oracle answers | Exact rational mass after `simulateQ finRatImpl` | `FinEnum` and inhabited answer types, plus an executable event |
| General `OracleComp` with chosen answer measures | Measure statement, not necessarily an algorithm | Answer measures (`[OracleSpec.AnswerMeasure spec]`); infinite sums need not reduce |
| Continuous `FreeM` queries | Measure statement and measurable-event proofs | Answer measures (`[PFunctor.AnswerMeasure P]`) and a measurable continuation or event; numerical integration is separate |
| Resumptions or possibly infinite interaction | Finite-fuel observations and limit theorems | No generic exact termination decision procedure |

`Raw.evalDist_apply_singleton_eq_prob` is the checkable boundary: the measure
of `{x}` equals the coercion of the executable `Raw.prob x`. The notation test
reads `Pr{let b ← mx}[b]` for a `Raw Bool` computation `mx` as `mx.prob true` through this
result, and checks that `Raw.coin` gives `true` the exact mass `1/2`.
Thus parsing can select the same expression in finite and continuous proofs,
while computation is requested explicitly through an executable representation.

The parser cannot infer decidability of an arbitrary proposition, turn an
arbitrary real-valued measure into a computable integral, or establish
measurability of a continuation. Making those claims implicitly would make
`Pr{...}[...]` look executable where it is not. A future elaborator can detect
a `Raw` computation and offer a diagnostic or a tactic that rewrites through
the bridge, but it should require the same decidability evidence and preserve
the measure meaning of the notation.

The expectation interpretation `ExpectationWP` is stated for monads `m : Type → Type v`, so every
draw in the braces returns a value in `Type`. This is sufficient for the repository's `OracleComp`
and `FreeM` examples. Higher-universe result monads would need a universe-polymorphic expectation
interpretation, not a parser trick.

## Migration order

Code written against the removed discrete API (`Pr[...]`, `𝒮[...]` and the classes that
interpreted them) converts with the codemod and the
[migration guide](../agents/probability-migration.md), in this order:

1. State theorems with `Pr{...}[...]`, `𝒟[...]`, or `Kernel`. Keep finite `Raw`
   calculations in executable code and bridge them to the measure statement.
2. Move client proofs onto the public measure equations. The one-time-pad UC observation
   theorem is a concrete example: its main equality is between measures.
3. Convert program-logic and coupling statements in coherent families.
4. Keep the result measure-valued. The environment linter `usesRetiredProbability` reports any
   declaration whose type or value uses Mathlib's `PMF` directly, and `scripts/nolints.json`
   holds no exception for it.

Oracle machines beyond well-founded `OracleComp` are a separate semantic
extension. The notation needs only an expectation interpretation, which every lawful monad with
lawful measure semantics has (`ExpectationWP.ofMeasure`), so it applies to such machines once a
sound returned-output measure is defined. Nothing here asserts that every machine terminates or
has an executable probability evaluator.
