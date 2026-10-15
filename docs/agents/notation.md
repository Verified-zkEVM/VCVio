# Notation Reference

The *Input* column gives the abbreviations of the `lean4` editor extension (type `\` and the
name). Beyond the tables: `ℝ≥0∞` is `\R\ge0\infty`, the dual carrier `ℝ≥0∞ᵒᵈ` adds `\^o\^d`,
core's entailment `⊑` is `\sqle`, its indexed infimum `⨅` is `\iInf`, and `←` is `\l`.

## OracleSpec Notations

| Notation | Meaning | Input | Defined in |
|----------|---------|-------|------------|
| `A →ₒ B` | Singleton oracle spec (`OracleSpec.ofFn`) | `\r`, `\_o` | `VCVio/OracleComp/OracleSpec.lean` |
| `[]ₒ` | Empty oracle spec (`emptySpec`) | `[]`, `\_o` | `VCVio/OracleComp/OracleSpec.lean` |
| `spec₁ + spec₂` | PFunctor coproduct (dependent `Sum.rec`) | `+`, `\_1` | `VCVio/OracleComp/OracleSpec.lean` |
| `⊂ₒ` | SubSpec relation | `\sub`, `\_o` | `VCVio/OracleComp/Coercions/SubSpec/Basic.lean` |
| `ˡ⊂ₒ` | Lawful (fiberwise bijective) SubSpec, `LawfulSubSpec` | `\^l`, `\sub`, `\_o` | `VCVio/OracleComp/Coercions/SubSpec/Basic.lean` |
| `∘ₛ` | QueryImpl composition | `\circ`, `\_s` | `VCVio/OracleComp/SimSemantics/QueryImpl/Compose.lean` |

## Probability Notations

| Notation | Meaning | Input | Defined in |
|----------|---------|-------|------------|
| `𝒟[mx]` | The successful-output `Measure` of `mx`, `evalDist mx` | `\McD` | `VCVio/EvalDist/Defs/Measure/Core.lean` |
| `Pr{let x ← mx; ...}[event]` | The probability of `event` after the draws. It is the expectation `𝔼{let x ← mx; ...}[𝟙⟦event⟧]` of the event's indicator, which elaborates to one nested expectation per draw, `wp⟦mx⟧ fun x => … wp⟦my⟧ (predInd fun y => event)` | `Pr{`, `\l` | `VCVio/EvalDist/ProbabilityNotation/Elab.lean` |
| `𝔼{let x ← mx; ...}[b]` | The expectation of `b : ℝ≥0∞` after the draws. It elaborates to nested core weakest preconditions, one per draw, each under the expectation interpretation of that draw's monad | `\bbE`, `\l` | `VCVio/EvalDist/ProbabilityNotation/Elab.lean` |
| `wp⟦mx⟧ g` | The expectation of `g : α → ℝ≥0∞` over the outputs of `mx`. It is core's `wp mx g ⊥` under the expectation interpretation `ExpectationWP` of `mx`'s monad, which integrates against the successful-output measure for a base monad and is core's lift of the base interpretation for `OptionT` and `ExceptT` | `wp\[[`, `\]]` | `VCVio/EvalDist/Expectation.lean` |

The braces take a `do`-style sequence, with pure `let`s, destructuring, nested `(← e)` actions,
branches, `match`, `let mut` and loops, but no `return` at their top level; see *Writing events
with `do` sequences* in `probability.md`. A single output is an event like any other,
`Pr{let x ← mx}[x = a]`. Failure is missing mass: the probability that `mx` fails is
`prFail mx = 1 - Pr{let _ ← mx}[True]`, and a lossless computation satisfies
`IsProbabilityMeasure 𝒟[mx]`. Every `OracleComp spec` computation is lossless under
`[OracleSpec.AnswerMeasure spec]` (`OracleComp.prEvent_true_eq_one`); failure arises in
`OptionT (OracleComp spec)` and similar transformers.

Use `Pr{...}[...]` for a probability after a Lean `do` sequence. It needs `EvalDistSemantics` for
the resulting computation and has the successful-output measure's semantics: failed or diverging
branches contribute zero. A Boolean event is coerced to a proposition. `prEvent_eq_evalDist_map`
identifies any event `Pr{let x ← mx}[p x]` with the mass `𝒟[p <$> mx] {True}`, with no
measurability assumption. For a measurable event, `prEvent_eq_evalDist` identifies it with
`𝒟[mx] {x | p x}`, and `prEvent_eq_evalDist_of_discrete` does so for any predicate on a discrete
output space. `prEvent_eq_evalDist_decide` connects an event to a Boolean experiment that returns
`decide` of the same predicate, without requiring a measurable structure on intermediate outputs.

State probabilities with `Pr{...}[...]` or apply `𝒟[...]` directly to a
measurable set; `prEvent_eq_evalDist_singleton` converts a point mass
`Pr{let x ← mx}[x = a]` to `𝒟[mx] {a}`. There is no `Pr_{...}[...]` syntax in VCVio.
See [probability notation and computability](../design/probability-notation-computability.md)
for the exact finite evaluator boundary and decidability requirements.

## Sampling Notations

| Notation | Meaning | Input | Defined in |
|----------|---------|-------|------------|
| `$ᵗ T` | `uniformSample T` (type-level uniform) | `$\^t` | `VCVio/OracleComp/Constructions/SampleableType/Basic.lean` |
| `$ xs` | `uniformSelect xs` (can fail on empty) | ASCII | `VCVio/OracleComp/ProbComp/Basic.lean` |
| `$! xs` | `uniformSelect! xs` (never fails) | ASCII | `VCVio/OracleComp/ProbComp/Basic.lean` |
| `$[0..n]` | `uniformFin n` (uniform `Fin (n+1)`) | ASCII | `VCVio/OracleComp/ProbComp/Basic.lean` |
| `$[n⋯m]` | `uniformRange n m` (uniform over range) | `\cdots` | `VCVio/OracleComp/ProbComp/Basic.lean` |

## Program Logic Notations

Open `OracleComp.ProgramLogic` for VCVio notation. Unary triples additionally require
`open scoped Std.WP`, and statements use the triple notation rather than `Std.WP.Triple c P Q E`
(see *Style Notes* in `CONTRIBUTING.md`); the necessary reading of an oracle computation is the
global instance.

| Notation | Meaning | Input | Defined in |
|----------|---------|-------|------------|
| `𝟙⟦P⟧` | Numeric proposition indicator (`propInd P`) | `\b1`, `\[[`, `\]]` | `VCVio/ProgramLogic/NotationCore.lean` |
| `rwp⟦c₁ ~ c₂ \| post; epost₁, epost₂⟧` | Relational WP (`VCVio.ProgramLogic.rwp c₁ c₂ post epost₁ epost₂`) | `rwp\[[`, `\]]`, `\_1` | `VCVio/ProgramLogic/NotationCore.lean` |
| `⦃ P ⦄ c ⦃ Q ⦄` | Core unary Hoare triple `Std.WP.Triple c P Q ⊥`, in whichever reading of `c` the scopes select. For `OracleComp`, the global necessary reading states that `Q` holds at every possible output of `c` when `P` holds; under `open scoped OracleComp.Lower` it states `P ≤ wp⟦c⟧ Q` | `\{{`, `\}}` | Lean core `Std.WP.Triple.Basic` |
| `⦃ P ⦄ c ⦃ Q; E ⦄` | Core unary Hoare triple with exception postcondition `E` (`Std.WP.Triple c P Q E`) | `\{{`, `\}}` | Lean core `Std.WP.Triple.Basic` |
| `⦃ toDual ε ⦄ c ⦃ Q ⦄` | Under `open scoped OracleComp.Upper`: the upper bound `wp⟦c⟧ (ofDual ∘ Q) ≤ ε`, with assertions in `ℝ≥0∞ᵒᵈ` ([gotcha 37][gotcha-37]) | `\{{`, `\e`, `\}}` | `VCVio/ProgramLogic/Unary/WP/Upper.lean` |
| `⦃ True ⦄ c ⦃ p ⦄` (possible) | Under `open scoped OracleComp.Possible`: some possible output of `c` satisfies `p` | `\{{`, `\}}` | `VCVio/ProgramLogic/Unary/WP/Possible.lean` |
| `mx =ᵈ my` | Equality in distribution (`EvalDistEq`): every event has the same probability, across monads | `=\^d` | `VCVio/EvalDist/EvalDistEq.lean` |
| `⟪c₁ ~ c₂ \| R⟫` | pRHL coupling (`RelTriple c₁ c₂ R`) | `\<<`, `\>>`, `\_1` | `VCVio/ProgramLogic/NotationCore.lean` |
| `⟪c₁ ≈[ε] c₂ \| R⟫` | Approximate coupling (`ApproxRelTriple ε c₁ c₂ R`) | `\<<`, `\~~`, `\e`, `\>>` | `VCVio/ProgramLogic/NotationCore.lean` |
| `⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` | Quantitative relational triple (`VCVio.ProgramLogic.RelTriple f c₁ c₂ g Lean.Order.bot Lean.Order.bot`) | `\{{`, `\~~`, `\_e`, `\}}` | `VCVio/ProgramLogic/NotationCore.lean` |

## UC Composition Notations

Scoped to `Interaction.UC` (activated by `open Interaction.UC`).
Defined in `PolyFun/Interaction/Open/Notation.lean`.

### Boundary-level

| Notation | Meaning | Input method |
|----------|---------|--------------|
| `Δ₁ ⊗ᵇ Δ₂` | `PortBoundary.tensor Δ₁ Δ₂` | `\otimes ^b` |
| `Δᵛ` | `PortBoundary.swap Δ` (dual/flip) | `\^v` |

### Expression-level (typeclass-backed)

Works for `Raw`, `Expr`, and `Interp` via `HasPar`/`HasWire`/`HasPlug` typeclasses.
Each type has `@[simp]` bridge lemmas (e.g., `Raw.hasPar`) that normalize
`HasPar.par e₁ e₂` back to `Raw.par e₁ e₂`, so existing simp lemmas
(`interpret_par`, etc.) fire transparently.

| Notation | Meaning | Prec | Input method |
|----------|---------|------|--------------|
| `e₁ ∥ e₂` | `HasPar.par e₁ e₂` (parallel) | 70r | `\parallel` |
| `e₁ ⊞ e₂` | `HasWire.wire e₁ e₂` (wire) | 65r | `\boxplus` |
| `e ⊠ k` | `HasPlug.plug e k` (plug/close) | 60r | `\boxtimes` |

Precedence ensures `A ∥ B ⊞ C ⊠ K` parses as `((A ∥ B) ⊞ C) ⊠ K`.

## Removed Notation

The notation of the removed discrete probability API, and its replacements, are tabulated in
[`probability-migration.md`](probability-migration.md), which also converts code written against
it.

[gotcha-37]: gotchas.md#37-an-upper-bound-triples-assertions-have-type-ℝ0ᵒᵈ
