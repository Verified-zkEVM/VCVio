# Notation Reference

## OracleSpec Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `A →ₒ B` | Singleton oracle spec (`OracleSpec.ofFn`) | `VCVio/OracleComp/OracleSpec.lean` |
| `[]ₒ` | Empty oracle spec (`emptySpec`) | `VCVio/OracleComp/OracleSpec.lean` |
| `spec₁ + spec₂` | PFunctor coproduct (dependent `Sum.rec`) | `VCVio/OracleComp/OracleSpec.lean` |
| `⊂ₒ` | SubSpec relation | `VCVio/OracleComp/Coercions/SubSpec/Basic.lean` |
| `ˡ⊂ₒ` | Lawful (fiberwise bijective) SubSpec, `LawfulSubSpec` | `VCVio/OracleComp/Coercions/SubSpec/Basic.lean` |
| `∘ₛ` | QueryImpl composition | `VCVio/OracleComp/SimSemantics/QueryImpl/Compose.lean` |

## Probability Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `𝒟[mx]` | successful-output `Measure` denotation, `evalDist mx` | `VCVio/EvalDist/Defs/Measure/Core.lean` |
| `Pr{let x ← mx; ...}[event]` | `prEvent`: the `{True}` mass of the computation returning `event`; the braces hold an ordinary `do` sequence | `VCVio/EvalDist/ProbabilityNotation.lean` |

The braces take any `do` sequence, with pure `let`s, destructuring, nested `(← e)` actions,
branches, `match`, `let mut` and loops; see *Writing events with `do` sequences* in
`probability.md`. A single output is an event like any other, `Pr{let x ← mx}[x = a]`. Failure
is missing mass: the probability that `mx` fails is `prFail mx = 1 - Pr{let _ ← mx}[True]`, and a
lossless computation satisfies `IsProbabilityMeasure 𝒟[mx]`. Every `OracleComp spec`
computation is lossless under `[OracleSpec.IsMeasureSpec spec]`
(`OracleComp.prEvent_true_eq_one`); failure arises in `OptionT (OracleComp spec)` and similar
transformers.

Use `Pr{...}[...]` for a probability after a Lean `do` sequence. It needs
`EvalDistSemantics` for the resulting computation and has the successful-output
measure's semantics: failed or diverging branches contribute zero. A Boolean event
is coerced to a proposition. For a single measurable event,
`prEvent_eq_evalDist` identifies it with `𝒟[mx] {x | p x}`;
`prEvent_eq_evalDist_of_discrete` handles any predicate on a discrete
output space. `prEvent_eq_evalDist_decide` connects an event to a Boolean
experiment that returns `decide` of the same predicate without requiring a
measurable structure on intermediate outputs. The notation
does not require a finite-distribution lift.

State probabilities with `Pr{...}[...]` or apply `𝒟[...]` directly to a
measurable set; `prEvent_eq_evalDist_singleton` converts a point mass
`Pr{let x ← mx}[x = a]` to `𝒟[mx] {a}`. There is no `Pr_{...}[...]` syntax in VCVio.
See [probability notation and computability](../design/probability-notation-computability.md)
for the exact finite evaluator boundary and decidability requirements.

## Sampling Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `$ᵗ T` | `uniformSample T` (type-level uniform) | `VCVio/OracleComp/Constructions/SampleableType/Basic.lean` |
| `$ xs` | `uniformSelect xs` (can fail on empty) | `VCVio/OracleComp/ProbComp/Basic.lean` |
| `$! xs` | `uniformSelect! xs` (never fails) | `VCVio/OracleComp/ProbComp/Basic.lean` |
| `$[0..n]` | `uniformFin n` (uniform `Fin (n+1)`) | `VCVio/OracleComp/ProbComp/Basic.lean` |
| `$[n⋯m]` | `uniformRange n m` (uniform over range) | `VCVio/OracleComp/ProbComp/Basic.lean` |

## Program Logic Notations

Open `OracleComp.ProgramLogic` for VCVio notation. Unary triples additionally require
`open scoped Std.Internal.Do` and an interpretation, such as `OracleComp.Quantitative`.

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `𝟙⟦P⟧` | Numeric proposition indicator (`propInd P`) | `VCVio/ProgramLogic/NotationCore.lean` |
| `wp⟦c⟧` | Quantitative WP (`wp c`) | `VCVio/ProgramLogic/NotationCore.lean` |
| `rwp⟦c₁ ~ c₂ \| post; epost₁, epost₂⟧` | Relational WP (`VCVio.ProgramLogic.rwp c₁ c₂ post epost₁ epost₂`) | `VCVio/ProgramLogic/NotationCore.lean` |
| `⦃P⦄ c ⦃Q⦄` | Core unary Hoare triple (`Std.Internal.Do.Triple`) | Lean core `Std.Internal.Do.Triple.Basic` |
| `mx =ᵈ my` | Equality in distribution (`EvalDistEq`): every event has the same probability, across monads | `VCVio/EvalDist/EvalDistEq.lean` |
| `⟪c₁ ~ c₂ \| R⟫` | pRHL coupling (`RelTriple c₁ c₂ R`) | `VCVio/ProgramLogic/Notation.lean` |
| `⟪c₁ ≈[ε] c₂ \| R⟫` | Approximate coupling (`ApproxRelTriple ε c₁ c₂ R`) | `VCVio/ProgramLogic/Notation.lean` |
| `⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` | Quantitative relational triple (`VCVio.ProgramLogic.RelTriple f c₁ c₂ g Lean.Order.bot Lean.Order.bot`) | `VCVio/ProgramLogic/Notation.lean` |

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

## Removed Notation (Do NOT Use)

| Dead notation | Replacement |
|---------------|-------------|
| `Pr[= x \| comp]`, `[= x \| comp]` | `Pr{let y ← comp}[y = x]` |
| `Pr[p \| comp]`, `Pr[p x \| x ← comp]` | `Pr{let x ← comp}[p x]` |
| `Pr[⊥ \| comp]` | `prFail comp` |
| `𝒮[comp]` | `𝒟[comp]` |
| `++ₒ` | `+` |

To convert code written against the removed discrete probability API, see
[`probability-migration.md`](probability-migration.md).
