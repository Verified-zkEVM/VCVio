# Notation Reference

## OracleSpec Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `A →ₒ B` | Singleton oracle spec (`OracleSpec.ofFn`) | `VCVio/OracleComp/OracleSpec.lean` |
| `[]ₒ` | Empty oracle spec (`emptySpec`) | `VCVio/OracleComp/OracleSpec.lean` |
| `spec₁ + spec₂` | PFunctor coproduct (dependent `Sum.rec`) | `VCVio/OracleComp/OracleSpec.lean` |
| `⊂ₒ` | SubSpec relation | `VCVio/OracleComp/Coercions/SubSpec.lean` |
| `∘ₛ` | QueryImpl composition | `VCVio/OracleComp/SimSemantics/QueryImpl/Constructions.lean` |

## Probability Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `𝒟[mx]` | primary `Measure` denotation, `evalDist mx` | `VCVio/EvalDist/Defs/Measure.lean` |
| `Pr{let x ← mx; ...}[event]` | `prEvent`: successful-output measure of the `do` computation returning `event`, evaluated at `{True}` | `VCVio/EvalDist/ProbabilityNotation.lean` |
| `𝒮[mx]` | explicit finite adapter, `evalSPMF mx` | `VCVio/EvalDist/Defs/Basic.lean` |
| `Pr[= x \| mx]` | `probOutput mx x` | `VCVio/EvalDist/Defs/Basic.lean` |
| `Pr[p \| mx]` | `probEvent mx p` | `VCVio/EvalDist/Defs/Basic.lean` |
| `Pr[⊥ \| mx]` | `probFailure mx` | `VCVio/EvalDist/Defs/Basic.lean` |
| `Pr[cond \| var ← src]` | `probEvent src (fun var => cond)` | `VCVio/EvalDist/Defs/Basic.lean` |

Legacy code and comments may still use `[= x | comp]` (without `Pr`). New
proofs use `Pr{let x ← comp}[x = target]` or apply `𝒟[comp]` to an event.

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

`Pr[...]` remains the discrete compatibility notation. Use the named
`evalDist_apply_singleton`, `evalDist_apply_setOf`, and `evalDist_apply_univ`
equations at a compatibility boundary. New probability statements should use
`Pr{...}[...]` or apply `𝒟[...]` directly to a measurable set. There is no
`Pr_{...}[...]` syntax in VCVio.
See [probability notation and computability](../design/probability-notation-computability.md)
for the exact finite evaluator boundary and decidability requirements.

## Sampling Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `$ᵗ T` | `uniformSample T` (type-level uniform) | `VCVio/OracleComp/Constructions/SampleableType.lean` |
| `$ xs` | `uniformSelect xs` (can fail on empty) | `VCVio/OracleComp/ProbComp.lean` |
| `$! xs` | `uniformSelect! xs` (never fails) | `VCVio/OracleComp/ProbComp.lean` |
| `$[0..n]` | `uniformFin n` (uniform `Fin (n+1)`) | `VCVio/OracleComp/ProbComp.lean` |
| `$[n⋯m]` | `uniformRange n m` (uniform over range) | `VCVio/OracleComp/ProbComp.lean` |

## Program Logic Notations

Open `OracleComp.ProgramLogic` for VCVio notation. Unary triples additionally require
`open scoped Std.Internal.Do` and an interpretation, such as `OracleComp.Quantitative`.

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `𝟙⟦P⟧` | Numeric proposition indicator (`propInd P`) | `VCVio/ProgramLogic/NotationCore.lean` |
| `wp⟦c⟧` | Quantitative WP (`wp c`) | `VCVio/ProgramLogic/NotationCore.lean` |
| `rwp⟦c₁ ~ c₂ \| post; epost₁, epost₂⟧` | Relational WP (`VCVio.ProgramLogic.rwp c₁ c₂ post epost₁ epost₂`) | `VCVio/ProgramLogic/NotationCore.lean` |
| `⦃P⦄ c ⦃Q⦄` | Core unary Hoare triple (`Std.Internal.Do.Triple`) | Lean core `Std.Internal.Do.Triple.Basic` |
| `g₁ ≡ₚ g₂` | Game equivalence (`GameEquiv`) | `VCVio/ProgramLogic/NotationCore.lean` |
| `⟪c₁ ~ c₂ \| R⟫` | pRHL coupling (`RelTriple c₁ c₂ R`) | `VCVio/ProgramLogic/Notation.lean` |
| `⟪c₁ ≈[ε] c₂ \| R⟫` | Approximate coupling (`ApproxRelTriple ε c₁ c₂ R`) | `VCVio/ProgramLogic/Notation.lean` |
| `⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` | Quantitative relational triple (`VCVio.ProgramLogic.RelTriple f c₁ c₂ g Lean.Order.bot Lean.Order.bot`) | `VCVio/ProgramLogic/Notation.lean` |

## UC Composition Notations

Scoped to `Interaction.UC` (activated by `open Interaction.UC`).
Defined in `PolyFun/Interaction/UC/Notation.lean`.

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

## Legacy Notation (Do NOT Use)

| Dead notation | Replacement |
|---------------|-------------|
| `[= x \| comp]` | `Pr{let result ← comp}[result = x]` |
| `++ₒ` | `+` |
