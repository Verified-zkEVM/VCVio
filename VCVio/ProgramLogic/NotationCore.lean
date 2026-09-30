/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Unary.HoareTriple
public import VCVio.EvalDist.MeasureTVDist.Basic
public import VCVio.ProgramLogic.Relational.Basic
public import VCVio.ProgramLogic.Relational.QuantitativeDefs
public import ToMathlib.Control.Monad.RelWP

/-!
# Ergonomic Notation and Convenience Layer for Program Logic

This file provides the lightweight user-facing notation and convenience predicates for
game-hopping proofs. It intentionally depends only on the core quantitative definitions,
not on the full eRHL theorem development.

The canonical proof mode lives in `VCVio/ProgramLogic/Tactics.lean`.

## Notation (activate with `open scoped OracleComp.ProgramLogic`)

### Prop indicator
- `𝟙⟦P⟧` — inject `Prop` into `ℝ≥0∞` (1 if true, 0 if false)

### Unary (core WP)

Unary triples additionally require `open scoped Std.WP`.
- `wp⟦c⟧ post` — expectation of `post` over the outputs of `c` (global, from
  `VCVio.EvalDist.Expectation`)
- `⦃ P ⦄ c ⦃ Q ⦄` — core's quantitative Hoare triple `Std.WP.Triple c P Q ⊥`
  (`P ≤ wp⟦c⟧ Q`)

### Game-level
- `g₁ =ᵈ g₂` — equality in distribution, from `VCVio.EvalDist.EvalDistEq`

### Relational (EasyCrypt-inspired)
- `⟪c₁ ~ c₂ | R⟫` — pRHL coupling triple
- `⟪c₁ ≈[ε] c₂ | R⟫` — approximate coupling triple
- `⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` — eRHL quantitative relational triple

## Convenience predicates

- `AdvBound game ε` — advantage of a game is at most `ε`
-/

@[expose] public section

open ENNReal OracleSpec OracleComp
open scoped Std.WP
open scoped OracleComp.Quantitative

universe u

namespace OracleComp.ProgramLogic

variable {ι₁ : Type u}
variable {spec₁ : OracleSpec.{u, 0} ι₁}
  [IsMeasureSpec spec₁]
variable {α β : Type}

/-! ## Convenience predicates -/

/-- Advantage of a Boolean game is at most `ε`, measured as the distance of its `true` mass from
one half. -/
def AdvBound (game : OracleComp spec₁ Bool) (ε : ℝ≥0∞) : Prop :=
  ENNReal.absDiff (𝒟[game] {true}) (1 / 2) ≤ ε

/-! ## Notation -/

/-- Numeric proposition indicator: `𝟙⟦P⟧ = 1` if `P` holds, `0` otherwise.
The true branch is the numeric value `1`, including for the unbounded expectation carrier. -/
scoped notation "𝟙⟦" P "⟧" => propInd P

/-- Raw relational WP notation.
`rwp⟦c₁ ~ c₂ | post; epost₁, epost₂⟧` elaborates to `VCVio.ProgramLogic.rwp`.
The normal assertion carrier and both exception-post carriers are inferred from
`post`, `epost₁`, and `epost₂`, so this notation also works for stateful and
exception-aware `RelWP` instances. -/
scoped syntax:max (name := relWpBracket)
  "rwp⟦" term:lead " ~ " term:lead " | " term ";" term ", " term "⟧" : term

scoped macro_rules (kind := relWpBracket)
  | `(rwp⟦ $c₁ ~ $c₂ | $post; $epost₁, $epost₂ ⟧) =>
      `(VCVio.ProgramLogic.rwp $c₁ $c₂ $post $epost₁ $epost₂)

/-- pRHL coupling: `⟪c₁ ~ c₂ | R⟫` means `RelTriple c₁ c₂ R`. -/
scoped notation "⟪" c₁ " ~ " c₂ " | " R "⟫" => Relational.RelTriple c₁ c₂ R

/-- Approximate coupling: `⟪c₁ ≈[ε] c₂ | R⟫` means `ApproxRelTriple ε c₁ c₂ R`. -/
scoped notation "⟪" c₁ " ≈[" ε "] " c₂ " | " R "⟫" =>
  Relational.ApproxRelTriple ε c₁ c₂ R

/-- eRHL quantitative relational triple:
`⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` means the quantitative `VCVio.ProgramLogic.RelTriple` form. -/
scoped syntax:lead "⦃" term "⦄ " term:lead " ≈ₑ " term:lead " ⦃" term "⦄" : term
macro_rules
  | `(⦃$f⦄ $c₁ ≈ₑ $c₂ ⦃$g⦄) =>
      `(VCVio.ProgramLogic.RelTriple $f $c₁ $c₂ $g Lean.Order.bot Lean.Order.bot)

/-! ## Bridge lemmas: numeric indicators and existing API -/

/-- `RelPost.indicator` is pointwise `𝟙⟦_⟧`. -/
lemma Relational.RelPost.indicator_eq_propInd {α β : Type}
    (R : Relational.RelPost α β) (a : α) (b : β) :
    Relational.RelPost.indicator R a b = 𝟙⟦R a b⟧ := rfl

/-- Almost-sure correctness: `⦃ 𝟙⟦True⟧ ⦄ c ⦃ fun x => 𝟙⟦p x⟧ ⦄` iff
`Pr{let x ← c}[p x] = 1`. -/
lemma triple_propInd_iff_prEvent_eq_one {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec] {α : Type}
    (oa : OracleComp spec α) (p : α → Prop) :
    ⦃ (𝟙⟦True⟧ : ℝ≥0∞) ⦄ oa ⦃ fun x => 𝟙⟦p x⟧ ⦄ ↔ Pr{let x ← oa}[p x] = 1 := by
  rw [Std.WP.Triple.iff, propInd_true]
  exact ⟨fun h ↦ le_antisymm (prEvent_le_one oa) h, fun h ↦ h.ge⟩

/-- Lower-bound event goals are exactly quantitative triples with indicator postconditions. -/
lemma triple_propInd_iff_le_prEvent {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec] {α : Type}
    (oa : OracleComp spec α) (p : α → Prop) (r : ℝ≥0∞) :
    ⦃ r ⦄ oa ⦃ fun x => 𝟙⟦p x⟧ ⦄ ↔ r ≤ Pr{let x ← oa}[p x] :=
  Std.WP.Triple.iff

/-! ## Expectation-level bridge lemmas -/

/-- WP of a disjunction indicator is bounded by the sum of individual WP indicators. -/
theorem wp_propInd_or_le {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec] {α : Type}
    (oa : OracleComp spec α) (p q : α → Prop) :
    wp⟦oa⟧ (fun x => 𝟙⟦p x ∨ q x⟧) ≤
        wp⟦oa⟧ (fun x => 𝟙⟦p x⟧) +
          wp⟦oa⟧ (fun x => 𝟙⟦q x⟧) := by
  rw [← MeasureProgramLogic.wp_add]
  apply wp_mono
  intro x
  by_cases hp : p x <;> by_cases hq : q x <;> simp [propInd, hp, hq]

/-- Markov inequality: if `a ≤ f x` whenever `p x`, then `a * Pr{let x ← oa}[p x] ≤ E[f | oa]`. -/
theorem markov_bound {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec] {α : Type}
    (oa : OracleComp spec α) (f : α → ℝ≥0∞) (a : ℝ≥0∞) (p : α → Prop)
    (hf : ∀ x, p x → a ≤ f x) :
    a * Pr{let x ← oa}[p x] ≤ wp⟦oa⟧ f := by
  rw [← MeasureProgramLogic.wp_const_mul]
  refine wp_mono oa fun x => ?_
  rw [predInd_apply]
  unfold propInd
  split_ifs with hp
  · simpa using hf x hp
  · simp

/-- A triple with precondition `1` and indicator postcondition when the event holds on the
support. -/
theorem triple_propInd_of_support {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec] {α : Type}
    (oa : OracleComp spec α) (p : α → Prop) (h : ∀ x ∈ support oa, p x) :
    ⦃ (1 : ℝ≥0∞) ⦄ oa ⦃ fun x => 𝟙⟦p x⟧ ⦄ := by
  refine ⟨?_⟩
  rw [← MeasureProgramLogic.wp_const_of_oracle oa 1]
  apply wp_mono_of_support
  intro x hx
  simp [propInd, h x hx]

/-! ## Bridge lemmas: advantage -/

/-- Advantage bound via total variation distance. -/
theorem AdvBound.of_measureETVDist {game₁ game₂ : OracleComp spec₁ Bool} {ε₁ ε₂ : ℝ≥0∞}
    (hbound : AdvBound game₁ ε₁) (htv : measureETVDist game₁ game₂ ≤ ε₂) :
    AdvBound game₂ (ε₁ + ε₂) := by
  unfold AdvBound at *
  calc ENNReal.absDiff (𝒟[game₂] {true}) (1 / 2)
      ≤ ENNReal.absDiff (𝒟[game₂] {true}) (𝒟[game₁] {true}) +
          ENNReal.absDiff (𝒟[game₁] {true}) (1 / 2) := ENNReal.absDiff_triangle _ _ _
    _ ≤ ε₂ + ε₁ := by
      refine add_le_add ?_ hbound
      rw [ENNReal.absDiff_comm]
      exact (measure_absDiff_apply_le_measureETVDist game₁ game₂
        (measurableSet_singleton true)).trans htv
    _ = ε₁ + ε₂ := add_comm _ _

/-- Transfer advantage bounds across games equal in distribution. -/
theorem AdvBound.of_evalDistEq
    {g₁ g₂ : OracleComp spec₁ Bool} {ε : ℝ≥0∞}
    (heq : g₁ =ᵈ g₂) (hbound : AdvBound g₁ ε) :
    AdvBound g₂ ε := by
  unfold AdvBound at *
  rwa [← heq.evalDist_eq]

end OracleComp.ProgramLogic
