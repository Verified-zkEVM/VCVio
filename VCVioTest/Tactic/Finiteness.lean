/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.ProgramLogic.Unary.HoareTriple
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import Mathlib.Tactic.Positivity.Finset
public import ToMathlib.Data.ENNReal.Finiteness

/-!
# `finiteness` on probability terms

Canaries for the `finiteness` rule-set tags on `prEvent_ne_top` and `prFail_ne_top`, for
Mathlib's finite-measure rule on `𝒟[mx] s`, and for the `Finset.sum` rule.
-/

public section

open scoped ENNReal

namespace VCVioTest.Finiteness

variable {α : Type} {m : Type → Type} [Monad m] [EvalDistSemantics m]

example (mx : m α) (x : α) : Pr{let y ← mx}[y = x] ≠ ⊤ := by finiteness

example (mx : m α) (p : α → Prop) : Pr{let y ← mx}[p y] * 2 ≠ ⊤ := by finiteness

example (mx : m α) (x : α) : prFail mx + Pr{let y ← mx}[y = x] / 2 ≠ ⊤ := by
  finiteness

example (mx : m α) (x : α) : Pr{let y ← mx}[y = x] < ⊤ := by finiteness

example [MeasurableSpace α] (mx : m α) (s : Set α) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    𝒟[mx] s * c ≠ ⊤ := by finiteness

example [Fintype α] (mx : m α) : ∑ x : α, Pr{let y ← mx}[y = x] ≠ ⊤ := by finiteness

/-- A quotient by a cardinality, the shape of the slack terms in the tag-reader bounds. The
nonzero side goal is `positivity`'s, and its `Fintype.card` extension lives in
`Mathlib.Tactic.Positivity.Finset`, which a file using this shape has to import. -/
example {D : Type} [Fintype D] [Nonempty D] (a : ℕ) :
    ((a : ℕ) : ℝ≥0∞) / (Fintype.card D : ℝ≥0∞) ≠ ⊤ := by finiteness

/-- A coin and a die, drawn independently. -/
def coinDie : ProbComp (Bool × Fin 6) := do
  let b ← $ᵗ Bool
  let d ← $ᵗ (Fin 6)
  pure (b, d)

example : Pr{let x ← coinDie}[x = (true, 0)] * 3 + prFail coinDie / 2 ≠ ⊤ := by finiteness

/-- Local abbreviations can be exposed explicitly without changing global unfolding. -/
example (mx : m α) (p : α → Prop) :
    let mass := Pr{let y ← mx}[p y]
    mass + 1 ≠ ⊤ := by
  dsimp only
  finiteness

section wp

open OracleComp.ProgramLogic

variable {ι : Type} {spec : OracleSpec ι} [OracleSpec.IsMeasureSpec spec] {β : Type}

/-- Not a `finiteness` rule, by design: an arbitrary functional need not have finite expectation,
so the bound is supplied by hand. -/
example (oa : OracleComp spec β) (g : β → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤) (h : ∀ x, g x ≤ c) :
    wp⟦oa⟧ g ≠ ⊤ :=
  ne_top_of_le_ne_top hc (wp_le_const_of_support oa fun x _ => h x)

example [Finite β] (oa : OracleComp spec β) (g : β → ℝ≥0∞) (hg : ∀ x, g x ≠ ⊤) :
    wp⟦oa⟧ g + 1 ≠ ⊤ := by finiteness

/-- A finite output type still requires finiteness of the functional. -/
example [Finite β] (oa : OracleComp spec β) (g : β → ℝ≥0∞) (hg : ∀ x, g x ≠ ⊤) :
    wp⟦oa⟧ g ≠ ⊤ := by
  fail_if_success solve | clear hg; finiteness
  finiteness

/-- Pointwise finiteness alone does not bound an infinite sum. -/
example (oa : OracleComp spec ℕ) (g : ℕ → ℝ≥0∞) (hg : ∀ x, g x ≠ ⊤) :
    (∀ x, g x ≠ ⊤) ∧ wp⟦oa⟧ g = wp⟦oa⟧ g := by
  fail_if_success have : wp⟦oa⟧ g ≠ ⊤ := by finiteness
  exact ⟨hg, rfl⟩

end wp

end VCVioTest.Finiteness
