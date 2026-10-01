/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Tactics.Unary
public import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# Probability goals

`prvcgen` states a bound or a probability-one statement about one program as a core triple and
runs `vcgen` on it; `prrw` rewrites an equality between the probabilities of two programs by bind
swaps and shared prefixes; `by_hoare` and `expect_arith` state and normalize events as expectations.
-/

@[expose] public section

open ENNReal OracleSpec OracleComp
open Lean.Order
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic Std.WP
open scoped OracleComp.Lower

universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable {α β γ : Type}

section ProbabilityLowering

variable [OracleSpec.AnswerMeasure spec]

/-! ### Probability one

Without uniform answers `Pr{…}[p] = 1` splits by antisymmetry: the upper half holds on the range
of the indicator, and the lower half is the triple `⦃ 1 ⦄ oa ⦃ 𝟙⟦p ·⟧ ⦄`. -/

example {oa : OracleComp spec α} {p : α → Prop} [DecidablePred p]
    (h : ⦃ 1 ⦄ oa ⦃ fun x => 𝟙⟦p x⟧ ⦄) :
    Pr{let x ← oa}[p x] = 1 := by
  prvcgen

example {oa : OracleComp spec α} {p : α → Prop} [DecidablePred p]
    (h : ⦃ 1 ⦄ oa ⦃ fun x => 𝟙⟦p x⟧ ⦄) :
    1 = Pr{let x ← oa}[p x] := by
  prvcgen

example {oa : OracleComp spec Bool}
    (h : ⦃ 1 ⦄ oa ⦃ fun y => if y = true then 1 else 0 ⦄) :
    Pr{let y ← oa}[y = true] = 1 := by
  prvcgen
  simp only [propInd_eq_ite, le_refl]

end ProbabilityLowering

section Equalities

variable [∀ t, Countable (spec.Range t)] [OracleSpec.AnswerMeasure spec]

/-! ### Equalities between two programs -/

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f : α → β → OracleComp spec γ} {z : γ} :
    Pr{let x ← mx >>= fun a => my >>= fun b => f a b}[x = z] =
    Pr{let x ← my >>= fun b => mx >>= fun a => f a b}[x = z] := by
  prrw

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {y : β}
    (h : ∀ x ∈ support mx, Pr{let z ← f x}[z = y] = Pr{let z ← g x}[z = y]) :
    Pr{let x ← mx >>= f}[x = y] = Pr{let x ← mx >>= g}[x = y] := by
  prrw congr
  exact h _ ‹_›

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr{let y ← f x}[q y] = Pr{let y ← g x}[q y]) :
    Pr{let y ← mx >>= f}[q y] = Pr{let y ← mx >>= g}[q y] := by
  prrw congr'
  exact h _

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr{let y ← f x}[q y] = Pr{let y ← g x}[q y]) :
    Pr{let y ← mx >>= f}[q y] = Pr{let y ← mx >>= g}[q y] := by
  prrw congr' as ⟨x⟩
  exact h x

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f g : α → β → OracleComp spec γ} {q : γ → Prop}
    (h : ∀ x y, Pr{let r ← f x y}[q r] = Pr{let r ← g x y}[q r]) :
    Pr{let r ← mx >>= fun x => my >>= fun y => f x y}[q r] =
    Pr{let r ← mx >>= fun x => my >>= fun y => g x y}[q r] := by
  prrw congr' as ⟨x, y⟩
  exact h x y

example : 𝟙⟦(True : Prop)⟧ * 𝟙⟦(True : Prop)⟧ = (1 : ℝ≥0∞) := by
  expect_arith

end Equalities

section ProbabilityLowering

variable [OracleSpec.AnswerMeasure spec]

/-! ### Probability lower bounds -/

example {oa : OracleComp spec α} {p : α → Prop} [DecidablePred p] {r : ℝ≥0∞}
    (h : ⦃ r ⦄ oa ⦃ fun x => 𝟙⟦p x⟧ ⦄) :
    r ≤ Pr{let x ← oa}[p x] := by
  prvcgen

example {oa : OracleComp spec α} [DecidableEq α] {x : α} {r : ℝ≥0∞}
    (h : ⦃ r ⦄ oa ⦃ fun y => if y = x then 1 else 0 ⦄) :
    Pr{let y ← oa}[y = x] ≥ r := by
  prvcgen
  simp only [propInd_eq_ite, le_refl]

/-- An event of a branching draw is the branch of the two events: the notation keeps the branch
as the draw's program, and `expect_norm` distributes the event over it. -/
example (c : Prop) [Decidable c] (oa ob : OracleComp spec α)
    (p : α → Prop) [DecidablePred p] :
    Pr{let x ← if c then oa else ob}[p x] =
      if c then wp⟦oa⟧ (fun x => 𝟙⟦p x⟧) else wp⟦ob⟧ (fun x => 𝟙⟦p x⟧) := by
  simp only [expect_norm]

example (c : Prop) [Decidable c] (oa : c → OracleComp spec α)
    (ob : ¬c → OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    Pr{let x ← if h : c then oa h else ob h}[p x] =
      if h : c then wp⟦oa h⟧ (fun x ↦ propInd (p x))
      else wp⟦ob h⟧ (fun x ↦ propInd (p x)) := by
  by_hoare

/-! ### `by_hoare` -/

example (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    Pr{let x ← oa}[p x] = wp⟦oa⟧ (fun x => if p x then 1 else 0) := by
  by_hoare

example (oa : OracleComp spec α) [DecidableEq α] (x : α) :
    Pr{let y ← oa}[y = x] = wp⟦oa⟧ (fun y => if y = x then 1 else 0) := by
  by_hoare

/-! ### Expectation equations

An equation between an expectation of one program and its unfolding is `expect_norm`. -/

example (c : Prop) [Decidable c] (oa ob : OracleComp spec α)
    (post : α → ℝ≥0∞) :
    wp⟦if c then oa else ob⟧ post =
      if c then wp⟦oa⟧ post else wp⟦ob⟧ post := by
  simp only [expect_norm]

end ProbabilityLowering
