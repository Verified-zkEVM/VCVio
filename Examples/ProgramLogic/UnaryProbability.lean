/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Tactics.Unary

/-!
# Unary Probability Goal Examples

This file validates probability lowering, probability equalities,
and `by_hoare` support in the unary tactic layer.
-/

@[expose] public section

open ENNReal OracleSpec OracleComp
open Lean.Order
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic Std.Internal.Do OracleComp.Quantitative

universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable {α β γ : Type}

section NativeLowering

variable [∀ t, MeasurableSpace (spec.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]

/-! ### Probability goal lowering -/

example {oa : OracleComp spec α} {p : α → Prop} [DecidablePred p]
    (h : ⦃ 1 ⦄ oa ⦃ fun x => 𝟙⟦p x⟧ ⦄) :
    Pr{let x ← oa}[p x] = 1 := by
  vcgen

example {oa : OracleComp spec α} {p : α → Prop} [DecidablePred p]
    (h : ⦃ 1 ⦄ oa ⦃ fun x => 𝟙⟦p x⟧ ⦄) :
    1 = Pr{let x ← oa}[p x] := by
  vcgen

example {oa : OracleComp spec Bool}
    (h : ⦃ 1 ⦄ oa ⦃ fun y => if y = true then 1 else 0 ⦄) :
    Pr{let y ← oa}[y = true] = 1 := by
  vcgen

end NativeLowering

section CompatibilityEqualities

variable [IsUniformSpec spec]

/-! ### Probability equality (swap / congr) -/

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f : α → β → OracleComp spec γ} {z : γ} :
    Pr[= z | mx >>= fun a => my >>= fun b => f a b] =
    Pr[= z | my >>= fun b => mx >>= fun a => f a b] := by
  vcstep

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {y : β}
    (h : ∀ x ∈ support mx, Pr[= y | f x] = Pr[= y | g x]) :
    Pr[= y | mx >>= f] = Pr[= y | mx >>= g] := by
  vcstep rw congr
  exact h _ ‹_›

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr[ q | f x] = Pr[ q | g x]) :
    Pr[ q | mx >>= f] = Pr[ q | mx >>= g] := by
  vcstep rw congr'
  exact h _

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr[ q | f x] = Pr[ q | g x]) :
    Pr[ q | mx >>= f] = Pr[ q | mx >>= g] := by
  vcstep rw congr' as ⟨x⟩
  exact h x

/--
info: Try this:

  [apply] vcstep rw congr as ⟨x, hx⟩
-/
#guard_msgs (info) in
example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr[ q | f x] = Pr[ q | g x]) :
    Pr[ q | mx >>= f] = Pr[ q | mx >>= g] := by
  vcstep?
  exact h x

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f g : α → β → OracleComp spec γ} {q : γ → Prop}
    (h : ∀ x y, Pr[ q | f x y] = Pr[ q | g x y]) :
    Pr[ q | mx >>= fun x => my >>= fun y => f x y] =
    Pr[ q | mx >>= fun x => my >>= fun y => g x y] := by
  vcstep rw congr' as ⟨x, y⟩
  exact h x y

example : 𝟙⟦(True : Prop)⟧ * 𝟙⟦(True : Prop)⟧ = (1 : ℝ≥0∞) := by
  exp_norm

end CompatibilityEqualities

section NativeLowering

variable [∀ t, MeasurableSpace (spec.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]

/-! ### Probability lower bounds -/

example {oa : OracleComp spec α} {p : α → Prop} [DecidablePred p] {r : ℝ≥0∞}
    (h : ⦃ r ⦄ oa ⦃ fun x => 𝟙⟦p x⟧ ⦄) :
    r ≤ Pr{let x ← oa}[p x] := by
  vcstep
  exact h

example {oa : OracleComp spec α} [DecidableEq α] {x : α} {r : ℝ≥0∞}
    (h : ⦃ r ⦄ oa ⦃ fun y => if y = x then 1 else 0 ⦄) :
    Pr{let y ← oa}[y = x] ≥ r := by
  vcstep
  simpa only [← propInd_eq_ite] using h

example (c : Prop) [Decidable c] (oa ob : OracleComp spec α)
    (p : α → Prop) [DecidablePred p] :
    Pr{let x ← if c then oa else ob}[p x] =
      if c then wp⟦oa⟧ (fun x => 𝟙⟦p x⟧) else wp⟦ob⟧ (fun x => 𝟙⟦p x⟧) := by
  vcstep

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

/--
info: Try this:

  [apply] vcstep
---
info: Planner note: continuing in raw `wp` mode
-/
#guard_msgs in
example (c : Prop) [Decidable c] (oa ob : OracleComp spec α)
    (post : α → ℝ≥0∞) :
    wp⟦if c then oa else ob⟧ post =
      if c then wp⟦oa⟧ post else wp⟦ob⟧ post := by
  vcstep?

/-! ### Support-cut synthesis -/

example (oa : OracleComp spec α) (f : α → OracleComp spec Bool)
    (h : ∀ x ∈ support oa, Pr{let y ← f x}[y = true] = 1) :
    ⦃ 1 ⦄ (do let x ← oa; f x) ⦃ fun y => if y = true then 1 else 0 ⦄ := by
  vcstep
  intro x
  by_cases hx : x ∈ support oa
  · simpa [propInd, hx] using triple_probOutput_eq_one (oa := f x) (x := true) (h := h x hx)
  · simpa [propInd, hx] using
      triple_zero (oa := f x) (post := fun y => if y = true then 1 else 0)

end NativeLowering
