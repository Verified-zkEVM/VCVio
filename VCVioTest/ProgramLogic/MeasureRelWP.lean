/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Relational.Measure.Bind
public import VCVio.ProgramLogic.Relational.Measure.Deterministic
public import Mathlib.Tactic.GRewrite

/-!
# Measure-native relational proof canaries

Coupling judgments and their quantitative postconditions are available without a discrete
probability backend. Pointwise postcondition bounds support generalized congruence and rewriting.
-/

public section

open MeasureTheory MeasureProgramLogic
open scoped ENNReal

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "native relational WP unexpectedly imports {name}"

universe u v w

namespace VCVioTest.ProgramLogic.MeasureRelWP

variable {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
  {m : Type u → Type w} {n : Type v → Type w}
  [EvalDistSemantics m] [EvalDistSemantics n]

example (mx : m α) (my : n β) (f g : α → β → ENNReal) (hfg : ∀ a b, f a b ≤ g a b) :
    eRelWP mx my f ≤ eRelWP mx my g := by
  gcongr with a b
  exact hfg a b

example (mx : m α) (my : n β) (f g : α → β → ENNReal) (hfg : ∀ a b, f a b ≤ g a b) :
    eRelWP mx my f ≤ eRelWP mx my g := by
  grw [hfg]

example {mx : m α} {my : n β} {R S : α → β → Prop}
    (h : RelWP mx my R) (hRS : ∀ a b, R a b → S a b) : RelWP mx my S :=
  relWP_mono h hRS

example (a : Nat) : RelWP (some a) (some a) (· = ·) := relWP_refl _

example (a b : Nat) (g : Nat → Nat → ENNReal) :
    eRelWP (pure a : Option Nat) (pure b : Option Nat) g = g a b := by simp

example (a b : Nat) (R : Nat → Nat → Prop) :
    RelWP (pure a : Option Nat) (pure b : Option Nat) R ↔ R a b := by simp

example (g : Nat → Nat → ENNReal) : eRelWP (some 0) (none : Option Nat) g = 0 :=
  eRelWP_eq_zero_of_mass_ne _ _ (by simp) g

example (R : Nat → Nat → Prop) : ¬RelWP (some 0) (none : Option Nat) R :=
  not_relWP_of_mass_ne _ _ (by simp) R

example (g : Nat → Nat → ENNReal) (h : ∀ a b, g a b ≤ 1) :
    eRelWP (some 0) (some 1) g ≤ 1 := eRelWP_le _ _ g 1 h

example [MeasurableSpace ℝ] [MeasurableSingletonClass ℝ]
    (j : ℝ × ℝ → Measure (Nat × Nat)) : AEMeasurable j (Measure.dirac (0, 0)) :=
  aemeasurable_of_ae_mem_countable (Set.countable_singleton ((0, 0) : ℝ × ℝ))
    (by simp) j

example {μ ν : Measure Nat} {R S : Nat → Nat → Prop}
    (hinit : CouplingPost μ ν R) {k l : Nat → Measure Nat}
    (hk : Measurable k) (hl : Measurable l)
    (hstep : ∀ a b, R a b → CouplingPost (k a) (l b) S) :
    CouplingPost (μ.bind k) (ν.bind l) S :=
  hinit.bind_of_countable (Set.to_countable Set.univ) (Set.to_countable Set.univ)
    (by simp) (by simp) hk hl MeasurableSet.of_discrete (by
      intro a _ b _ h
      exact hstep a b h)

end VCVioTest.ProgramLogic.MeasureRelWP
