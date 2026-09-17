/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Relational.Measure.Bind
public import VCVio.EvalDist.Defs.Measure.Deterministic
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

end VCVioTest.ProgramLogic.MeasureRelWP
