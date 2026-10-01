/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Unary.WP.Measure
public import VCVio.EvalDist.Defs.Measure.Deterministic
public import Mathlib.Tactic.GRewrite

/-!
# Expectation WP canaries

The quantitative carrier is chosen explicitly. Lawful measure semantics are sufficient for
expectation reasoning, including monads with unsuccessful runs. These examples check mass
factors, generalized congruence, directional rewriting, and core triples through ordinary imports.
-/

public section

open MeasureTheory Std.WP
open scoped ENNReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PMF then
    throwError "expectation WP unexpectedly imports PMF"

namespace VCVioTest.ProgramLogic.MeasureWP

example : True := by
  fail_if_success let _ := inferInstanceAs (WPMonad Option ENNReal EStack⟨⟩)
  trivial

open scoped ExpectationWP.Quantitative

example (c : ENNReal) : wp (none : Option Nat) (fun _ ↦ c) Lean.Order.bot = 0 := by simp

example (c : ENNReal) : wp (some 7 : Option Nat) (fun _ ↦ c) Lean.Order.bot = c := by simp

noncomputable example : WPMonad Option ENNReal EStack⟨⟩ := inferInstance

example : Triple (none : Option Nat) (0 : ENNReal) (fun _ : Nat ↦ (1 : ENNReal))
    (Lean.Order.bot : EStack⟨⟩) := by
  exact Triple.intro (by simp)

universe v

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  {α : Type} [MeasurableSpace α]

example (mx : m α) (f g : α → ENNReal) (hfg : ∀ x, f x ≤ g x) :
    wp mx f Lean.Order.bot ≤ wp mx g Lean.Order.bot := by
  gcongr with x
  exact hfg x

example (mx : m α) (f g : α → ENNReal) (hfg : ∀ x, f x ≤ g x) :
    wp mx f Lean.Order.bot ≤ wp mx g Lean.Order.bot := by
  grw [hfg]

example (mx : m α) (f g : α → ENNReal) (c : ENNReal) :
    wp mx (fun x ↦ c + f x + g x) Lean.Order.bot =
      c * 𝒟[mx] Set.univ + wp mx f Lean.Order.bot + wp mx g Lean.Order.bot := by
  rw [ExpectationWP.wp_add mx (fun x ↦ c + f x) g,
    ExpectationWP.wp_add mx (fun _ ↦ c) f, wp_const, prEvent_true_eq_evalDist_apply_univ]

example (mx : m α) (f g : α → ENNReal) (c : ENNReal)
    (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ᵐ x ∂𝒟[mx], f x ≤ c + g x) :
    wp mx f Lean.Order.bot ≤ c * 𝒟[mx] Set.univ + wp mx g Lean.Order.bot :=
  ExpectationWP.wp_le_const_mul_mass_add mx hf hg hfg

example (mx : m α) (f g : α → ENNReal) (c : ENNReal) [IsProbabilityMeasure 𝒟[mx]]
    (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ᵐ x ∂𝒟[mx], f x ≤ c + g x) :
    wp mx f Lean.Order.bot ≤ c + wp mx g Lean.Order.bot := by
  simpa using ExpectationWP.wp_le_const_mul_mass_add mx hf hg hfg

end VCVioTest.ProgramLogic.MeasureWP
