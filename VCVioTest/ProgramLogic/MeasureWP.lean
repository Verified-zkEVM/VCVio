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
# Native expectation WP canaries

The quantitative carrier is chosen explicitly. Lawful measure semantics are sufficient for
expectation reasoning, including monads with unsuccessful runs. These examples check mass
factors, generalized congruence, directional rewriting, and core triples through ordinary imports.
-/

public section

open MeasureTheory Std.Internal.Do
open scoped ENNReal

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "native expectation WP unexpectedly imports {name}"

namespace VCVioTest.ProgramLogic.MeasureWP

example : True := by
  fail_if_success let _ := inferInstanceAs (WPMonad Option ENNReal EPost.Nil)
  trivial

open scoped MeasureProgramLogic.Quantitative

example (c : ENNReal) : MAlgOrdered.wp (none : Option Nat) (fun _ ↦ c) = 0 := by simp

example (c : ENNReal) : MAlgOrdered.wp (some 7 : Option Nat) (fun _ ↦ c) = c := by simp

noncomputable example : WPMonad Option ENNReal EPost.Nil := inferInstance

example : Triple (none : Option Nat) (0 : ENNReal) (fun _ : Nat ↦ (1 : ENNReal))
    (Lean.Order.bot : EPost.Nil) := by
  exact Triple.intro (by simp)

universe v

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]

example (mx : m α) (f g : α → ENNReal) (hfg : ∀ x, f x ≤ g x) :
    MAlgOrdered.wp mx f ≤ MAlgOrdered.wp mx g := by
  gcongr with x
  exact hfg x

example (mx : m α) (f g : α → ENNReal) (hfg : ∀ x, f x ≤ g x) :
    MAlgOrdered.wp mx f ≤ MAlgOrdered.wp mx g := by
  grw [hfg]

example (mx : m α) (f g : α → ENNReal) (c : ENNReal) :
    MAlgOrdered.wp mx (fun x ↦ c + f x + g x) =
      c * 𝒟[mx] Set.univ + MAlgOrdered.wp mx f + MAlgOrdered.wp mx g := by simp

example (mx : m α) (f g : α → ENNReal) (c : ENNReal)
    (hfg : ∀ᵐ x ∂𝒟[mx], f x ≤ c + g x) :
    MAlgOrdered.wp mx f ≤ c * 𝒟[mx] Set.univ + MAlgOrdered.wp mx g :=
  MeasureProgramLogic.Quantitative.wp_le_const_mul_mass_add mx hfg

example (mx : m α) (f g : α → ENNReal) (c : ENNReal) [IsProbabilityMeasure 𝒟[mx]]
    (hfg : ∀ᵐ x ∂𝒟[mx], f x ≤ c + g x) :
    MAlgOrdered.wp mx f ≤ c + MAlgOrdered.wp mx g := by
  simpa using MeasureProgramLogic.Quantitative.wp_le_const_mul_mass_add mx hfg

end VCVioTest.ProgramLogic.MeasureWP
