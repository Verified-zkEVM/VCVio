/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Support.Failure
public import VCVio.EvalDist.Defs.Measure.Deterministic
public import VCVio.EvalDist.Defs.Measure.OptionT
public import VCVio.EvalDist.Monad.Failure

/-!
# Native operational and measure failure canaries

Failure laws use attachment elimination for possible outputs and zero measure for probability.
Neither import surface contains a finite-distribution backend. State and reader bases need
no exact attachment assumption; measurable compositions need no operational attachment.
-/

public section

open MeasureTheory

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "native failure laws unexpectedly import {name}"

namespace VCVioTest.Failure

universe u v

section operational

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m]
  [LawfulMonadAttach m] {α σ ρ : Type u}

example : HasEvalSet.LawfulFailure (OptionT m) := inferInstance

example : support (failure : OptionT m α) = ∅ := by simp

example : support (failure : OptionT m α) = ∅ := by grind

example : HasEvalSet.LawfulFailure (OptionT (StateT σ m)) := inferInstance

example : support (failure : OptionT (StateT σ m) α) = ∅ := by simp

example : support (failure : OptionT (ReaderT ρ m) α) = ∅ := by grind

end operational

section measured

variable {m : Type u → Type v} [AlternativeMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
  {α β : Type u} [MeasurableSpace β]

example : 𝒟[(failure : m β)] = 0 := by simp

example : 𝒟[(failure : m β)] = 0 := by grind

example (f : α → m β) : 𝒟[(failure : m α) >>= f] = 0 := by simp

example (f : α → m β) : 𝒟[(failure : m α) >>= f] = 0 := by grind

example (mx : m α) : 𝒟[mx >>= fun _ ↦ (failure : m β)] = 0 := by simp

example (mx : m α) : 𝒟[mx >>= fun _ ↦ (failure : m β)] = 0 := by grind

end measured

section pure

variable {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
  [LawfulPureEvalDistSemantics m] {α : Type u} [MeasurableSpace α]

example : LawfulFailureEvalDistSemantics (OptionT m) := inferInstance

example : 𝒟[(failure : OptionT m α)] = 0 := by simp

end pure

section events

variable {m : Type → Type v} [AlternativeMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m] {α : Type}

example (p : α → Prop) : Pr{let x ← (failure : m α)}[p x] = 0 := by simp

example (p : α → Prop) : Pr{let x ← (failure : m α)}[p x] = 0 := by grind

end events

end VCVioTest.Failure
