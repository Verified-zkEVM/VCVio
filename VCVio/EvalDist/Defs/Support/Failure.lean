/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Support

/-!
# Operational failure

`HasEvalSet.LawfulFailure` states that failure has no possible outputs under `MonadAttach`.
The laws concern operational outputs independently of any probability interpretation.
-/

public section

universe u v

attribute [grind →] LawfulMonadAttach.eq_of_canReturn_pure

/-- Failure has no possible outputs under monadic attachment. -/
protected class HasEvalSet.LawfulFailure (m : Type u → Type v)
    [Alternative m] [MonadAttach m] : Prop where
  /-- Failure has empty attachment support. -/
  support_failure' {α : Type u} : support (failure : m α) = ∅

variable {m : Type u → Type v} [Alternative m] [MonadAttach m]
  [HasEvalSet.LawfulFailure m] {α : Type u}

/-- Failure has no possible outputs. -/
@[simp, grind =]
lemma support_failure : support (failure : m α) = ∅ :=
  HasEvalSet.LawfulFailure.support_failure'

/-- Failure has empty finite support. -/
@[simp, grind =]
lemma finSupport_failure [HasEvalFinset m] [DecidableEq α] :
    finSupport (failure : m α) = ∅ := by grind

/-- Optional failure has no possible outputs when attachment respects pure computations. -/
instance OptionT.instLawfulFailure (m : Type u → Type v) [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m] : HasEvalSet.LawfulFailure (OptionT m) where
  support_failure' := by grind
