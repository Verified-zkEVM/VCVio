/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.EvalDist.Monad.Map
public import Mathlib.Control.Lawful

/-!
# Support of `ExceptT` computations

`ExceptT ε m α` computations fail with an error of type `ε` or succeed with a value of type `α`;
the underlying type is `m (Except ε α)`. An `ExceptT` computation's support is the preimage of its
run's support under `Except.ok`, so errors are not outputs, and finite support lifts the same way.
Their output measures are in `VCVio.EvalDist.Defs.Measure.ExceptT`.
-/

@[expose] public section

universe u v

variable {ε : Type u} {m : Type u → Type v} [Monad m] {α β γ : Type u}

namespace ExceptT

section EvalSet

@[simp]
lemma run_liftM_eq_map_ok (mx : m α) :
    (liftM mx : ExceptT ε m α).run = Except.ok <$> mx := rfl

variable [MonadAttach m]

@[aesop unsafe norm, grind =]
lemma support_def (mx : ExceptT ε m α) :
    support mx = Except.ok ⁻¹' (support mx.run) := by
  ext x
  exact MonadAttach.ExceptT.canReturn_iff

lemma mem_support_iff (mx : ExceptT ε m α) (x : α) :
    x ∈ support mx ↔ Except.ok x ∈ support mx.run := Iff.rfl

variable [LawfulMonad m] [ExactMonadAttach m]

@[simp]
lemma support_liftM (mx : m α) :
    support (liftM mx : ExceptT ε m α) = support mx := by
  ext x
  simp

end EvalSet

section EvalFinset

noncomputable instance (ε : Type u) (m : Type u → Type v) [Monad m]
    [DecidableEq ε] [MonadAttach m] [HasEvalFinset m] :
    HasEvalFinset (ExceptT ε m) where
  finSupport mx := (finSupport mx.run).preimage Except.ok
    (by intro a b; simp [Except.ok.injEq])
  coe_finSupport mx := by ext x; simp

variable [DecidableEq ε] [MonadAttach m] [HasEvalFinset m]

@[aesop unsafe norm, grind =]
lemma finSupport_def [DecidableEq α] (mx : ExceptT ε m α) :
    finSupport mx = (finSupport mx.run).preimage Except.ok
      (fun a _ => by simp [Except.ok.injEq]) := rfl

@[simp low]
lemma mem_finSupport_iff' [DecidableEq α] (mx : ExceptT ε m α) (x : α) :
    x ∈ finSupport mx ↔ Except.ok x ∈ finSupport mx.run := by
  rw [finSupport_def]
  exact Finset.mem_preimage

@[simp]
lemma finSupport_liftM [LawfulMonad m] [ExactMonadAttach m] [DecidableEq α] (mx : m α) :
    finSupport (liftM mx : ExceptT ε m α) = finSupport mx := by
  ext x
  rw [mem_finSupport_iff', mem_finSupport_iff_mem_support, mem_finSupport_iff_mem_support]
  simp

end EvalFinset

end ExceptT
