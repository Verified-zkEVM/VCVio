/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import ToMathlib.Control.OptionT
public import VCVio.EvalDist.Defs.Support.Failure
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.EvalDist.Monad.Map

/-!
# Support of potentially failing computations

This file gives the support and finite support of `OptionT` computations in terms of the
underlying `m (Option α)`. Their support comes from PolyFun's `MonadAttach` instance; their output
measures are in `VCVio.EvalDist.Defs.Measure.OptionT`.
-/

@[expose] public section

universe u v w

variable {m : Type u → Type v} [Monad m] {α β γ : Type u}

namespace OptionT

section EvalSet

variable [MonadAttach m]

@[aesop unsafe norm, grind =]
lemma support_def (mx : OptionT m α) : support mx = some ⁻¹' (support mx.run) := by
  ext x
  exact MonadAttach.OptionT.canReturn_iff

lemma mem_support_iff (mx : OptionT m α) (x : α) :
    x ∈ support mx ↔ some x ∈ support mx.run := by grind

variable [LawfulMonad m] [ExactMonadAttach m]

@[simp]
lemma support_liftM (mx : m α) :
    support (liftM mx : OptionT m α) = support mx := by grind

@[simp]
lemma support_lift (mx : m α) :
    support (OptionT.lift mx) = support mx := by grind

/-- Peel the leading sample off the support of an `OptionT.mk`'d bind: any element of the
support of `OptionT.mk (sample >>= body)` factors through a sample `a` in the support of
`sample`, with the element in the support of `OptionT.mk (body a)`. -/
lemma mem_support_bind_mk (sample : m α) (body : α → m (Option β)) {x : β}
    (hx : x ∈ support (OptionT.mk (sample >>= body))) :
    ∃ a, a ∈ support sample ∧ x ∈ support (OptionT.mk (body a)) := by
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨a, ha, hx⟩ := hx
  exact ⟨a, ha, by simpa [OptionT.mem_support_iff] using hx⟩

end EvalSet

section HasEvalFinset

/-- Lift a `HasEvalFinset` instance to `OptionT`. by just taking preimage under `some`. -/
noncomputable instance (m : Type u → Type v) [Monad m] [MonadAttach m] [HasEvalFinset m] :
    HasEvalFinset (OptionT m) where
  finSupport mx := (finSupport mx.run).preimage some (by simp)
  coe_finSupport := by aesop

variable [MonadAttach m] [HasEvalFinset m]

@[aesop unsafe norm, grind =]
lemma finSupport_def [DecidableEq α] (mx : OptionT m α) :
    finSupport mx = (finSupport mx.run).preimage some (by simp) := rfl

@[simp low]
lemma mem_finSupport_iff [DecidableEq α] (mx : OptionT m α) (x : α) :
    x ∈ finSupport mx ↔ some x ∈ finSupport mx.run := by
  simp [finSupport_def, Finset.mem_preimage]

@[simp]
lemma finSupport_liftM [ExactMonadAttach m] [LawfulMonad m] [DecidableEq α] (mx : m α) :
    finSupport (liftM mx : OptionT m α) = finSupport mx := by
  ext x; simp [mem_finSupport_iff, mem_finSupport_iff_mem_support]

@[simp]
lemma finSupport_lift [ExactMonadAttach m] [LawfulMonad m] [DecidableEq α] (mx : m α) :
    finSupport (OptionT.lift mx) = finSupport mx := by
  ext x; simp [mem_finSupport_iff, mem_finSupport_iff_mem_support]

end HasEvalFinset

end OptionT
