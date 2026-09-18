/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Basic
public import VCVio.EvalDist.Defs.Support.Failure

/-!
# Discrete probability semantics of failure

The operational failure law and discrete support/probability compatibility identify failure
with zero successful-output probability and an absent result in the discrete distribution.
-/

@[expose] public section

open ENNReal HasEvalSet

universe u v w

variable {m : Type u → Type v} [AlternativeMonad m] {α β γ : Type u}

open HasEvalSet (LawfulFailure)

@[simp, grind =]
lemma probOutput_failure [MonadLiftT m SPMF]
    [MonadAttach m] [EvalDistCompatible m]
    [LawfulFailure m] (x : α) : Pr[= x | (failure : m α)] = 0 :=
  (probOutput_eq_zero_iff _ _).2 (by simp)

@[simp, grind =]
lemma probEvent_failure [MonadLiftT m SPMF]
    [MonadAttach m] [EvalDistCompatible m]
    [LawfulFailure m] (p : α → Prop) : Pr[ p | (failure : m α)] = 0 :=
  (probEvent_eq_zero_iff).2 (by simp)

@[simp, grind =]
lemma probFailure_failure [MonadLiftT m SPMF]
    [MonadAttach m] [EvalDistCompatible m]
    [LawfulFailure m] :
    Pr[⊥ | (failure : m α)] = 1 :=
  (probFailure_eq_one_iff _).2 (by simp)

@[simp, grind =]
lemma evalSPMF_failure [MonadLiftT m SPMF]
    [MonadAttach m] [EvalDistCompatible m]
    [LawfulFailure m] : 𝒮[(failure : m α)] = (failure : SPMF α) := by
  simp [SPMF.failure_eq_mk]
