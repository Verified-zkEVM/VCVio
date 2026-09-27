/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Defs.NeverFails
public import VCVio.EvalDist.Monad.Map

/-!
# Evaluation Distributions on Boolean-Valued Computations

Specialization lemmas for `MonadLiftT m SPMF` computations returning `Bool`.
-/

@[expose] public section

variable {m : Type _ → Type _} [MonadLiftT m SPMF] {α β : Type _}

@[simp, grind =]
lemma probOutput_true_add_false (mx : m Bool) :
    Pr[= true | mx] + Pr[= false | mx] = 1 - Pr[⊥ | mx] := by
  simpa using tsum_probOutput_eq_sub mx

@[simp, grind =]
lemma probOutput_false_add_true (mx : m Bool) :
    Pr[= false | mx] + Pr[= true | mx] = 1 - Pr[⊥ | mx] := by
  rw [add_comm, probOutput_true_add_false]

@[simp]
lemma probOutput_not_map [Monad m] [LawfulMonad m] [LawfulMonadLiftT m SPMF] (mx : m Bool) :
    Pr[= true | (! ·) <$> mx] = Pr[= false | mx] :=
  probOutput_map_injective mx (fun a b h => by cases a <;> cases b <;> simp_all) false

@[simp]
lemma probOutput_not_map' [Monad m] [LawfulMonad m] [LawfulMonadLiftT m SPMF] (mx : m Bool) :
    Pr[= false | (! ·) <$> mx] = Pr[= true | mx] :=
  probOutput_map_injective mx (fun a b h => by cases a <;> cases b <;> simp_all) true

@[grind =]
lemma probOutput_true_add_false_of_neverFail [Monad m] {mx : m Bool} [NeverFail mx] :
    Pr[= true | mx] + Pr[= false | mx] = 1 := by simp

@[grind =]
lemma probEvent_true_eq_probOutput (mx : m Bool) :
    Pr[ (· = true) | mx] = Pr[= true | mx] := probEvent_eq_eq_probOutput mx true

@[grind =]
lemma probEvent_not_eq_probOutput (mx : m Bool) :
    Pr[ (· = false) | mx] = Pr[= false | mx] := probEvent_eq_eq_probOutput mx false
