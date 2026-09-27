/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.NeverFails
public import VCVio.EvalDist.Monad.Map

/-!
# Probability Distributions on `Option` return types

Lemmas about `evalSPMF` and the associated probabilities for computations
returning an `Option`.
-/

@[expose] public section

universe u v w

variable {m : Type u → Type v} {α β γ : Type u}

section map_some

variable [Monad m] [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

@[simp, grind =]
lemma probOutput_some_map_some (mx : m α) (x : α) :
    Pr[= some x | some <$> mx] = Pr[= x | mx] :=
  probOutput_map_injective mx (Option.some_injective α) x

@[simp, grind =]
lemma probOutput_some_map_none (mx : m α) :
    Pr[= none | some <$> mx] = 0 := by
  classical
  rw [probOutput_map_eq_tsum_ite]
  simp

end map_some

section double_option

variable [Monad m] [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  (mx : m (Option α))

@[simp]
lemma probOutput_some_map_option_map {f : α → β} (hf : f.Injective) (x : α) :
    Pr[= some (f x) | Option.map f <$> mx] = Pr[= some x | mx] := by
  refine probOutput_map_injective mx ?_ (some x)
  intro a b h
  cases a <;> cases b <;> simp_all [Option.map, hf.eq_iff]

@[simp]
lemma probOutput_none_map_option_map (f : α → β) :
    Pr[= none | Option.map f <$> mx] = Pr[= none | mx] := by
  classical
  rw [probOutput_map_eq_tsum_ite]
  refine (tsum_eq_single none fun x hx => ?_).trans (by simp)
  cases x with
  | none => exact absurd rfl hx
  | some => simp

end double_option
