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

variable [MonadLiftT m SPMF] (mx : m (Option α))

lemma probOutput_none_add_tsum_some :
    Pr[= none | mx] + ∑' x, Pr[= some x | mx] = 1 - Pr[⊥ | mx] := by
  rw [← tsum_probOutput_eq_sub mx, ← tsum_option _ ENNReal.summable]

/-- The probability of returning `some` is the total mass of all `some`
outputs, without requiring the computation to be failure-free. -/
lemma probEvent_isSome_eq_tsum_probOutput_some :
    Pr[fun r => r.isSome | mx] = ∑' x, Pr[= some x | mx] := by
  rw [probEvent_eq_tsum_ite]
  simpa only [Option.isSome, Bool.false_eq_true, eq_self, ite_false, ite_true, zero_add] using
    (tsum_option (fun r : Option α =>
      if r.isSome = true then Pr[= r | mx] else 0) ENNReal.summable)

/-- Selector fibers inside an optional output are disjoint, so their finite
sum is bounded by the probability of returning any `some` value. -/
lemma sum_probEvent_option_map_eq_some_le_isSome
    [Fintype γ] (select : α → Option γ) :
    ∑ k : γ, Pr[fun r => r.map select = some (some k) | mx] ≤
      Pr[fun r => r.isSome | mx] := by
  let : MeasurableSpace α := ⊤
  simpa only [evalDist_apply_setOf] using
    (MeasureTheory.Measure.sum_apply_option_map_eq_some_le_isSome 𝒟[mx] select
      fun _ ↦ MeasurableSet.of_discrete)

lemma probEvent_isSome_eq_one_sub_probOutput_none [Monad m] [NeverFail mx] :
    Pr[ fun r => r.isSome | mx] = 1 - Pr[= none | mx] := by
  rw [probEvent_eq_tsum_ite,
    tsum_option (fun r : Option α => if r.isSome then Pr[= r | mx] else 0) ENNReal.summable]
  simp only [Option.isSome, reduceCtorEq, ↓reduceIte, zero_add]
  have hnone_ne_top : Pr[= none | mx] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one
  have htotal : (∑' x, Pr[= some x | mx]) + Pr[= none | mx] = 1 := by
    simpa [probFailure_eq_zero (mx := mx), tsub_zero, add_comm]
      using probOutput_none_add_tsum_some (mx := mx)
  exact ENNReal.eq_sub_of_add_eq hnone_ne_top htotal

lemma sum_probOutput_some_le_one [Fintype α] :
    ∑ x : α, Pr[= (some x : Option α) | mx] ≤ 1 := by
  classical
  calc
    ∑ x : α, Pr[= (some x : Option α) | mx]
      ≤ ∑' y : Option α, Pr[= y | mx] := by
          rw [← tsum_fintype (L := .unconditional _),
            tsum_option (fun y : Option α => Pr[= y | mx]) ENNReal.summable]
          exact le_add_self
    _ ≤ 1 := tsum_probOutput_le_one

variable [Monad m] [LawfulMonad m] [LawfulMonadLiftT m SPMF]

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
