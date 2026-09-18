/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.EvalDist
public import Batteries.Control.OptionT

/-!
# Discrete compatibility laws for uniform oracle sampling

Finite support and discrete output-probability equations for the uniform sampling operations.
-/

@[expose] public section


open OracleComp ENNReal

universe u v w

namespace ProbComp

section uniformFin

@[simp]
lemma finSupport_uniformFin (n : ℕ) :
    finSupport (do $[0..n]) = Finset.univ := by
  rw [finSupport_eq_iff_support_eq_coe, support_uniformFin]; simp

@[grind =]
lemma probOutput_uniformFin_eq_div (n : ℕ) (m : Fin (n + 1)) :
    Pr[= m | do $[0..n]] = 1 / (n + 1) := by simp [uniformFin_def]

@[simp, grind =]
lemma probOutput_uniformFin (n : ℕ) (m : Fin (n + 1)) :
    Pr[= m | do $[0..n]] = (n + 1 : ℝ≥0∞)⁻¹ := by simp [uniformFin_def]

@[simp, grind =]
lemma probEvent_uniformFin (n : ℕ) (p : Fin (n + 1) → Prop) [DecidablePred p] :
    Pr[ p | do $[0..n]] = (Fin.countP fun i => p i) / ↑(n + 1) := by
  simp [uniformFin_def, Fin.card_eq_countP_mem]

lemma probFailure_uniformFin (n : ℕ) :
    Pr[⊥ | do $[0..n]] = 0 := by aesop

end uniformFin

section uniformRange

@[simp, grind =]
lemma probOutput_uniformRange (n m : ℕ) (k : Fin (m + 1)) (h : n < m) :
    Pr[= k | uniformRange n m h] = if n ≤ k then (m - n + 1 : ℝ≥0∞)⁻¹ else 0 := by
  simp only [uniformRange, probOutput_map_eq_sum_finSupport_ite, finSupport_uniformFin, Fin.ext_iff,
    probOutput_uniformFin, natCast_sub, Finset.sum_boole', nsmul_eq_mul]
  rw [show ({x | (k : ℕ) = ↑x + n} : Finset (Fin (m - n + 1))).card =
      if n ≤ (k : ℕ) then 1 else 0 from ?_]
  · split <;> simp
  · by_cases hk : n ≤ (k : ℕ)
    · rw [ite_eq_left hk, Finset.card_eq_one]
      exact ⟨⟨k - n, by omega⟩, by ext i; simp [Fin.ext_iff]; omega⟩
    · rw [ite_eq_right hk, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x; simp; omega

@[simp]
lemma finSupport_uniformRange (n m : ℕ) (h : n < m) :
    finSupport (do uniformRange n m h) =
      Finset.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m) := by
  apply finSupport_eq_of_support_eq_coe
  simp [support_uniformRange n m h]

@[simp, grind =]
lemma probEvent_uniformRange (n m : ℕ)
    (p : Fin (m + 1) → Prop) [DecidablePred p] (h : n < m) :
    Pr[ p | uniformRange n m h] = Finset.card {x : Fin (m + 1) | n ≤ x ∧ p x} / (m - n + 1) := by
  rw [probEvent_eq_sum_filter_finSupport, finSupport_uniformRange]
  simp_rw [probOutput_uniformRange]
  rw [Finset.sum_ite_of_true fun x hx => by
        rw [Finset.mem_filter, Finset.mem_Icc, Fin.ofNat_Icc_iff h] at hx; lia,
    Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  congr 3 with x
  simp only [Finset.mem_filter, Finset.mem_Icc, Fin.ofNat_Icc_iff h,
    Finset.mem_univ, true_and]

lemma probFailure_uniformRange (n m : ℕ) (h : n < m) :
    Pr[⊥ | uniformRange n m h] = 0 := by aesop

end uniformRange

section uniformSelect

variable {cont : Type u} {β : Type}

end uniformSelect

section uniformSelectList

variable {α : Type} (xs : List α)

@[simp, grind =]
lemma finSupport_uniformSelectList [DecidableEq α] (xs : List α) :
    finSupport ($ xs) = xs.toFinset := match xs with
  | [] => by simp
  | x :: xs => by
      apply finSupport_eq_of_support_eq_coe
      simp [Set.ext_iff]

@[simp, grind =]
lemma probOutput_uniformSelectList [DecidableEq α] (xs : List α) (x : α) :
    Pr[= x | $ xs] = (xs.count x : ℝ≥0∞) / xs.length := match xs with
  | [] => by simp
  | y :: ys => by
    rw [List.count, ← List.countP_eq_sum_fin_ite]
    simp [uniformSelectList_cons, probOutput_map_eq_sum_fintype_ite, div_eq_mul_inv, @eq_comm _ x]

@[simp, grind =] lemma probFailure_uniformSelectList (xs : List α) :
    Pr[⊥ | $ xs] = if xs.isEmpty then 1 else 0 := match xs with
  | [] => by simp
  | y :: ys => by simp [uniformSelectList_cons]

@[simp, grind =] lemma probEvent_uniformSelectList
    (xs : List α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ xs] = (xs.countP p : ℝ≥0∞) / xs.length := match xs with
  | [] => by simp
  | y :: ys => by
    simp only [uniformSelectList_cons, Fin.getElem_fin, liftM_map, probEvent_map,
      OptionT.probEvent_liftM, probEvent_uniformFin, Function.comp_apply,
      Fin.countP_eq_countP_map_finRange, Nat.cast_add, Nat.cast_one, List.length_cons]
    congr 2
    exact List.countP_finRange_getElem (y :: ys) (fun b => decide (p b))

end uniformSelectList

section uniformSelectVector

variable {α : Type} {n : ℕ} (xs : Vector α (n + 1))

@[simp, grind =]
lemma finSupport_uniformSelectVector [DecidableEq α] :
    finSupport ($ xs) = xs.toList.toFinset := by
  rw [uniformSelect_eq_liftM_uniformSelect!, OptionT.finSupport_liftM]
  apply finSupport_eq_of_support_eq_coe
  simp [support_uniformSelectVector]

@[simp, grind =]
lemma probOutput_uniformSelectVector [DecidableEq α] (x : α) :
    Pr[= x | $! xs] = xs.count x / (n + 1) := by
  simp [uniformSelectVector_def, probOutput_map_eq_sum_finSupport_ite, div_eq_mul_inv,
    ← Vector.card_eq_count]

@[simp, grind =]
lemma probEvent_uniformSelectVector (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ xs] = xs.toList.countP p / (n + 1) := by
  simp [uniformSelect_eq_liftM_uniformSelect!, uniformSelectVector_def,
    probEvent_eq_sum_fintype_ite, div_eq_mul_inv, ← Vector.card_eq_countP]

end uniformSelectVector

section uniformSelectListVector

variable {α : Type} {n : ℕ} (xs : List.Vector α (n + 1))

@[simp, grind =]
lemma probOutput_uniformSelectListVector [DecidableEq α] (x : α) :
    Pr[= x | $! xs] = xs.toList.count x / (n + 1) := by
  simp [uniformSelectListVector_def, probOutput_map_eq_sum_finSupport_ite, div_eq_mul_inv,
    ← List.Vector.card_eq_count]

@[simp, grind =]
lemma probEvent_uniformSelectListVector (p : α → Prop) [DecidablePred p] :
    Pr[ p | $! xs] = xs.toList.countP p / (n + 1) := by
  simp [uniformSelectListVector_def, probEvent_eq_sum_fintype_ite, div_eq_mul_inv,
    ← List.Vector.card_eq_countP]

end uniformSelectListVector

section uniformSelectFinset

variable {α : Type} (s : Finset α)

@[simp, grind =]
lemma finSupport_uniformSelectFinset [DecidableEq α] :
    finSupport ($ s) = if s.Nonempty then s else ∅ := by
  aesop (add norm uniformSelectFinset_def)

@[simp, grind =]
lemma probOutput_uniformSelectFinset [DecidableEq α] (x : α) :
    Pr[= x | $ s] = if x ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  have hcount : s.toList.count x = if x ∈ s then 1 else 0 := by
    simpa using (Finset.nodup_toList s).count (a := x)
  aesop (add norm uniformSelectFinset_def)

@[simp, grind =]
lemma probEvent_uniformSelectFinset (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ s] = {x ∈ s | p x}.card / s.card := by
  simp only [uniformSelectFinset_def, probEvent_uniformSelectList, Finset.length_toList,
    ← Multiset.coe_countP, Finset.coe_toList, Multiset.countP_eq_card_filter, Finset.card_def,
    Finset.filter_val]

@[simp, grind =]
lemma probFailure_uniformSelectFinset :
    Pr[⊥ | $ s] = if s.Nonempty then 0 else 1 := by
  aesop (add norm uniformSelectFinset_def)

end uniformSelectFinset

section uniformSelectArray

variable {α : Type} (xs : Array α)

@[simp, grind =]
lemma finSupport_uniformSelectArray [DecidableEq α] :
    finSupport ($ xs) = xs.toList.toFinset := by
  simp [finSupport_eq_iff_support_eq_coe, support_uniformSelectArray]

@[simp, grind =]
lemma probFailure_uniformSelectArray : Pr[⊥ | $ xs] = if xs.size = 0 then 1 else 0 := by
  by_cases h : xs.size = 0
  · have hxs : xs = #[] := Array.size_eq_zero_iff.mp h
    subst hxs; simp
  · rw [uniformSelectArray_def, dite_eq_right h]
    simp [h]

-- TODO: `probOutput_uniformSelectArray` and `probEvent_uniformSelectArray` analogous to the
-- `List` API. These need a careful `Fin (xs.size - 1 + 1) ≃ Fin xs.size` reindexing that
-- the present helpers don't cleanly factor. Bridging through `xs.toList` once a clean
-- `($ xs : OptionT ProbComp α) = $ xs.toList` lemma lands is probably the right path.

end uniformSelectArray

section uniformSelectMultiset

variable {α : Type} (s : Multiset α)

@[simp, grind =]
lemma finSupport_uniformSelectMultiset [DecidableEq α] :
    finSupport ($ s) = s.toFinset := by
  apply finSupport_eq_of_support_eq_coe
  ext x
  simp [Multiset.mem_toFinset]

@[simp, grind =]
lemma probOutput_uniformSelectMultiset [DecidableEq α] (x : α) :
    Pr[= x | $ s] = (s.count x : ℝ≥0∞) / Multiset.card s := by
  simp [uniformSelectMultiset_def, ← Multiset.coe_count]

@[simp, grind =]
lemma probEvent_uniformSelectMultiset (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ s] = (Multiset.countP p s : ℝ≥0∞) / Multiset.card s := by
  simp [uniformSelectMultiset_def, ← Multiset.coe_countP]

@[simp, grind =]
lemma probFailure_uniformSelectMultiset :
    Pr[⊥ | $ s] = if 0 < Multiset.card s then 0 else 1 := by
  grind [uniformSelectMultiset_def, probFailure_uniformSelectList, Multiset.empty_toList,
    Multiset.card_eq_zero]

end uniformSelectMultiset

end ProbComp

section coinSpec
-- NOTE: This treats `coin` as essentially part of `ProbComp`, but it is more general.
-- In particular we can have a seperate theory of bounded uniform selection using only coins.

@[simp, grind =]
lemma finSupport_coin : finSupport coin = {true, false} := by aesop

@[simp, grind =]
lemma probOutput_coin (b : Bool) : Pr[= b | coin] = 2⁻¹ := by aesop

@[simp, grind =]
lemma probEvent_coin (p : Bool → Prop) [DecidablePred p] :
    Pr[ p | coin] = if p true then
      (if p false then 1 else 2⁻¹) else
      (if p false then 2⁻¹ else 0) := by
  rw [probEvent_eq_sum_fintype_ite, Fintype.sum_bool]
  split_ifs <;> simp_all [ENNReal.inv_two_add_inv_two]

@[grind =]
lemma probFailure_coin : Pr[⊥ | coin] = 0 :=
  NeverFail.probFailure_eq_zero

end coinSpec
