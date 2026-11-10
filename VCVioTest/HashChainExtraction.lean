/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.CryptoFoundations.HashChain.Extraction

/-!
# Ordinary uses of addressed-chain extraction

The repeated-label example first merges at position one.
A different collision in its partial step table cannot serve as that fold's witness.
-/

public section

namespace ChainFirstMergeConsumer

universe u v

/-- An empty successful chain determines its input for arbitrary carrier and label types. -/
theorem empty_same {I : Type u} {D : Type v} (step : I → D → Option D)
    (honest : Nat → D) (candidate : D)
    (reaches : ([] : List I).foldlM (fun value label => step label value) candidate =
      some (honest 0)) : candidate = honest 0 := by
  have settled : ∀ (k : Nat) (hk : k < ([] : List I).length),
      step ([] : List I)[k] (honest k) = some (honest (k + 1)) := by
    intro k hk
    simp at hk
  rcases HashChain.foldlM_eq_some_same_or_first_merge step [] honest settled candidate reaches
    with same | ⟨k, hk, _⟩
  · exact same
  · simp at hk

/-- A small partial step table has a genuine merge and an unrelated collision. -/
@[expose] def partialStep (_ : Unit) : Nat → Option Nat
  | 0 => some 1
  | 1 => some 2
  | 7 => some 9
  | 9 => some 2
  | 3 => some 5
  | 4 => some 5
  | _ => none

/-- Repeated addresses preserve the actual first-merge position and its candidate prefix. -/
theorem repeated_labels_first_merge :
    ∃ (k : Nat) (_hk : k < 2), k = 1 ∧
      (([(), ()] : List Unit).take k).foldlM
        (fun value label => partialStep label value) 7 = some 9 ∧
      partialStep () 9 = some (k + 1) := by
  have settled : ∀ (k : Nat) (hk : k < ([(), ()] : List Unit).length),
      partialStep ([(), ()] : List Unit)[k] k = some (k + 1) := by
    intro k hk
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
        exact (Nat.not_lt_zero k
          (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hk))).elim
  have reaches : ([(), ()] : List Unit).foldlM
      (fun value label => partialStep label value) 7 = some (id 2) := rfl
  rcases HashChain.foldlM_eq_some_same_or_first_merge partialStep [(), ()] id settled 7 reaches
    with same | ⟨k, hk, value, prefixRun, _, merged, _, _⟩
  · simp at same
  · have firstIndex : k = 1 := by
      cases k with
      | zero =>
        have valueSeven : value = 7 := by simpa using prefixRun.symm
        subst value
        simp [partialStep] at merged
      | succ k =>
        cases k with
        | zero => rfl
        | succ k =>
          exact (Nat.not_lt_zero k
            (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hk))).elim
    subst k
    have valueNine : value = 9 := by
      simpa [partialStep, List.foldlM_cons] using prefixRun.symm
    subst value
    exact ⟨1, by decide, rfl, prefixRun, merged⟩

/-- A missing first step produces failure, never a purported shared successful endpoint. -/
theorem missing_step_fails :
    ([(), ()] : List Unit).foldlM (fun value label => partialStep label value) 10 = none := rfl

/-- A one-step candidate collision is extracted from its actual empty prefix. -/
theorem singleton_merge :
    ∃ value : Nat,
      ([] : List Unit).foldlM (fun value label => partialStep label value) 9 = some value ∧
      value ≠ 1 ∧ partialStep () value = some 2 := by
  have settled : ∀ (k : Nat) (hk : k < ([()] : List Unit).length),
      partialStep ([()] : List Unit)[k] (k + 1) = some (k + 1 + 1) := by
    intro k hk
    cases k with
    | zero => rfl
    | succ k => simp at hk
  rcases HashChain.foldlM_eq_some_same_or_first_merge partialStep [()] (fun k => k + 1)
      settled 9 (by rfl) with same | ⟨k, hk, value, prefixRun, different, merged, _, _⟩
  · simp at same
  · cases k with
    | zero => exact ⟨value, prefixRun, different, merged⟩
    | succ k => simp at hk

end ChainFirstMergeConsumer
