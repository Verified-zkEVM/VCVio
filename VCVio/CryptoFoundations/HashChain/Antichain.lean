/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.CryptoFoundations.HashChain.Extraction
public import Mathlib.Order.Antichain

/-!
# Structural extraction from antichain chain payloads

Accepted digit functions are incomparable in the pointwise order.
A payload reaching the honest terminals either matches the revealed payload, first merges
with an honest chain, or supplies an earlier canonical coordinate.
The earlier coordinate alone carries no claim of secrecy or unpredictability.
-/

public section

namespace HashChain

universe u v

variable {n : Nat} {I : Type u} {D : Type v}

/-- A first merge on one actual candidate suffix, including every earlier unequal prefix.

The relation is exposed so ordinary consumers can inspect its full same-address witness.
-/
@[expose] def FirstMerge (height : Fin n → Nat) (address : Fin n → Nat → I)
    (step : I → D → Option D) (honest : Fin n → Nat → D)
    (digits : Fin n → Nat) (values : Fin n → D) : Prop :=
  ∃ i, let labels := (List.range' (digits i) (height i - digits i)).map (address i)
    ∃ (k : Nat) (_hk : k < labels.length) (value : D),
      (labels.take k).foldlM (fun value label => step label value) (values i) = some value ∧
      value ≠ honest i (digits i + k) ∧
      step (address i (digits i + k)) value = some (honest i (digits i + k + 1)) ∧
      step (address i (digits i + k)) (honest i (digits i + k)) =
        some (honest i (digits i + k + 1)) ∧
      ∀ j, j ≤ k → ∃ earlierValue : D,
        (labels.take j).foldlM (fun value label => step label value) (values i) =
          some earlierValue ∧ earlierValue ≠ honest i (digits i + j)

-- Shift the existing chain theorem to the candidate digit, retaining its literal suffix fold.
private theorem same_or_merge_at (height : Fin n → Nat) (address : Fin n → Nat → I)
    (step : I → D → Option D) (honest : Fin n → Nat → D)
    (settled : ∀ i k, k < height i →
      step (address i k) (honest i k) = some (honest i (k + 1)))
    (digits : Fin n → Nat) (values : Fin n → D) (i : Fin n)
    (bound : digits i ≤ height i)
    (reaches : ((List.range' (digits i) (height i - digits i)).map (address i)).foldlM
      (fun value label => step label value) (values i) = some (honest i (height i))) :
    values i = honest i (digits i) ∨ FirstMerge height address step honest digits values := by
  let labels := (List.range' (digits i) (height i - digits i)).map (address i)
  have shifted : ∀ (k : Nat) (hk : k < labels.length),
      step labels[k] (honest i (digits i + k)) =
        some (honest i (digits i + (k + 1))) := by
    intro k hk
    have smaller : k < height i - digits i := by
      simpa only [labels, List.length_map, List.length_range'] using hk
    simpa only [labels, List.getElem_map, List.getElem_range', Nat.one_mul,
      Nat.add_assoc] using settled i (digits i + k) (Nat.add_lt_of_lt_sub' smaller)
  have terminal : labels.foldlM (fun value label => step label value) (values i) =
      some (honest i (digits i + labels.length)) := by
    simpa only [labels, List.length_map, List.length_range', Nat.add_sub_of_le bound]
      using reaches
  rcases foldlM_eq_some_same_or_first_merge step labels
    (fun k => honest i (digits i + k)) shifted (values i) terminal with same |
      ⟨k, hk, value, prefixRun, different, merged, honestStep, prior⟩
  · exact Or.inl (by simpa using same)
  · refine Or.inr ⟨i, k, hk, value, prefixRun, different, ?_, ?_, prior⟩
    · simpa only [labels, List.getElem_map, List.getElem_range', Nat.one_mul,
        Nat.add_assoc] using merged
    · simpa only [labels, List.getElem_map, List.getElem_range', Nat.one_mul,
        Nat.add_assoc] using honestStep

/-- A successful antichain payload is exact, first-merging, or canonical at a decreased digit.

Equality here covers the abstract digit and chain-value functions, not a message or nonce.
-/
theorem same_payload_or_first_merge_or_earlier
    (height : Fin n → Nat) (address : Fin n → Nat → I) (step : I → D → Option D)
    (honest : Fin n → Nat → D)
    (settled : ∀ i k, k < height i →
      step (address i k) (honest i k) = some (honest i (k + 1)))
    (accepted : Set (Fin n → Nat))
    (bounded : ∀ digits ∈ accepted, ∀ i, digits i ≤ height i)
    (antichain : IsAntichain (· ≤ ·) accepted)
    (signed digits : Fin n → Nat) (signedAccepted : signed ∈ accepted)
    (candidateAccepted : digits ∈ accepted) (values : Fin n → D)
    (reaches : ∀ i,
      ((List.range' (digits i) (height i - digits i)).map (address i)).foldlM
        (fun value label => step label value) (values i) = some (honest i (height i))) :
    (digits = signed ∧ values = fun i => honest i (signed i)) ∨
      FirstMerge height address step honest digits values ∨
      ∃ i, digits i < signed i ∧ values i = honest i (digits i) := by
  classical
  by_cases sameDigits : digits = signed
  · by_cases sameValues : values = fun i => honest i (signed i)
    · exact Or.inl ⟨sameDigits, sameValues⟩
    · have changed : ¬ ∀ i, values i = honest i (signed i) := fun h => sameValues (funext h)
      obtain ⟨i, different⟩ := Classical.not_forall.mp changed
      rcases same_or_merge_at height address step honest settled digits values i
        (bounded digits candidateAccepted i) (reaches i) with canonical | merge
      · exact (different (by simpa only [sameDigits] using canonical)).elim
      · exact Or.inr (Or.inl merge)
  · have notDominated : ¬ ∀ i, signed i ≤ digits i := fun h =>
      sameDigits (antichain.eq signedAccepted candidateAccepted h).symm
    obtain ⟨i, notLe⟩ := Classical.not_forall.mp notDominated
    have earlier : digits i < signed i := Nat.lt_of_not_ge notLe
    rcases same_or_merge_at height address step honest settled digits values i
      (bounded digits candidateAccepted i) (reaches i) with canonical | merge
    · exact Or.inr (Or.inr ⟨i, earlier, canonical⟩)
    · exact Or.inr (Or.inl merge)

/-- Without a prior payload, an explicit interior digit yields a merge or a preterminal value.

Antichain acceptedness alone does not supply an interior digit: an all-terminal singleton
is an antichain too.
The extracted coordinate alone is not a non-exposure or probability conclusion.
-/
theorem first_merge_or_before_public_terminal
    (height : Fin n → Nat) (address : Fin n → Nat → I) (step : I → D → Option D)
    (honest : Fin n → Nat → D)
    (settled : ∀ i k, k < height i →
      step (address i k) (honest i k) = some (honest i (k + 1)))
    (digits : Fin n → Nat) (values : Fin n → D)
    (interior : ∃ i, digits i < height i)
    (reaches : ∀ i,
      ((List.range' (digits i) (height i - digits i)).map (address i)).foldlM
        (fun value label => step label value) (values i) = some (honest i (height i))) :
    FirstMerge height address step honest digits values ∨
      ∃ i, digits i < height i ∧ values i = honest i (digits i) := by
  obtain ⟨i, before⟩ := interior
  rcases same_or_merge_at height address step honest settled digits values i
    before.le (reaches i) with canonical | merge
  · exact Or.inr ⟨i, before, canonical⟩
  · exact Or.inl merge

end HashChain
