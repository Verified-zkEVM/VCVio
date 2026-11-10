/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.CryptoFoundations.HashChain.Antichain

/-!
# Structural antichain payload controls

The controls retain actual prefix witnesses, changed equal-digit values and empty families.
An all-terminal singleton shows why the no-reveal theorem needs its interior condition.
No message, nonce, probability or exposure interpretation is supplied.
-/

public section

namespace HashChainAntichainTest

open HashChain

universe u v

variable {n : Nat} {I : Type u} {D : Type v}

/-- Ordinary imports expose an actual successful prefix at the witnessed chain position. -/
theorem actual_prefix (height : Fin n → Nat) (address : Fin n → Nat → I)
    (step : I → D → Option D) (honest : Fin n → Nat → D)
    (digits : Fin n → Nat) (values : Fin n → D)
    (merge : FirstMerge height address step honest digits values) :
    ∃ i, let labels := (List.range' (digits i) (height i - digits i)).map (address i)
      ∃ k, k < labels.length ∧ ∃ value,
        (labels.take k).foldlM (fun value label => step label value) (values i) = some value ∧
        value ≠ honest i (digits i + k) ∧
        step (address i (digits i + k)) value = some (honest i (digits i + k + 1)) := by
  obtain ⟨i, k, hk, value, prefixRun, different, merged, _, _⟩ := merge
  exact ⟨i, k, hk, value, prefixRun, different, merged⟩

/-- Repeated labels and changed equal-digit values still force an actual first merge. -/
theorem repeated_labels_changed_values_merge (height : Fin n → Nat) (label : I)
    (step : I → D → Option D) (honest : Fin n → Nat → D)
    (settled : ∀ i k, k < height i →
      step label (honest i k) = some (honest i (k + 1)))
    (accepted : Set (Fin n → Nat))
    (bounded : ∀ digits ∈ accepted, ∀ i, digits i ≤ height i)
    (antichain : IsAntichain (· ≤ ·) accepted) (signed : Fin n → Nat)
    (signedAccepted : signed ∈ accepted) (values : Fin n → D)
    (different : values ≠ fun i => honest i (signed i))
    (reaches : ∀ i,
      ((List.range' (signed i) (height i - signed i)).map (fun _ => label)).foldlM
        (fun value label => step label value) (values i) = some (honest i (height i))) :
    FirstMerge height (fun _ _ => label) step honest signed values := by
  rcases same_payload_or_first_merge_or_earlier height (fun _ _ => label) step honest settled
    accepted bounded antichain signed signed signedAccepted signedAccepted values reaches with
    same | merge | ⟨i, earlier, _⟩
  · exact (different same.2).elim
  · exact merge
  · exact (Nat.lt_irrefl _ earlier).elim

/-- An empty family returns exact abstract payload equality and cannot select a coordinate. -/
theorem empty_family (height : Fin 0 → Nat) (address : Fin 0 → Nat → I)
    (step : I → D → Option D) (honest : Fin 0 → Nat → D)
    (accepted : Set (Fin 0 → Nat)) (signed digits : Fin 0 → Nat)
    (signedAccepted : signed ∈ accepted) (candidateAccepted : digits ∈ accepted)
    (values : Fin 0 → D) :
    digits = signed ∧ values = fun i => honest i (signed i) := by
  have small : accepted.Subsingleton := fun _ _ _ _ => funext fun i => Fin.elim0 i
  have result := same_payload_or_first_merge_or_earlier height address step honest
    (fun i => Fin.elim0 i) accepted (fun _ _ i => Fin.elim0 i)
    (small.isAntichain (· ≤ ·)) signed digits signedAccepted candidateAccepted values
    (fun i => Fin.elim0 i)
  rcases result with same | ⟨i, _⟩ | ⟨i, _⟩
  · exact same
  · exact Fin.elim0 i
  · exact Fin.elim0 i

/-- Antichain acceptedness permits entirely public terminal payloads without an interior policy. -/
theorem all_terminal_counterexample (height : Fin n → Nat) (address : Fin n → Nat → I)
    (step : I → D → Option D) (honest : Fin n → Nat → D) :
    IsAntichain (· ≤ ·) ({height} : Set (Fin n → Nat)) ∧
      (∀ i, ((List.range' (height i) (height i - height i)).map (address i)).foldlM
        (fun value label => step label value) (honest i (height i)) =
          some (honest i (height i))) ∧
      ¬ FirstMerge height address step honest height (fun i => honest i (height i)) ∧
      ¬ ∃ i, height i < height i := by
  refine ⟨IsAntichain.singleton, ?_, ?_, ?_⟩
  · intro i
    simp
  · rintro ⟨i, k, hk, _⟩
    simp at hk
  · rintro ⟨i, smaller⟩
    exact Nat.lt_irrefl _ smaller

/-- A missing first step cannot be reinterpreted as a successful complete suffix. -/
theorem missing_step_fails (step : I → D → Option D) (label : I) (rest : List I)
    (initial terminal : D) (missing : step label initial = none) :
    (label :: rest).foldlM (fun value label => step label value) initial ≠ some terminal := by
  simp [List.foldlM_cons, missing]

/-- A local policy on accepted digits supplies the explicit no-reveal interior premise. -/
theorem no_reveal_from_policy (height : Fin n → Nat) (address : Fin n → Nat → I)
    (step : I → D → Option D) (honest : Fin n → Nat → D)
    (settled : ∀ i k, k < height i →
      step (address i k) (honest i k) = some (honest i (k + 1)))
    (accepted : Set (Fin n → Nat))
    (interiorPolicy : ∀ digits ∈ accepted, ∃ i, digits i < height i)
    (digits : Fin n → Nat) (candidateAccepted : digits ∈ accepted) (values : Fin n → D)
    (reaches : ∀ i,
      ((List.range' (digits i) (height i - digits i)).map (address i)).foldlM
        (fun value label => step label value) (values i) = some (honest i (height i))) :
    FirstMerge height address step honest digits values ∨
      ∃ i, digits i < height i ∧ values i = honest i (digits i) :=
  first_merge_or_before_public_terminal height address step honest settled digits values
    (interiorPolicy digits candidateAccepted) reaches

end HashChainAntichainTest
