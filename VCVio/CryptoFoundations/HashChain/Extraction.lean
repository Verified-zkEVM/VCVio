/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import Mathlib.Data.List.Basic

/-!
# First merges of finite addressed chains

A candidate reaching the honest endpoint starts at the honest value or first merges.
The merge uses distinct inputs at the same addressed step.
The witness records the candidate's actual prefix and every earlier unequal prefix.
The steps may fail, the labels may repeat, and neither carrier needs an equality instance.

The total-chain dichotomy also appears as `SLHDSA.chain_diverge` in
`HashSig/SLHDSA/Security/WotsWitnesses.lean`.
Here the computation is the public `List.foldlM` over arbitrary partial steps.
-/

public section

namespace HashChain

universe u v

/-- A successful candidate meets the honest chain first at an actual same-address merge.

Both inputs at that step are retained, and the earlier candidate prefixes remain unequal.
An empty chain can only return its initial value.
-/
theorem foldlM_eq_some_same_or_first_merge
    {I : Type u} {D : Type v} (step : I → D → Option D)
    (labels : List I) (honest : Nat → D)
    (settled : ∀ (k : Nat) (hk : k < labels.length),
      step labels[k] (honest k) = some (honest (k + 1)))
    (candidate : D)
    (reaches : labels.foldlM (fun value label => step label value) candidate =
      some (honest labels.length)) :
    candidate = honest 0 ∨
      ∃ (k : Nat) (hk : k < labels.length) (value : D),
        (labels.take k).foldlM (fun value label => step label value) candidate = some value ∧
        value ≠ honest k ∧
        step labels[k] value = some (honest (k + 1)) ∧
        step labels[k] (honest k) = some (honest (k + 1)) ∧
        (∀ j, j ≤ k → ∃ earlierValue : D,
          (labels.take j).foldlM (fun value label => step label value) candidate =
            some earlierValue ∧
          earlierValue ≠ honest j) := by
  classical
  induction labels generalizing honest candidate with
  | nil =>
    exact Or.inl (by simpa using reaches)
  | cons label labels ih =>
    by_cases same : candidate = honest 0
    · exact Or.inl same
    · apply Or.inr
      -- A failed first step cannot have a successful terminal result.
      cases first : step label candidate with
      | none => simp [List.foldlM_cons, first] at reaches
      | some next =>
        have rest : labels.foldlM (fun value label => step label value) next =
            some (honest (labels.length + 1)) := by
          simpa only [List.foldlM_cons, first, Option.bind_eq_bind, Option.bind_some,
            List.length_cons] using reaches
        by_cases meets : next = honest 1
        · refine ⟨0, by simp, candidate, rfl, same, ?_, settled 0 (by simp), ?_⟩
          · exact first.trans (congrArg some meets)
          · intro j hj
            have zero : j = 0 := Nat.eq_zero_of_le_zero hj
            subst j
            exact ⟨candidate, rfl, same⟩
        · -- Shift the settled trajectory by exactly the head already executed.
          have tailSettled : ∀ (k : Nat) (hk : k < labels.length),
              step labels[k] (honest (k + 1)) = some (honest (k + 1 + 1)) := by
            intro k hk
            simpa only [List.getElem_cons_succ] using settled (k + 1) (Nat.succ_lt_succ hk)
          rcases ih (honest := fun k => honest (k + 1)) (candidate := next)
            tailSettled rest with equal |
              ⟨k, hk, value, prefixRun, different, merged, honestStep, prior⟩
          · exact (meets equal).elim
          · refine ⟨k + 1, Nat.succ_lt_succ hk, value, ?_, different, ?_, ?_, ?_⟩
            · simpa only [List.take_succ_cons, List.foldlM_cons, first,
                Option.bind_eq_bind, Option.bind_some] using prefixRun
            · simpa only [List.getElem_cons_succ] using merged
            · simpa only [List.getElem_cons_succ] using honestStep
            · intro j hj
              cases j with
              | zero => exact ⟨candidate, rfl, same⟩
              | succ j =>
                obtain ⟨earlier, earlierPrefix, earlierDifferent⟩ :=
                  prior j (Nat.le_of_succ_le_succ hj)
                refine ⟨earlier, ?_, earlierDifferent⟩
                simpa only [List.take_succ_cons, List.foldlM_cons, first,
                  Option.bind_eq_bind, Option.bind_some] using earlierPrefix

end HashChain
