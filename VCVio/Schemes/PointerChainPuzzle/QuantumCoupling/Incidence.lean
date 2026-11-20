/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling
import VCVio.Schemes.PointerChainPuzzle.LeanSealDelay

/-!
# Incidence of raw pointer-chain inputs

The raw encoding preserves the classical future-input incidence bound under resampling outside
an honest rank prefix. All path labels remain unconditional, and the public commitment stays
fixed while its input is still included among the future inputs.
-/

public section

open OracleSpec OracleComp Quantum MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PointerChainPuzzle.LeanSeal

variable {b n m B : ℕ} [NeZero n]

/-- A fixed raw byte string hits an input beyond the next honest round with probability at most
`hitBound`, under uniform resampling of labels outside the current rank prefix. -/
theorem prEvent_eq_futurePathWindowInput_mixLabels_le
    (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B) (salt : Bytes 16) (x : Bytes b)
    (z : Fin (n - 1) → Bytes b) (ℓ₀ : Labels n m (Bytes 32) (Bytes b)) (r : ℕ)
    (t : ByteArray.Bounded B) :
    Pr{let ℓ' ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[
      ∃ v : PathValue n m, r + 1 < v.rho ∧
        t = pathWindowInput hB salt x z v
          (mixLabels (PathValue.rankPrefix n m r) ℓ₀ ℓ')] ≤
      hitBound n m (Bytes 32) (Bytes b) := by
  classical
  by_cases ht : ∃ u : TypedPoint b n, hashInputWindow hB u = t
  · obtain ⟨u, rfl⟩ := ht
    refine (prEvent_mono _ _ _ fun ℓ' ⟨v, hv, he⟩ ↦ ?_).trans
      (prEvent_mem_futurePathInputs_mixLabels_le
        (m := m) (mkCtx := ctx b n m) (initAcc := id)
        (labelPuzzle salt x z ℓ₀) ℓ₀ r u)
    refine ⟨v, hv, ?_⟩
    have hp := hashInputWindow_injective hB hn he
    simpa only [pathWindowInput, labelPuzzle_mixLabels] using hp
  · apply le_trans (b := 0)
    · exact le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun ℓ' ⟨v, _, he⟩ ↦
        ht ⟨_, he.symm⟩)
    · exact zero_le

end PointerChainPuzzle.LeanSeal
