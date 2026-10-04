/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.CryptoFoundations.UniversalHash

/-!
# Universal hash family checks

The masking family `h_k x = x ∧ k` on `K = D = T = BitVec 1`. For its only pair of distinct
inputs, `h_k x ⊕ h_k y = (x ⊕ y) ∧ k = k`, so `#{k | h_k x ⊕ h_k y = Δ} = 1` for every `Δ`. The
counting criterion makes the family `(1/2)`-AXU, which attains the floor `|T|⁻¹ = 1/2`.
-/

public section

open ENNReal UniversalHash

example : IsAlmostXorUniversal (fun (k x : BitVec 1) => x &&& k) (1 / 2 : ℝ≥0∞) := by
  simpa using isAlmostXorUniversal_of_card_le (K := BitVec 1) (d := 1) (by decide)

example : IsAlmostUniversal (fun (k x : BitVec 1) => x &&& k) (1 / 2 : ℝ≥0∞) := by
  have h : IsAlmostXorUniversal (fun (k x : BitVec 1) => x &&& k) (1 / 2 : ℝ≥0∞) := by
    simpa using isAlmostXorUniversal_of_card_le (K := BitVec 1) (d := 1) (by decide)
  exact h.isAlmostUniversal

example : (Fintype.card (BitVec 1) : ℝ≥0∞)⁻¹ = 1 / 2 := by
  simp
