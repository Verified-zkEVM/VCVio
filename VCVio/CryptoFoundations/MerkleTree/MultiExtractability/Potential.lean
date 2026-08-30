/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.AdaptivePrefix

/-!
# Exact Shared-Log Potential for Merkle Multi-Extractability

This module owns the arithmetic security budget for a finite family of Merkle commitment
checkpoints sharing one random-oracle log. If the extracted checkpoint trees contain at most
`nodeBudget` nodes in total and there are `checkpointCount` roots, then a log backed by `k`
distinct oracle keys exposes at most

`min nodeBudget (2 * k + checkpointCount)`

distinct candidate labels: every populated key contributes its two ordered children and every
checkpoint contributes its root. This shared-log cap is strictly sharper than multiplying the
single-tree `min (2L - 1) (2k + 1)` cap by the number of checkpoints.

The exact numerator is a finite maximum over the adaptive commitment-prefix cache misses. Coarse
closed forms are derived below as corollaries; they are not used as the primary theorem budget.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open OracleComp

/-- Sharp structural cap on the union of labels reachable in all checkpoint extractions from a
shared log containing `keyCount` populated complete queries. -/
def sharedTargetCount (nodeBudget checkpointCount keyCount : ℕ) : ℕ :=
  min nodeBudget (2 * keyCount + checkpointCount)

/-- Exact adaptive-prefix potential for multi-extractability. `verifierOverhead` counts honest
suffix queries separately from the adversary's remaining two-phase query budget. -/
def multiExtractabilityPotential
    (nodeBudget checkpointCount verifierOverhead remaining cached : ℕ) : ℕ :=
  adaptivePrefixPotential
    (sharedTargetCount nodeBudget checkpointCount)
    verifierOverhead remaining cached

/-- Unrelaxed shared-ROM error numerator from an empty cache. -/
def multiExtractabilityROMErrorNumerator
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ) : ℕ :=
  multiExtractabilityPotential
    nodeBudget checkpointCount verifierOverhead queryBound 0

/-- The exact numerator is the finite maximum over every feasible number of fresh prefix inputs.
This theorem is the intended rewrite interface for audits and downstream arithmetic relaxations. -/
theorem multiExtractabilityROMErrorNumerator_eq_sup
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ) :
    multiExtractabilityROMErrorNumerator
        nodeBudget checkpointCount verifierOverhead queryBound =
      (Finset.range (queryBound + 1)).sup fun prefixMisses =>
        prefixMisses.choose 2 +
          min nodeBudget (2 * prefixMisses + checkpointCount) *
            (queryBound - prefixMisses + verifierOverhead) := by
  simp [multiExtractabilityROMErrorNumerator, multiExtractabilityPotential,
    adaptivePrefixPotential, adaptivePrefixEnergy, sharedTargetCount]

/-- Shared extraction never exposes more candidates than the total node budget. -/
theorem sharedTargetCount_le_nodeBudget
    (nodeBudget checkpointCount keyCount : ℕ) :
    sharedTargetCount nodeBudget checkpointCount keyCount ≤ nodeBudget :=
  Nat.min_le_left _ _

/-- Shared extraction never exposes more than two children per populated complete query plus one
root per checkpoint. -/
theorem sharedTargetCount_le_querySupport
    (nodeBudget checkpointCount keyCount : ℕ) :
    sharedTargetCount nodeBudget checkpointCount keyCount ≤ 2 * keyCount + checkpointCount :=
  Nat.min_le_right _ _

/-- Coarse closed form obtained from the exact finite maximum by separately maximizing the
birthday and target-hit terms. -/
theorem multiExtractabilityROMErrorNumerator_le_coarse
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ) :
    multiExtractabilityROMErrorNumerator
        nodeBudget checkpointCount verifierOverhead queryBound ≤
      queryBound.choose 2 + nodeBudget * (queryBound + verifierOverhead) := by
  rw [multiExtractabilityROMErrorNumerator_eq_sup]
  apply Finset.sup_le
  intro prefixMisses hprefix
  simp only [Finset.mem_range] at hprefix
  have hmisses : prefixMisses ≤ queryBound := by omega
  have hchoose : prefixMisses.choose 2 ≤ queryBound.choose 2 :=
    Nat.choose_le_choose 2 hmisses
  have htarget : min nodeBudget (2 * prefixMisses + checkpointCount) ≤ nodeBudget :=
    Nat.min_le_left _ _
  have hremaining : queryBound - prefixMisses + verifierOverhead ≤
      queryBound + verifierOverhead := by omega
  exact Nat.add_le_add hchoose (Nat.mul_le_mul htarget hremaining)

/-- A still simpler quadratic relaxation, useful when a consumer does not want binomial
coefficients in its public statement. -/
theorem multiExtractabilityROMErrorNumerator_le_quadratic
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ) :
    multiExtractabilityROMErrorNumerator
        nodeBudget checkpointCount verifierOverhead queryBound ≤
      queryBound * queryBound + nodeBudget * (queryBound + verifierOverhead) := by
  exact (multiExtractabilityROMErrorNumerator_le_coarse
    nodeBudget checkpointCount verifierOverhead queryBound).trans (by
      gcongr
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ 2).trans
        (Nat.mul_le_mul_left queryBound (Nat.sub_le queryBound 1)))

end MerkleTreeMultiExtractability
