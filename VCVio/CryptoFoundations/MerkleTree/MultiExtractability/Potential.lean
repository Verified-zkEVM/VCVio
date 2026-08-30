/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.AdaptivePrefix

/-!
# Safe Shared-Log Potential for Merkle Multi-Extractability

This module owns the arithmetic security budget for a finite family of Merkle commitment
checkpoints sharing one random-oracle log. If the extracted checkpoint trees contain at most
`nodeBudget` nodes in total and there are `checkpointCount` roots, then a log backed by `k`
distinct oracle keys exposes at most

`min nodeBudget (2 * k + checkpointCount)`

distinct candidate labels: every populated key contributes its two ordered children and every
checkpoint contributes its root. This shared-log cap is strictly sharper than multiplying the
single-tree `min (2L - 1) (2k + 1)` cap by the number of checkpoints.

The safe numerator is a finite maximum over fresh adversarial inputs across every commitment
phase and terminal opening production. It deliberately overcharges queries made before a target
exists. `MultiExtractability.OnlineBound` proves the checkpoint-aware stopping recurrence for this
envelope; this module still does not identify it with a tighter textbook potential. Coarse closed
forms are derived below as corollaries.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open OracleComp

/-- Sharp structural cap on the union of labels reachable in all checkpoint extractions from a
shared log containing `keyCount` populated complete queries. -/
def sharedTargetCount (nodeBudget checkpointCount keyCount : ℕ) : ℕ :=
  min nodeBudget (2 * keyCount + checkpointCount)

/-- Existing terminal-suffix potential. This charges target hits only after the adaptive prefix
has terminated and is therefore suitable for a single checkpoint, but not by itself for
checkpoint evolution during a multi-commitment prefix. -/
def terminalSuffixPotential
    (nodeBudget checkpointCount verifierOverhead remaining cached : ℕ) : ℕ :=
  adaptivePrefixPotential
    (sharedTargetCount nodeBudget checkpointCount)
    verifierOverhead remaining cached

/-- Multi-checkpoint stopping energy after `prefixMisses` fresh inputs. In addition to cache
collision terms, the shared target set is charged against the entire remaining adversarial budget:
a later commitment query may hit a target of an earlier checkpoint even before the terminal
opening suffix begins. -/
def multiCheckpointEnergy
    (nodeBudget checkpointCount verifierOverhead remaining cached prefixMisses : ℕ) : ℕ :=
  prefixMisses * cached + prefixMisses.choose 2 +
    sharedTargetCount nodeBudget checkpointCount (cached + prefixMisses) *
      (remaining + verifierOverhead)

/-- Finite maximum of the multi-checkpoint energy over every feasible number of fresh prefix
inputs. A probability theorem consuming this budget must separately prove the checkpoint-aware
stopping lemma; unlike `terminalSuffixPotential`, this definition does not silently reuse the
single-checkpoint adaptive-prefix theorem. -/
def multiExtractabilitySafePotential
    (nodeBudget checkpointCount verifierOverhead remaining cached : ℕ) : ℕ :=
  (Finset.range (remaining + 1)).sup fun prefixMisses =>
    multiCheckpointEnergy nodeBudget checkpointCount verifierOverhead remaining cached
      prefixMisses

/-- Unrelaxed shared-ROM error numerator from an empty cache. -/
def multiExtractabilitySafeNumerator
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ) : ℕ :=
  multiExtractabilitySafePotential
    nodeBudget checkpointCount verifierOverhead queryBound 0

/-- The safe, unrelaxed numerator is the finite maximum over every feasible number of fresh
adversarial inputs.
This theorem is the intended rewrite interface for audits and downstream arithmetic relaxations. -/
theorem multiExtractabilitySafeNumerator_eq_sup
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ) :
    multiExtractabilitySafeNumerator
        nodeBudget checkpointCount verifierOverhead queryBound =
      (Finset.range (queryBound + 1)).sup fun prefixMisses =>
        prefixMisses.choose 2 +
          min nodeBudget (2 * prefixMisses + checkpointCount) *
            (queryBound + verifierOverhead) := by
  simp [multiExtractabilitySafeNumerator, multiExtractabilitySafePotential,
    multiCheckpointEnergy, sharedTargetCount]

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

/-- The safe shared-target cap is monotone as fresh complete-query keys accumulate. -/
theorem sharedTargetCount_mono_keyCount
    (nodeBudget checkpointCount : ℕ) :
    Monotone (sharedTargetCount nodeBudget checkpointCount) := by
  intro left right hle
  unfold sharedTargetCount
  gcongr

/-- The shared target cap is monotone in both global resource envelopes. -/
theorem sharedTargetCount_mono_budget
    {leftNodeBudget rightNodeBudget leftCheckpointCount rightCheckpointCount keyCount : ℕ}
    (hnodes : leftNodeBudget ≤ rightNodeBudget)
    (hcheckpoints : leftCheckpointCount ≤ rightCheckpointCount) :
    sharedTargetCount leftNodeBudget leftCheckpointCount keyCount ≤
      sharedTargetCount rightNodeBudget rightCheckpointCount keyCount := by
  unfold sharedTargetCount
  gcongr

/-- Enlarging the global node/checkpoint envelope can only enlarge the online energy. -/
theorem multiCheckpointEnergy_mono_budget
    {leftNodeBudget rightNodeBudget leftCheckpointCount rightCheckpointCount : ℕ}
    (hnodes : leftNodeBudget ≤ rightNodeBudget)
    (hcheckpoints : leftCheckpointCount ≤ rightCheckpointCount)
    (verifierOverhead remaining cached prefixMisses : ℕ) :
    multiCheckpointEnergy leftNodeBudget leftCheckpointCount verifierOverhead
        remaining cached prefixMisses ≤
      multiCheckpointEnergy rightNodeBudget rightCheckpointCount verifierOverhead
        remaining cached prefixMisses := by
  unfold multiCheckpointEnergy
  gcongr
  exact sharedTargetCount_mono_budget hnodes hcheckpoints

/-- Enlarging the global node/checkpoint envelope can only enlarge the safe potential. -/
theorem multiExtractabilitySafePotential_mono_budget
    {leftNodeBudget rightNodeBudget leftCheckpointCount rightCheckpointCount : ℕ}
    (hnodes : leftNodeBudget ≤ rightNodeBudget)
    (hcheckpoints : leftCheckpointCount ≤ rightCheckpointCount)
    (verifierOverhead remaining cached : ℕ) :
    multiExtractabilitySafePotential leftNodeBudget leftCheckpointCount verifierOverhead
        remaining cached ≤
      multiExtractabilitySafePotential rightNodeBudget rightCheckpointCount verifierOverhead
        remaining cached := by
  unfold multiExtractabilitySafePotential
  apply Finset.sup_mono_fun
  intro prefixMisses _
  exact multiCheckpointEnergy_mono_budget hnodes hcheckpoints
    verifierOverhead remaining cached prefixMisses

/-- More remaining adversarial syntax can only enlarge the online energy. -/
theorem multiCheckpointEnergy_mono_remaining
    (nodeBudget checkpointCount verifierOverhead cached prefixMisses : ℕ) :
    Monotone fun remaining =>
      multiCheckpointEnergy nodeBudget checkpointCount verifierOverhead
        remaining cached prefixMisses := by
  intro left right hremaining
  unfold multiCheckpointEnergy
  apply Nat.add_le_add_left
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hremaining verifierOverhead)

/-- The safe potential is monotone in the remaining adversarial query budget. -/
theorem multiExtractabilitySafePotential_mono_remaining
    (nodeBudget checkpointCount verifierOverhead cached : ℕ) :
    Monotone fun remaining =>
      multiExtractabilitySafePotential nodeBudget checkpointCount verifierOverhead
        remaining cached := by
  intro left right hremaining
  unfold multiExtractabilitySafePotential
  apply Finset.sup_le
  intro prefixMisses hprefix
  apply (multiCheckpointEnergy_mono_remaining nodeBudget checkpointCount
    verifierOverhead cached prefixMisses hremaining).trans
  apply Finset.le_sup
  simp only [Finset.mem_range] at hprefix ⊢
  omega

/-- Fresh-miss recurrence behind the safe online envelope. The local step pays collision against
the existing cache and a hit in the target set predictable before sampling; the continuation then
uses the enlarged cache. -/
theorem multiCheckpointEnergy_miss_step
    (nodeBudget checkpointCount verifierOverhead remaining cached continuationMisses : ℕ)
    (hremaining : 0 < remaining) :
    cached + sharedTargetCount nodeBudget checkpointCount cached +
        multiCheckpointEnergy nodeBudget checkpointCount verifierOverhead
          (remaining - 1) (cached + 1) continuationMisses ≤
      multiCheckpointEnergy nodeBudget checkpointCount verifierOverhead
        remaining cached (continuationMisses + 1) := by
  have hkeys : cached + 1 + continuationMisses =
      cached + (continuationMisses + 1) := by omega
  have hchoose : (continuationMisses + 1).choose 2 =
      continuationMisses + continuationMisses.choose 2 := by
    rw [show continuationMisses + 1 = continuationMisses.succ by omega,
      Nat.choose_succ_succ]
    simp
  have htarget := sharedTargetCount_mono_keyCount nodeBudget checkpointCount
    (show cached ≤ cached + (continuationMisses + 1) by omega)
  have htargetTerm :
      sharedTargetCount nodeBudget checkpointCount cached +
          sharedTargetCount nodeBudget checkpointCount
              (cached + (continuationMisses + 1)) *
            (remaining - 1 + verifierOverhead) ≤
        sharedTargetCount nodeBudget checkpointCount
            (cached + (continuationMisses + 1)) *
          (remaining + verifierOverhead) := by
    calc
      _ ≤ sharedTargetCount nodeBudget checkpointCount
              (cached + (continuationMisses + 1)) +
            sharedTargetCount nodeBudget checkpointCount
                (cached + (continuationMisses + 1)) *
              (remaining - 1 + verifierOverhead) :=
        Nat.add_le_add_right htarget _
      _ = _ := by
        have hremaining' : remaining + verifierOverhead =
            (remaining - 1 + verifierOverhead) + 1 := by omega
        rw [hremaining', Nat.mul_succ]
        omega
  have hcollision :
      cached + continuationMisses * (cached + 1) + continuationMisses.choose 2 =
        (continuationMisses + 1) * cached + (continuationMisses + 1).choose 2 := by
    rw [hchoose]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega
  unfold multiCheckpointEnergy
  rw [hkeys]
  calc
    cached + sharedTargetCount nodeBudget checkpointCount cached +
          (continuationMisses * (cached + 1) + continuationMisses.choose 2 +
            sharedTargetCount nodeBudget checkpointCount
                (cached + (continuationMisses + 1)) *
              (remaining - 1 + verifierOverhead)) =
        (cached + continuationMisses * (cached + 1) + continuationMisses.choose 2) +
          (sharedTargetCount nodeBudget checkpointCount cached +
            sharedTargetCount nodeBudget checkpointCount
                (cached + (continuationMisses + 1)) *
              (remaining - 1 + verifierOverhead)) := by ac_rfl
    _ ≤ ((continuationMisses + 1) * cached + (continuationMisses + 1).choose 2) +
          sharedTargetCount nodeBudget checkpointCount
              (cached + (continuationMisses + 1)) *
            (remaining + verifierOverhead) :=
      Nat.add_le_add (le_of_eq hcollision) htargetTerm
    _ = _ := rfl

private theorem multiCheckpointEnergy_zero
    (nodeBudget checkpointCount verifierOverhead remaining cached : ℕ) :
    multiCheckpointEnergy nodeBudget checkpointCount verifierOverhead remaining cached 0 =
      sharedTargetCount nodeBudget checkpointCount cached *
        (remaining + verifierOverhead) := by
  simp [multiCheckpointEnergy]

/-- Terminal target-hit budget is contained in the safe finite maximum. -/
theorem multiExtractabilitySafePotential_terminal_le
    (nodeBudget checkpointCount verifierOverhead remaining cached : ℕ) :
    sharedTargetCount nodeBudget checkpointCount cached *
        (remaining + verifierOverhead) ≤
      multiExtractabilitySafePotential
        nodeBudget checkpointCount verifierOverhead remaining cached := by
  rw [← multiCheckpointEnergy_zero]
  exact Finset.le_sup (by simp)

private theorem multiCheckpointEnergy_hit_le
    (nodeBudget checkpointCount verifierOverhead remaining cached misses : ℕ) :
    multiCheckpointEnergy nodeBudget checkpointCount verifierOverhead
        (remaining - 1) cached misses ≤
      multiCheckpointEnergy nodeBudget checkpointCount verifierOverhead
        remaining cached misses := by
  unfold multiCheckpointEnergy
  gcongr
  omega

/-- A cached query consumes remaining budget without increasing the cache or target cap. -/
theorem multiExtractabilitySafePotential_hit_le
    (nodeBudget checkpointCount verifierOverhead remaining cached : ℕ) :
    multiExtractabilitySafePotential nodeBudget checkpointCount verifierOverhead
        (remaining - 1) cached ≤
      multiExtractabilitySafePotential nodeBudget checkpointCount verifierOverhead
        remaining cached := by
  unfold multiExtractabilitySafePotential
  apply Finset.sup_le
  intro misses hmisses
  apply (multiCheckpointEnergy_hit_le nodeBudget checkpointCount verifierOverhead
    remaining cached misses).trans
  apply Finset.le_sup
  simp only [Finset.mem_range] at hmisses ⊢
  omega

/-- One fresh miss pays collision plus predictable live-target hit, then recurs with one more
populated key and one fewer query. -/
theorem multiExtractabilitySafePotential_miss_le
    (nodeBudget checkpointCount verifierOverhead remaining cached : ℕ)
    (hremaining : 0 < remaining) :
    cached + sharedTargetCount nodeBudget checkpointCount cached +
        multiExtractabilitySafePotential nodeBudget checkpointCount verifierOverhead
          (remaining - 1) (cached + 1) ≤
      multiExtractabilitySafePotential nodeBudget checkpointCount verifierOverhead
        remaining cached := by
  unfold multiExtractabilitySafePotential
  rw [Finset.add_sup (by simp)]
  apply Finset.sup_le
  intro continuationMisses hmisses
  apply (multiCheckpointEnergy_miss_step nodeBudget checkpointCount verifierOverhead
    remaining cached continuationMisses hremaining).trans
  apply Finset.le_sup
  simp only [Finset.mem_range] at hmisses ⊢
  omega

/-- Coarse closed form obtained from the safe finite maximum by separately maximizing the
birthday and target-hit terms. -/
theorem multiExtractabilitySafeNumerator_le_coarse
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ) :
    multiExtractabilitySafeNumerator
        nodeBudget checkpointCount verifierOverhead queryBound ≤
      queryBound.choose 2 + nodeBudget * (queryBound + verifierOverhead) := by
  rw [multiExtractabilitySafeNumerator_eq_sup]
  apply Finset.sup_le
  intro prefixMisses hprefix
  simp only [Finset.mem_range] at hprefix
  have hmisses : prefixMisses ≤ queryBound := by omega
  have hchoose : prefixMisses.choose 2 ≤ queryBound.choose 2 :=
    Nat.choose_le_choose 2 hmisses
  have htarget : min nodeBudget (2 * prefixMisses + checkpointCount) ≤ nodeBudget :=
    Nat.min_le_left _ _
  exact Nat.add_le_add hchoose (Nat.mul_le_mul_right _ htarget)

/-- A still simpler quadratic relaxation, useful when a consumer does not want binomial
coefficients in its public statement. -/
theorem multiExtractabilitySafeNumerator_le_quadratic
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ) :
    multiExtractabilitySafeNumerator
        nodeBudget checkpointCount verifierOverhead queryBound ≤
      queryBound * queryBound + nodeBudget * (queryBound + verifierOverhead) := by
  exact (multiExtractabilitySafeNumerator_le_coarse
    nodeBudget checkpointCount verifierOverhead queryBound).trans (by
      gcongr
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ 2).trans
        (Nat.mul_le_mul_left queryBound (Nat.sub_le queryBound 1)))

end MerkleTreeMultiExtractability
