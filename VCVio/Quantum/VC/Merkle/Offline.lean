/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineSecurity
public import VCVio.CryptoFoundations.MerkleTree.Salted.Commutativity
public import VCVio.CryptoFoundations.MerkleTree.Salted.Extraction
public import VCVio.Quantum.VC.Merkle.Online
public import VCVio.OracleComp.QueryTracking.Instability.Collision

/-!
# Offline extractability of salted Merkle commitments

The collision and instability bounds control the original bad-database weight. Checked
challenger reads add only the two batch distances, including leaf hashes at depth zero.
The scalar bundle keeps the minimum of both bad-database bounds: twice that numerator
plus the checker term, divided by `N` and capped at one. Its collision branch has leading
term `(7/2) · w · t² / N`, where `w = min wVC t`.
-/

public section

open Quantum OracleSpec
open scoped ENNReal Kronecker
namespace SaltedMerkle

/-- The best of the trace cap, generic instability bound, and collision bound. -/
@[expose]
noncomputable def merkleOfflineBadError (N t : ℕ) (wVC : ℝ≥0∞) : ℝ≥0∞ :=
  let w := min wVC (t : ℝ≥0∞)
  min 1 (min (24 * (t : ℝ≥0∞) * w * (t - 1 : ℕ) / N)
    ((7 * (t : ℝ≥0∞) + 5) * t * w / (4 * N)))

/-- The two-amplitude Merkle offline bound, with every cross term retained. -/
@[expose]
noncomputable def merkleOfflineAmplitudeError (N dmax t : ℕ) (wVC : ℝ≥0∞) (qs : ℕ) : ℝ≥0∞ :=
  min 1 ((merkleOfflineBadError N t wVC ^ (2⁻¹ : ℝ) +
    2 * (((qs * (dmax + 1) : ℕ) : ℝ≥0∞) / N) ^ (2⁻¹ : ℝ)) ^ 2)

/-- A monotone checked offline bound: twice the minimum bad-database numerator plus
the checker term, over `N`, capped at one. With `w = min wVC t`, the collision branch
has leading term `(7/2) · w · t² / N`. -/
@[expose]
noncomputable def merkleOfflineError (N dmax t : ℕ) (wVC : ℝ≥0∞) (qs : ℕ) : ℝ≥0∞ :=
  let w := min wVC (t : ℝ≥0∞)
  min 1 ((2 * min (24 * (t : ℝ≥0∞) * w * (t - 1 : ℕ))
    ((7 * (t : ℝ≥0∞) + 5) * t * w / 4) + 8 * (qs * (dmax + 1) : ℕ)) / N)

/-- The finite-query Merkle errors, with the collision-sensitive checked offline bound.
Its offline numerator is twice the minimum bad-database numerator plus the checker term;
the collision branch has leading term `(7/2) · min wVC t · t² / N`. -/
@[expose]
noncomputable def merkleErrors (N dmax : ℕ) : MEErrors where
  sim := fun _ ↦ 0
  com := comErrorBound (Y := Fin N)
  extract := fun _ _ _ n ↦ extractErrorBound (Y := Fin N) (2 ^ dmax) n
  offline := fun t wVC _ qs ↦ merkleOfflineError N dmax t wVC qs
  online := fun t wVC _ _ ↦ merkleOnlineError N t wVC

open scoped Classical in
private theorem offline_instability_le {X Y : Type} [DecidableEq X]
    [Fintype Y] [UniformAnswerMeasure (X →ₒ Y)] (t : ℕ) :
    Database.instability (offlineLabel (collisionFree : Set (Database X Y))) t ≤
      ((t - 1 : ℕ) : ℝ≥0∞) / Fintype.card Y := by
  classical
  have hp : Database.labelPartition (offlineLabel (collisionFree : Set (Database X Y))) =
      (fun b : Bool ↦ cond b {D : QueryCache (X →ₒ Y) | ¬ OracleComp.CacheHasCollision D}
        {D : QueryCache (X →ₒ Y) | ¬ OracleComp.CacheHasCollision D}ᶜ) := by
    funext b
    ext D
    cases b <;> simp [Database.labelPartition, offlineLabel, mem_collisionFree_iff]
  rw [Database.instability, hp, QueryCache.partitionInstability_cond]
  change QueryCache.instability {D : QueryCache (X →ₒ Y) | OracleComp.CacheHasCollision D}ᶜ t ≤ _
  rw [QueryCache.instability_compl]
  exact QueryCache.instability_cacheHasCollision_le (fun _ ↦ le_rfl) t

private theorem q1_le {X Y Msg Salt : Type} [DecidableEq X] [DecidableEq Y]
    [SampleableType Salt]
    (enc : MerkleTreeHashing.QueryEncoding X Unit Unit (Msg × Salt) Y) {k : ℕ} (d : Fin k → ℕ)
    (dmax qs : ℕ) (hd : ∀ i, d i ≤ dmax) :
    q1 (fun i ↦ nonadaptiveCheck enc (d i)) qs ≤ qs * (dmax + 1) := by
  obtain ⟨v, hv, he⟩ := exists_sum_qVC_eq_q1 (fun i ↦ nonadaptiveCheck enc (d i)) qs
  rw [← he]
  calc
    _ = ∑ i, v i * (d i + 1) := rfl
    _ ≤ ∑ i, v i * (dmax + 1) := by gcongr with i; exact hd i
    _ = (∑ i, v i) * (dmax + 1) := (Finset.sum_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hv

variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [AddCommGroup Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  [SampleableType Salt]
  (enc : MerkleTreeHashing.QueryEncoding X Unit Unit (Msg × Salt) Y) {k : ℕ} (d : Fin k → ℕ)
  {Z : Type} [Fintype Z] [DecidableEq Z] [AddGroup Z]

universe v w

/-- Offline extractability with the collision-sensitive two-amplitude error. -/
theorem merkle_offline_amplitude
    (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i))) Z)
    (dmax : ℕ) (hd : ∀ i, d i ≤ dmax) :
    OfflineExtractable.{v, w} (fun i ↦ (scheme enc (d i)).toVectorCommitment)
      (compressedVCOracle k X Y) (multiExtract enc d) code
      (fun t wVC _ qs ↦ merkleOfflineAmplitudeError (Fintype.card Y) dmax t wVC qs) := by
  classical
  let : UniformAnswerMeasure (X →ₒ Y) := UniformAnswerMeasure.ofFiniteNonempty _
  have h := offlineExtractable_compressedVCOracle_of_badEvent
    (fun i ↦ nonadaptiveCheck enc (d i)) (multiExtract enc d) (fun _ ↦ tdBot) collisionFree
    (conditions enc d) code (merkleOfflineBadError (Fintype.card Y)) ?_
  · apply h.mono
    intro t wVC wME qs
    dsimp only [merkleOfflineAmplitudeError]
    gcongr
    exact_mod_cast q1_le enc d dmax qs hd
  · intro t w A W x ρ hx hw
    let E := (compressedVCOracle k X Y).withExtract (multiExtract enc d) code
    have hg := badEvent_compressedWithExtract_le (multiExtract enc d) code collisionFree
      empty_mem_collisionFree .instruments x hx ρ
    have hQ := isStarProjection_familyBadProjector (k := k) (collisionFree : Set (Database X Y))
    have hcap := (QuantumRuntime.eventWeight_le_trace .instruments E.coherent.toRuntime
      hQ.isSelfAdjoint hQ.isIdempotentElem x (ρ.prod E.init).posSemidef).trans
        (ENNReal.ofReal_le_one.mpr (ρ.prod E.init).trace_re_le_one)
    apply le_min hcap
    apply le_min
    · calc
        _ ≤ 24 * (t : ℝ≥0∞) * min w t *
            Database.instability (offlineLabel (collisionFree : Set (Database X Y))) t := by
          apply hg.trans
          gcongr
          convert hw using 1
          rfl
        _ ≤ 24 * (t : ℝ≥0∞) * min w t * (((t - 1 : ℕ) : ℝ≥0∞) / Fintype.card Y) := by
          gcongr
          exact offline_instability_le t
        _ = _ := by rw [mul_div_assoc]
    · have he : (collisionFree : Set (Database X Y)) = {D | D.CollisionFree} := rfl
      rw [he, familyBadProjector_collisionFree]
      have hc := collisionEvent_compressedWithExtract_le (multiExtract enc d) code
        .instruments x hx ρ
      refine hc.trans ?_
      have hn : (0 : ℝ) < Fintype.card Y := by positivity
      rw [ENNReal.ofReal_div_of_pos (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity)]
      norm_num only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
      rw [ENNReal.ofReal_mul (by positivity)]
      norm_num only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
      have hw' : ∑ i : Fin k, E.totalMass .instruments x
          (ρ.matrix ⊗ₖ E.init.matrix) (.inl i) ≤ w := by
        convert hw using 1
        rfl
      exact (mul_le_mul_right (min_le_min hw' (le_rfl : (t : ℝ≥0∞) ≤ t)) _).trans_eq
        (by simp only [div_eq_mul_inv]; ring)


/-- The two-amplitude error is bounded by its quadratic monotone facade. -/
theorem merkleOfflineAmplitudeError_le {N : ℕ} (hN : 0 < N)
    (dmax t : ℕ) (w : ℝ≥0∞) (qs : ℕ) :
    merkleOfflineAmplitudeError N dmax t w qs ≤ merkleOfflineError N dmax t w qs := by
  let b := merkleOfflineBadError N t w
  let q : ℝ≥0∞ := (qs * (dmax + 1) : ℕ) / N
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
  have hq : q ≠ ⊤ := by dsimp [q]; finiteness
  have ha : b ^ (2⁻¹ : ℝ) ≠ ⊤ := by finiteness
  have hc : 2 * q ^ (2⁻¹ : ℝ) ≠ ⊤ := by finiteness
  have hsq : (b ^ (2⁻¹ : ℝ) + 2 * q ^ (2⁻¹ : ℝ)) ^ 2 ≤ 2 * (b + 4 * q) := by
    have h : (b ^ (2⁻¹ : ℝ) + 2 * q ^ (2⁻¹ : ℝ)) ^ 2 ≤
        2 * ((b ^ (2⁻¹ : ℝ)) ^ 2 + (2 * q ^ (2⁻¹ : ℝ)) ^ 2) := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simpa only [ENNReal.toReal_pow, ENNReal.toReal_mul,
        ENNReal.toReal_add ha hc,
        ENNReal.toReal_add (ENNReal.pow_ne_top ha) (ENNReal.pow_ne_top hc),
        ENNReal.toReal_ofNat] using
          (add_sq_le (a := (b ^ (2⁻¹ : ℝ)).toReal) (b := (2 * q ^ (2⁻¹ : ℝ)).toReal))
    have hs (x : ℝ≥0∞) : (x ^ (2⁻¹ : ℝ)) ^ 2 = x := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    simpa only [mul_pow, hs, show (2 : ℝ≥0∞) ^ 2 = 4 by norm_num] using h
  apply min_le_min_left 1
  refine hsq.trans ?_
  let num := min (24 * (t : ℝ≥0∞) * min w t * (t - 1 : ℕ))
    ((7 * (t : ℝ≥0∞) + 5) * t * min w t / 4)
  have hbad : b ≤ num / N := by
    dsimp [b, merkleOfflineBadError, num]
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv (by simp) (by simp), ← mul_assoc, ← min_mul]
    exact min_le_right _ _
  calc
    _ ≤ 2 * (num / N + 4 * q) := by gcongr
    _ = _ := by dsimp only [q, num]; simp only [div_eq_mul_inv]; ring

/-- Offline extractability for salted Merkle commitments at varying bounded depths. -/
theorem merkle_offline
    (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i))) Z)
    (dmax : ℕ) (hd : ∀ i, d i ≤ dmax) :
    OfflineExtractable.{v, w} (fun i ↦ (scheme enc (d i)).toVectorCommitment)
      (compressedVCOracle k X Y) (multiExtract enc d) code
      (merkleErrors (Fintype.card Y) dmax).offline :=
  (merkle_offline_amplitude enc d code dmax hd).mono fun t w _ qs ↦
    merkleOfflineAmplitudeError_le (by positivity) dmax t w qs

end SaltedMerkle
