/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldLeaf

/-!
# Offline extractability of the old salted Merkle checker

The adaptive leaf sum uses the actual ordinary/extraction runtime throughout. Collision,
checker discrepancy, invalid potential and the terminal component increment are added as
amplitudes before squaring.
-/

public section

open Matrix MeasureTheory
open scoped ENNReal Kronecker
namespace Quantum
universe u v w uL vL

/-- The original joint poststates of an arbitrary runtime have total trace at most one. -/
theorem QuantumRuntime.tsum_jointPost_trace_le_one {spec : QuantumOracleSpec.{u, v}}
    (R : QuantumRuntime spec) {L : LocalSig.{uL, vL}} (I : L.Interp)
    {A : QReg} {W : QReg → Type w} (x : QuantumComp L spec W A) (ρ : SubState A) :
    ∑' p, ENNReal.ofReal (R.jointPost I x ρ p).matrix.trace.re ≤ 1 := by
  exact ((R.run I x).isCPTNIFamily.tsum_ofReal_trace_re_le (ρ.prod R.init).posSemidef).trans
    (ENNReal.ofReal_le_one.mpr (ρ.prod R.init).trace_re_le_one)

/-- Every measurable runtime event has probability at most one. -/
theorem QuantumRuntime.outcomeLawWith_le_one {spec : QuantumOracleSpec.{u, v}}
    (R : QuantumRuntime spec) {L : LocalSig.{uL, vL}} (I : L.Interp)
    {A : QReg} {W : QReg → Type w} (x : QuantumComp L spec W A) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) (s : Set γ) :
    R.outcomeLawWith I x ρ f s ≤ 1 := by
  apply (measure_mono (Set.subset_univ s)).trans
  rw [R.outcomeLawWith_apply_univ I x ρ f, ← R.tsum_jointPost_trace I x ρ]
  exact R.tsum_jointPost_trace_le_one I x ρ

/-- A trace-weighted constant has total weight at most that constant. -/
theorem tsum_weighted_trace_le {P : Type*} (m : P → ℝ≥0∞) (hm : ∑' p, m p ≤ 1)
    (c : ℝ≥0∞) : ∑' p, c * m p ≤ c := by
  rw [ENNReal.tsum_mul_left]
  exact (mul_le_mul_right hm c).trans_eq (mul_one c)

/-- The square root of four times a nonnegative real is twice its square root in ENNReal. -/
theorem ofReal_four_mul_rpow (a : ℝ) :
    ENNReal.ofReal (4 * a) ^ (2⁻¹ : ℝ) = 2 * ENNReal.ofReal a ^ (2⁻¹ : ℝ) := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  congr 1
  rw [ENNReal.ofReal_rpow_inv_two, show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

end Quantum

namespace Quantum.SaltedMerkle
open _root_.SaltedMerkle EmulatedOracle
universe v w
variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [AddCommGroup Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  [SampleableType Salt] (enc : Encoding X Y Msg Salt) {k : ℕ} (d : ℕ)
  {Z : Type} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- Offline extractability for the old checker, for `k` trees of a common depth `d`, with the
proved collision coefficient for all budgets; each opened leaf makes at most `d + 1` checks. -/
theorem merkle_offline_old
    (code : TpDCode k (DmOf (fun _ ↦ 2 ^ d) Msg (fun _ ↦ Td Y Salt d)) Z) :
    OfflineExtractable.{v, w} (fun _ : Fin k ↦ (scheme enc d).toVectorCommitment)
      (compressedVCOracle k X Y) (multiExtract enc (fun _ ↦ d)) code
      (fun t w e qs ↦ oldOfflineBound (Fintype.card Y) t w e (qs * (d + 1))) := by
  classical
  intro hk t qs wVC wME A W x claim ρ hx hw he
  let ME := multiExtract enc (fun _ : Fin k ↦ d)
  let E := (compressedVCOracle k X Y).withExtract ME code
  let R := E.coherent.toRuntime
  let σ := fun p : Σ B, W B ↦ R.jointPost .instruments x ρ p
  let m := fun p ↦ ENNReal.ofReal (σ p).matrix.trace.re
  let a := fun p : Σ B, W B ↦ ENNReal.ofReal (MatrixMap.conj
    ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ extractCollisionMatrix) (σ p).matrix).trace.re
  let b := fun p ↦ ENNReal.ofReal
    (4 * (qs * (d + 1) : ℕ) / (Fintype.card Y : ℝ)) * m p
  let c := fun p ↦ QuantumRuntime.potential
    (CompressedReplay.invalidStack (k := k) (X := X) (Y := Y)) (σ p).matrix
  let f := fun p ↦ ENNReal.ofReal (4 * t * oldChangingFraction (Fintype.card Y) t) * m p
  let chal := fun B y ↦ offlineChallenger (fun _ : Fin k ↦ (scheme enc d).toVectorCommitment)
    code hk qs (claim B y) B
  have hleaf : ∀ p, ((R.run₂ .instruments (chal p.1 p.2)).outcomeMeasure (σ p) {true}) ^
      (2⁻¹ : ℝ) ≤ a p ^ (2⁻¹ : ℝ) + b p ^ (2⁻¹ : ℝ) + c p ^ (2⁻¹ : ℝ) +
        f p ^ (2⁻¹ : ℝ) := by
    intro p
    apply offlineChallenger_four_amplitudes enc d code hk t qs (claim p.1 p.2) p.1 (σ p)
    have hs := databasePopulation_post_old ME code .instruments hx ρ p
    ext i j
    rw [diagonal_mul]
    by_cases hij : (σ p).matrix i j = 0
    · simp [hij]
    · have hi := (hs i j hij).1
      simp only [Set.mem_Iic] at hi
      simp [hi]
  have hh := outcomeLawWith_experiment_le_four_amplitudes R x chal ρ a b c f hleaf
  have hm : ∑' p, m p ≤ 1 := R.tsum_jointPost_trace_le_one .instruments x ρ
  have ha : ∑' p, a p ≤ ENNReal.ofReal
      ((7 * t + 5) * t / (4 * (Fintype.card Y : ℝ))) * min wVC t := by
    have hcol := collisionEvent_compressedWithExtract_le ME code .instruments x hx ρ
    refine hcol.trans ?_
    exact mul_le_mul_right (min_le_min hw le_rfl) _
  have hb : (∑' p, b p) ^ (2⁻¹ : ℝ) ≤
      2 * ((qs * (d + 1) : ℕ) / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) := by
    refine (ENNReal.rpow_le_rpow (tsum_weighted_trace_le m hm _) (by norm_num)).trans_eq ?_
    rw [show (4 * (qs * (d + 1) : ℕ) / (Fintype.card Y : ℝ)) =
      4 * ((qs * (d + 1) : ℕ) / (Fintype.card Y : ℝ)) by ring,
      ofReal_four_mul_rpow, ENNReal.ofReal_div_of_pos (by positivity)]
    simp only [ENNReal.ofReal_natCast]
  have hc : (∑' p, c p) ^ (2⁻¹ : ℝ) ≤
      2 * (ENNReal.ofReal (oldLeakagePolynomial t) / Fintype.card Y * wME) ^ (2⁻¹ : ℝ) := by
    have hinv := old_run_invalid_le enc (fun _ ↦ d) code .instruments x ρ t hx
    exact hinv.trans (mul_le_mul_right
      (ENNReal.rpow_le_rpow (mul_le_mul_right he _) (by norm_num)) 2)
  have hf : (∑' p, f p) ^ (2⁻¹ : ℝ) ≤
      2 * ENNReal.ofReal (t * oldChangingFraction (Fintype.card Y) t) ^ (2⁻¹ : ℝ) := by
    refine (ENNReal.rpow_le_rpow (tsum_weighted_trace_le m hm _) (by norm_num)).trans_eq ?_
    rw [mul_assoc, ofReal_four_mul_rpow]
  apply le_min (R.outcomeLawWith_le_one .instruments (experiment x chal) ρ Sigma.snd {true})
  refine hh.trans (ENNReal.rpow_le_rpow ?_ (by norm_num : (0 : ℝ) ≤ 2))
  exact add_le_add (add_le_add (add_le_add
    (ENNReal.rpow_le_rpow ha (by norm_num)) hb) hc) hf

/-- For total query budgets at least four, the old offline theorem implies the repair
note's FIX (35) error. No FIX coefficient comparison is asserted for smaller budgets. -/
theorem merkle_offline_old_fix
    (code : TpDCode k (DmOf (fun _ ↦ 2 ^ d) Msg (fun _ ↦ Td Y Salt d)) Z)
    (hk : 1 ≤ k) (t qs : ℕ) (ht : 4 ≤ t) (wVC wME : ℝ≥0∞)
    {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec (extIn k X Y Y Z)) W A)
    (claim : ∀ B, W B → OpeningClaim k Y Msg (fun _ ↦ 2 ^ d) (fun _ ↦ Pf Y Salt d))
    (ρ : SubState A) (hx : x.IsQueryBound fun _ ↦ t)
    (hw : ∑ i : Fin k, ((compressedVCOracle k X Y).withExtract
      (multiExtract enc (fun _ ↦ d)) code).totalMass .instruments x
        (ρ.matrix ⊗ₖ (compressedVCOracle k X Y).init.matrix) (.inl i) ≤ wVC)
    (he : ((compressedVCOracle k X Y).withExtract (multiExtract enc (fun _ ↦ d)) code).totalMass
      .instruments x (ρ.matrix ⊗ₖ (compressedVCOracle k X Y).init.matrix)
        (.inr ()) ≤ wME) :
    ((compressedVCOracle k X Y).withExtract
      (multiExtract enc (fun _ ↦ d)) code).coherent.toRuntime.outcomeLawWith
      .instruments
        (experiment x fun B y ↦ offlineChallenger
          (fun _ : Fin k ↦ (scheme enc d).toVectorCommitment) code hk qs (claim B y) B)
        ρ Sigma.snd {true} ≤ oldOfflineFixBound (Fintype.card Y) t wVC wME (qs * (d + 1)) :=
  (merkle_offline_old enc d code hk t qs wVC wME x claim ρ hx hw he).trans
    (oldOfflineBound_le_fix (by positivity) ht wVC wME (qs * (d + 1)))

end Quantum.SaltedMerkle
