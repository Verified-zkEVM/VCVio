/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Merkle.OfflineOld
import all VCVio.Quantum.VC.Proof.CheckerComparison

/-!
# Outcome-preserving old-oracle comparison and amplitude aggregation

The ideal partial-database mismatch branch vanishes on good databases, including the
randomized opening/decision instrument. The leaf aggregation retains all four amplitudes
in extended nonnegative reals before squaring. The error comparison with FIX (35) holds
only for total budgets at least four. The concrete checker and runtime estimates assemble
these amplitudes in `Quantum.SaltedMerkle.merkle_offline_old`.
-/

public section

open Matrix OracleComp
open scoped Kronecker
namespace Quantum
variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  [∀ i, DecidableEq (DmOf ℓ Msg Td i)]
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (io : ∀ i, (VC i).CheckIOForm)
  (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (Fin k → Database X Y))
  (tdBot : ∀ i, Td i) (Pgood : Set (Database X Y)) [DecidablePred (· ∈ Pgood)]

open scoped Classical in
/-- The accepted partial-database comparison map has no mismatch branch on good databases.
The extraction outcome and every possible randomized opening outcome remain fixed. -/
theorem partialAccepted_mismatch_good_zero (hC : Conditions VC io ME tdBot Pgood)
    (hk : 1 ≤ k) (c : OpeningClaim k Cm Msg ℓ Pf)
    (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) (pf' : ∀ i, Pf i)
    (hpf : ∀ i, pf' i ∈ support ((VC i).opening (c.ans i).dom (tdm i).2)) :
    (if Function.Injective c.idx ∧
        (∃ i, ¬ PartialVec.Agrees (tdm i).1 (c.ans i) ∨ pf' i ≠ c.pf i) then
      checkPassProjector io c.Wᶜ c.idx c.cm c.ans c.pf *
        extractProj ME (TpIC.full hk c.idx c.cm) tdm *
          checkPassProjector io c.W c.idx c.cm c.ans c.pf else 0) *
      diagonal (fun D : Fin k → Database X Y ↦ if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0) = 0 := by
  classical
  split_ifs with hm
  · simp only [checkPassProjector, extractProj, diagonal_mul_diagonal]
    rw [← diagonal_zero]
    congr 1
    funext D
    split_ifs with hb he ha hg <;> simp only [zero_mul, mul_zero, one_mul]
    have hall : ∀ i, (io i).checkOn (D (c.idx i))
        (c.cm i) (c.ans i) (c.pf i) = true := by
      intro i
      by_cases hi : i ∈ c.W
      · exact ha i hi
      · exact hb i (Finset.mem_compl.mpr hi)
    have hbind := hC.binding hk c.idx hm.1 c.cm c.ans c.pf D hg hall
    rw [he] at hbind
    obtain ⟨i, hi | hi⟩ := hm.2
    · exact (hi (hbind i).1).elim
    · exact (hi ((hbind i).2 _ (hpf i))).elim
  · simp

variable [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z]
  [AddGroup Z] [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
/-- The actual opening/decision instrument has zero mismatch branch after the ideal
partial-database accepted map on good databases. Randomized openings are included. -/
theorem run₂_offlineFinish_partial_good_zero (hC : Conditions VC io ME tdBot Pgood)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) :
    let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
    let K := checkPassProjector io c.Wᶜ c.idx c.cm c.ans c.pf *
      extractProj ME (TpIC.full hk c.idx c.cm) tdm *
        checkPassProjector io c.W c.idx c.cm c.ans c.pf *
          diagonal (fun D : Fin k → Database X Y ↦ if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0)
    (R.run₂ .instruments (offlineFinish (VC := VC) (Z := Z) hk qs c B
      (true, some tdm, true))).branch true ∘ₗ
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ K) = 0 := by
  classical
  let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
  dsimp only
  ext ρ : 1
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [offlineFinish, QuantumRuntime.run₂_bind, SubInstrument.branch_bind_apply]
  refine (tsum_congr fun pf' ↦ ?_).trans tsum_zero
  obtain ⟨c₀, hc₀, hz⟩ := exists_branch_run₂_pi_eq_smul R
    (fun i ↦ openAt VC B i (c.ans i).dom (tdm i).2)
    (fun i ↦ support ((VC i).opening (c.ans i).dom (tdm i).2))
    (fun i b ↦ exists_branch_run₂_toQuantumAt_coinImpl_eq_smul _ _ b) pf'
  rw [hc₀, LinearMap.smul_apply, LinearMap.id_apply, QuantumRuntime.run₂_pure]
  by_cases hs : ∃ i, pf' i ∉ support ((VC i).opening (c.ans i).dom (tdm i).2)
  · rw [hz hs, zero_smul, map_zero]
  · by_cases he : (true && true &&
        decide (∃ i : Fin k, ¬ PartialVec.Agrees (tdm i).1 (c.ans i) ∨ pf' i ≠ c.pf i) &&
        decide (∑ i, (c.ans i).dom.card ≤ qs) && decide (Function.Injective c.idx)) = true
    · rw [he, SubInstrument.branch_pure_self, LinearMap.id_apply]
      simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at he
      have hh := partialAccepted_mismatch_good_zero io ME tdBot Pgood hC hk c tdm pf'
        (fun i ↦ by by_contra hh; exact hs ⟨i, hh⟩)
      rw [ite_eq_left ⟨he.2, he.1.1⟩] at hh
      rw [hh]
      erw [Matrix.kronecker_zero, MatrixMap.conj_zero, LinearMap.zero_apply, smul_zero]
    · rw [SubInstrument.branch_pure_of_ne (Ne.symm he), LinearMap.zero_apply]
end Quantum

open MeasureTheory
open scoped ENNReal
namespace Quantum
/-- Four square-root error terms sum across arbitrary leaf types before squaring. -/
theorem tsum_le_sq_of_four_amplitudes {L : Type*} (t a b c d : L → ℝ≥0∞)
    (h : ∀ l, t l ^ (2⁻¹ : ℝ) ≤ a l ^ (2⁻¹ : ℝ) + b l ^ (2⁻¹ : ℝ) +
      c l ^ (2⁻¹ : ℝ) + d l ^ (2⁻¹ : ℝ)) :
    ∑' l, t l ≤ ((∑' l, a l) ^ (2⁻¹ : ℝ) + (∑' l, b l) ^ (2⁻¹ : ℝ) +
      (∑' l, c l) ^ (2⁻¹ : ℝ) + (∑' l, d l) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) := by
  have hs (x : ℝ≥0∞) : (x ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) = x := by
    rw [← ENNReal.rpow_mul]
    norm_num
  let ab := fun l ↦ (a l ^ (2⁻¹ : ℝ) + b l ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)
  let cd := fun l ↦ (c l ^ (2⁻¹ : ℝ) + d l ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)
  have h₁ := rpow_inv_two_tsum_le_of_le_add (t := ab) (a := a) (b := b)
    (fun l ↦ (hs _).le)
  have h₂ := rpow_inv_two_tsum_le_of_le_add (t := cd) (a := c) (b := d)
    (fun l ↦ (hs _).le)
  have h₃ := rpow_inv_two_tsum_le_of_le_add (t := t) (a := ab) (b := cd)
    (fun l ↦ by simpa only [ab, cd, hs, add_assoc] using h l)
  apply (ENNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 2)).mp
  exact h₃.trans (by simpa only [add_assoc] using add_le_add h₁ h₂)
end Quantum
namespace Quantum
universe u₁ v₁ v w
/-- A challenger experiment is the sum over the actual dependent post-adversary substates. -/
theorem outcomeLawWith_experiment_true_eq_tsum {spec : QuantumOracleSpec.{u₁, v₁}} {A : QReg}
    {W : QReg → Type w} (R : QuantumRuntime spec)
    (x : QuantumComp LocalSig.instruments.{v} spec W A)
    (chal : ∀ u, W u → QComp.{u₁, v₁, 0} spec u u Bool) (ρ : SubState A) :
    R.outcomeLawWith .instruments (experiment x chal) ρ Sigma.snd {true} =
      ∑' p : Σ u, W u, (R.run₂ .instruments (chal p.1 p.2)).outcomeMeasure
        (R.jointPost .instruments x ρ p) {true} := by
  let _ : MeasurableSpace (Σ _ : QReg, Bool) := ⊤
  let _ : MeasurableSpace (Σ u, W u) := ⊤
  have hS : MeasurableSet (Sigma.snd ⁻¹' {true} : Set (Σ _ : QReg, Bool)) :=
    MeasurableSpace.measurableSet_top
  have h₁ : R.outcomeLawWith .instruments (experiment x chal) ρ Sigma.snd {true} =
      (R.run .instruments (experiment x chal)).outcomeMeasure (ρ.prod R.init)
        (Sigma.snd ⁻¹' {true}) := by
    rw [QuantumRuntime.outcomeLawWith_apply _ _ _ _ _ (measurableSet_singleton true),
      DSubInstrument.outcomeMeasure_apply _ _ hS]
    rfl
  rw [h₁, run_experiment, DSubInstrument.outcomeMeasure_bind, Measure.sum_apply _ hS]
  simp only [QuantumRuntime.outcomeMeasure_run_forgetReg R _ _ _ (measurableSet_singleton true)
    hS]
  rfl

/-- Four proved leafwise amplitude bounds aggregate over adaptive, register-changing leaves.
The arithmetic stays in extended nonnegative reals and retains every cross term. -/
theorem outcomeLawWith_experiment_le_four_amplitudes
    {spec : QuantumOracleSpec.{u₁, v₁}} {A : QReg} {W : QReg → Type w}
    (R : QuantumRuntime spec) (x : QuantumComp LocalSig.instruments.{v} spec W A)
    (chal : ∀ u, W u → QComp.{u₁, v₁, 0} spec u u Bool) (ρ : SubState A)
    (a b c d : (Σ u, W u) → ℝ≥0∞)
    (h : ∀ p, ((R.run₂ .instruments (chal p.1 p.2)).outcomeMeasure
      (R.jointPost .instruments x ρ p) {true}) ^ (2⁻¹ : ℝ) ≤
        a p ^ (2⁻¹ : ℝ) + b p ^ (2⁻¹ : ℝ) + c p ^ (2⁻¹ : ℝ) + d p ^ (2⁻¹ : ℝ)) :
    R.outcomeLawWith .instruments (experiment x chal) ρ Sigma.snd {true} ≤
      ((∑' p, a p) ^ (2⁻¹ : ℝ) + (∑' p, b p) ^ (2⁻¹ : ℝ) +
        (∑' p, c p) ^ (2⁻¹ : ℝ) + (∑' p, d p) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) := by
  rw [outcomeLawWith_experiment_true_eq_tsum]
  exact tsum_le_sq_of_four_amplitudes _ a b c d h
end Quantum

open scoped ENNReal
namespace Quantum.SaltedMerkle
/-- Four-term old-oracle error with the proved collision coefficient and extended query masses. -/
@[expose]
noncomputable def oldOfflineBound (N u : ℕ) (w e : ℝ≥0∞) (q : ℕ) : ℝ≥0∞ :=
  min 1 (((ENNReal.ofReal ((7 * u + 5) * u / (4 * (N : ℝ))) * min w u) ^ (2⁻¹ : ℝ) +
    2 * ((q : ℝ≥0∞) / N) ^ (2⁻¹ : ℝ) +
    2 * (ENNReal.ofReal (oldLeakagePolynomial u) / N * e) ^ (2⁻¹ : ℝ) +
    2 * ENNReal.ofReal (u * oldChangingFraction N u) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ))

/-- The FIX (35) error in extended nonnegative reals, with all cross terms retained. -/
@[expose]
noncomputable def oldOfflineFixBound (N u : ℕ) (w e : ℝ≥0∞) (q : ℕ) : ℝ≥0∞ :=
  min 1 (((ENNReal.ofReal (3 * u * (u - 1 : ℕ) / (N : ℝ)) * w) ^ (2⁻¹ : ℝ) +
    2 * ((q : ℝ≥0∞) / N) ^ (2⁻¹ : ℝ) +
    2 * (ENNReal.ofReal (oldLeakagePolynomial u) / N * e) ^ (2⁻¹ : ℝ) +
    2 * ENNReal.ofReal (u * oldChangingFraction N u) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ))

/-- The proved collision coefficient implies the FIX coefficient for budgets at least four,
including infinite ordinary or extraction mass allowances. -/
theorem oldOfflineBound_le_fix {N u : ℕ} (hN : 0 < N) (hu : 4 ≤ u)
    (w e : ℝ≥0∞) (q : ℕ) : oldOfflineBound N u w e q ≤ oldOfflineFixBound N u w e q := by
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
  have hc := collisionCoefficient_le_fix hu (N := (N : ℝ)) (w := 1)
    (by exact_mod_cast hN) (by norm_num)
  rw [min_eq_left hu', mul_one] at hc
  norm_num only [mul_one] at hc
  have hh : ENNReal.ofReal ((7 * u + 5) * u / (4 * (N : ℝ))) * min w u ≤
      ENNReal.ofReal (3 * u * (u - 1 : ℕ) / (N : ℝ)) * w :=
    mul_le_mul (ENNReal.ofReal_le_ofReal hc) (min_le_left _ _) (by positivity) (by positivity)
  unfold oldOfflineBound oldOfflineFixBound
  gcongr

/-- Zero total calls and zero checks have zero error, without finite-mass assumptions. -/
@[simp] theorem oldOfflineBound_zero (N : ℕ) (w e : ℝ≥0∞) :
    oldOfflineBound N 0 w e 0 = 0 := by
  simp [oldOfflineBound, oldChangingFraction, oldLeakagePolynomial]
end Quantum.SaltedMerkle
