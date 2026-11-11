/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.CheckerComparison
public import VCVio.Quantum.VC.Proof.GoodEvent

/-!
# Offline extractability with checked reads

The mismatch amplitude is bounded by the original bad-database amplitude plus the two
checked-batch distances, retaining measured extraction outcomes and opening coins.
-/

public section

open Matrix MeasureTheory OracleSpec
open scoped ENNReal Kronecker Matrix.Norms.L2Operator
namespace Quantum

variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z]
  [DecidableEq Z] [AddGroup Z] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (chk : ∀ i, (VC i).NonadaptiveCheck)
  (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (Fin k → Database X Y))
  (tdBot : ∀ i, Td i) (Pgood : Set (Database X Y)) [DecidablePred (· ∈ Pgood)]

/-- The checked challenger's amplitude is bounded on every joint substate. Its extraction
response is initialized afresh, and the trace factor is retained for adaptive leaf sums. -/
theorem offlineChallenger_amplitude_le (hC : Conditions VC chk ME tdBot Pgood)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (ρ : SubState (B × (Fin k → Database X Y))) :
    let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
    ((R.run₂ .instruments (offlineChallenger VC code hk qs c B)).outcomeMeasure ρ {true}) ^
        (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        familyBadProjector (k := k) Pgood) ρ.matrix).trace.re ^ (2⁻¹ : ℝ) +
      (4 * ((q1 chk qs : ℝ≥0∞) / Fintype.card Y) *
        ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) := by
  classical
  let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
  dsimp only
  by_cases hq : ∑ i, (c.ans i).dom.card ≤ qs
  · have hlift : R.run₂ .instruments
        (QuantumComp.liftOrdinary (extractQuery code B (TpIC.full hk c.idx c.cm))) =
        ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.run₂ .instruments
          (extractQuery code B (TpIC.full hk c.idx c.cm)) := by
      unfold R QuantumRuntime.run₂ VCOracle.mixedExtractRuntime
      erw [QuantumRuntime.run_liftOrdinary]
      rfl
    have hext (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) :
        (((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.run₂ .instruments
          (extractQuery code B (TpIC.full hk c.idx c.cm))).branch (some tdm) =
          MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
            extractProj ME (TpIC.full hk c.idx c.cm) tdm) :=
      run₂_extractQuery_branch (compressedVCOracle k X Y) ME code B (TpIC.full hk c.idx c.cm) tdm
    have heq (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) :
        (R.run₂ .instruments (offlineChecks VC code hk c B)).branch (true, some tdm, true) =
          MatrixMap.conj (((1 : Matrix B B ℂ) ⊗ₖ filledBatch chk c.Wᶜ c) *
            ((1 : Matrix B B ℂ) ⊗ₖ (show Matrix (Fin k → Database X Y) _ ℂ from
              extractProj ME (TpIC.full hk c.idx c.cm) tdm)) *
            ((1 : Matrix B B ℂ) ⊗ₖ filledBatch chk c.W c)) := by
      rw [run₂_offlineChecks]
      erw [branch_run₂_filledBatch_compressedVCOracle chk ME code,
        branch_run₂_filledBatch_compressedVCOracle chk ME code, hlift, hext]
      exact (MatrixMap.conj_mul _ _ |>.trans
        (congrArg
          (fun F ↦ F ∘ₗ MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ filledBatch chk c.W c))
          (MatrixMap.conj_mul _ _))).symm
    have hb := offlineFinish_le_bad_add_distance chk ME tdBot Pgood hC code hk qs c B
      ρ.posSemidef
    rw [offlineChallenger_weight_eq_retained VC code R hk qs c B ρ]
    simp only [run₂_offlineInstrument, heq]
    dsimp only at hb
    rw [familyBadProjector_eq_one_sub]
    refine hb.trans ?_
    let Δ := fun W ↦ ‖(1 : Matrix B B ℂ) ⊗ₖ filledBatch chk W c -
      (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector chk W c.idx c.cm c.ans c.pf‖
    have hd : Δ c.W + Δ c.Wᶜ ≤
        2 * Real.sqrt ((q1 chk qs : ℝ) / Fintype.card Y) :=
      (two_batch_reference_distance_le chk c B).trans (by
        gcongr
        exact_mod_cast length_two_batches_le chk qs c hq)
    have hs (W) :
        (ENNReal.ofReal (Δ W ^ 2) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) =
        ENNReal.ofReal (Δ W) * ENNReal.ofReal ρ.matrix.trace.re ^ (2⁻¹ : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.ofReal_rpow_inv_two, Real.sqrt_sq (norm_nonneg _)]
    change _ + (ENNReal.ofReal (Δ c.W ^ 2) * _) ^ (2⁻¹ : ℝ) +
      (ENNReal.ofReal (Δ c.Wᶜ ^ 2) * _) ^ (2⁻¹ : ℝ) ≤ _
    rw [add_assoc, hs, hs, ← add_mul, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    refine add_le_add ?_ ?_
    · exact le_of_eq (by simp [familyGoodProjector, labelProjector])
    · refine (mul_le_mul_left (ENNReal.ofReal_le_ofReal hd) _).trans_eq ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      congr 1
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ← ENNReal.ofReal_natCast (n := q1 chk qs),
        ← ENNReal.ofReal_natCast (n := Fintype.card Y),
        ← ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_rpow_inv_two,
        ENNReal.ofReal_mul (by norm_num)]
      congr 1
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (2 ^ 2 : ℝ) by norm_num,
        ENNReal.ofReal_rpow_inv_two, Real.sqrt_sq (by norm_num)]
  · rw [offlineChallenger_over_budget VC code R hk qs c B ρ hq]
    simp


/-- The capped bad-database bound for an ordinary/extraction prefix. -/
@[expose]
noncomputable def offlineBadError [UniformAnswerMeasure (X →ₒ Y)]
    (Pgood : Set (Database X Y)) [DecidablePred (· ∈ Pgood)]
    (t : ℕ) (w : ℝ≥0∞) : ℝ≥0∞ :=
  min 1 (24 * (t : ℝ≥0∞) * min w (t : ℝ≥0∞) *
    Database.instability (offlineLabel Pgood) t)

/-- The offline error adds the bad-database and checker amplitudes before squaring. -/
@[expose]
noncomputable def offlineError [UniformAnswerMeasure (X →ₒ Y)]
    (t : ℕ) (w : ℝ≥0∞) (qs : ℕ) : ℝ≥0∞ :=
  min 1 ((offlineBadError Pgood t w ^ (2⁻¹ : ℝ) +
    2 * ((q1 chk qs : ℝ≥0∞) / Fintype.card Y) ^ (2⁻¹ : ℝ)) ^ 2)

universe v w

/-- Any proved bound on the original post-adversary bad event gives offline extractability.
The event hypothesis concerns the same ordinary/extraction execution as the security game. -/
theorem offlineExtractable_compressedVCOracle_of_badEvent
    (hC : Conditions VC chk ME tdBot Pgood) (code : TpDCode k (DmOf ℓ Msg Td) Z)
    (bound : ℕ → ℝ≥0∞ → ℝ≥0∞)
    (hbad : ∀ (t : ℕ) (w : ℝ≥0∞) {A : QReg} {W : QReg → Type w}
      (x : QuantumComp LocalSig.instruments.{v} (EmulatedOracle.cohSpec (extIn k X Y Cm Z)) W A)
      (ρ : SubState A), x.IsQueryBound (fun _ ↦ t) →
      (∑ i : Fin k, ((compressedVCOracle k X Y).withExtract ME code).totalMass .instruments x
        (ρ.matrix ⊗ₖ (compressedVCOracle k X Y).init.matrix) (.inl i)) ≤ w →
      ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.eventWeight
        .instruments (familyBadProjector (k := k) Pgood) x
        (ρ.matrix ⊗ₖ (compressedVCOracle k X Y).init.matrix) ≤ bound t w) :
    OfflineExtractable.{v, w} VC (compressedVCOracle k X Y) ME code
      (fun t wVC _ qs ↦ min 1 ((bound t wVC ^ (2⁻¹ : ℝ) +
        2 * ((q1 chk qs : ℝ≥0∞) / Fintype.card Y) ^ (2⁻¹ : ℝ)) ^ 2)) := by
  classical
  intro hk t qs wVC wME A W x claim ρ hx hw _
  let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
  let σ := fun p : Σ B, W B ↦ R.jointPost .instruments x.liftOrdinary ρ p
  let a := fun p : Σ B, W B ↦ ENNReal.ofReal (MatrixMap.conj
    ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ familyBadProjector (k := k) Pgood) (σ p).matrix).trace.re
  let b := fun p ↦ 4 * ((q1 chk qs : ℝ≥0∞) / Fintype.card Y) *
    ENNReal.ofReal (σ p).matrix.trace.re
  let chal := fun B y ↦ offlineChallenger VC code hk qs (claim B y) B
  have hh := rpow_inv_two_tsum_le_of_le_add
    (t := fun p : Σ B, W B ↦ (R.run₂ .instruments (chal p.1 p.2)).outcomeMeasure (σ p) {true})
    (a := a) (b := b) (fun p ↦
      offlineChallenger_amplitude_le chk ME tdBot Pgood hC code hk qs (claim p.1 p.2) p.1 (σ p))
  have hrun : R.run .instruments x.liftOrdinary =
      ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.run .instruments x := by
    unfold R VCOracle.mixedExtractRuntime
    erw [QuantumRuntime.run_liftOrdinary]
  have hinit : R.init = (compressedVCOracle k X Y).init := by
    simp only [R, VCOracle.mixedExtractRuntime, EmulatedOracle.coherent]
    rfl
  have ha : ∑' p, a p ≤ bound t wVC := by
    have h := hbad t wVC x ρ hx hw
    simp only [a, σ, QuantumRuntime.matrix_jointPost, hrun, hinit]
    unfold QuantumRuntime.eventWeight at h
    convert h using 1
    rfl
  have hb : ∑' p, b p ≤ 4 * ((q1 chk qs : ℝ≥0∞) / Fintype.card Y) :=
    tsum_weighted_trace_le _ (R.tsum_jointPost_trace_le_one .instruments x.liftOrdinary ρ) _
  have hr : (4 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 2 := by
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (2 ^ 2 : ℝ) by norm_num,
      ENNReal.ofReal_rpow_inv_two, Real.sqrt_sq (by norm_num)]
    norm_num
  apply le_min (R.outcomeLawWith_le_one .instruments (experiment x.liftOrdinary chal)
    ρ Sigma.snd {true})
  rw [evalDistMap_experiment_true_eq_tsum, ← ENNReal.rpow_natCast]
  apply (ENNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 2)).mp
  refine hh.trans (add_le_add (ENNReal.rpow_le_rpow ha (by norm_num)) ?_)
  exact (ENNReal.rpow_le_rpow hb (by norm_num)).trans_eq (by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hr])

/-- Offline extractability for checked challenger reads and arbitrary ordinary/extraction
adversaries, under the three vector-commitment conditions. -/
theorem offlineExtractable_compressedVCOracle [UniformAnswerMeasure (X →ₒ Y)]
    (hC : Conditions VC chk ME tdBot Pgood) (code : TpDCode k (DmOf ℓ Msg Td) Z) :
    OfflineExtractable.{v, w} VC (compressedVCOracle k X Y) ME code
      (fun t wVC _ qs ↦ offlineError chk Pgood t wVC qs) := by
  classical
  unfold offlineError
  apply offlineExtractable_compressedVCOracle_of_badEvent chk ME tdBot Pgood hC code
    (offlineBadError Pgood)
  intro t w A W x ρ hx hw
  apply le_min
  · let E := (compressedVCOracle k X Y).withExtract ME code
    have hQ := isStarProjection_familyBadProjector (k := k) Pgood
    exact (QuantumRuntime.eventWeight_le_trace .instruments E.coherent.toRuntime
      hQ.isSelfAdjoint hQ.isIdempotentElem x (ρ.prod E.init).posSemidef).trans
        (ENNReal.ofReal_le_one.mpr (ρ.prod E.init).trace_re_le_one)
  · exact (badEvent_compressedWithExtract_le ME code Pgood hC.empty_mem
      .instruments x hx ρ).trans (by
        gcongr
        convert hw using 1
        rfl)

end Quantum
