/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.HadamardExecution

/-!
# Extraction correctness for empty-sector extensions

The actual accepting effect dominates the filled-only consistency projector conjugated by
compression. The overlap calculation of `Quantum.exists_le_checkPassProjector_conj` therefore
gives P3 with error `1 - (1 - 1/N)^(2 n q₂)`, as in the repair note §4. This improves the paper's
`8 n q₂ / N` bound and is at most `2 n q₂ / N`.

This argument needs only unitarity of the empty-sector response. It needs neither a flat zero
column nor an exponent-two answer group: the lower accepting-effect bound holds for arbitrary
empty-sector amplitudes. Those additional hypotheses belong to other properties of the witness.
-/

public section

open Matrix OracleSpec OracleComp MeasureTheory
open scoped Kronecker ENNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe v w

namespace Quantum

section trace

variable {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
/-- Ordering accepting effects orders their trace weights on every positive joint state. -/
theorem trace_re_conj_one_kronecker_mono_effect {K L : Matrix S S ℂ}
    (hKL : Kᴴ * K ≤ Lᴴ * L) {φ : Matrix (B × S) (B × S) ℂ} (hφ : φ.PosSemidef) :
    (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ K) φ).trace.re ≤
      (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ L) φ).trace.re := by
  have ht (M : Matrix S S ℂ) :
      (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ M) φ).trace =
        (((1 : Matrix B B ℂ) ⊗ₖ (Mᴴ * M)) * φ).trace := by
    rw [MatrixMap.conj_apply, Matrix.trace_mul_cycle, conjTranspose_kronecker,
      conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  have hp := (Matrix.PosSemidef.one (n := B) (R := ℂ)).kronecker
    (sub_nonneg.mpr hKL).posSemidef
  have h := hp.trace_mul_re_nonneg hφ
  have hs : (1 : Matrix B B ℂ) ⊗ₖ (Lᴴ * L - Kᴴ * K) =
      (1 : Matrix B B ℂ) ⊗ₖ (Lᴴ * L) - (1 : Matrix B B ℂ) ⊗ₖ (Kᴴ * K) := by
    ext i j
    simp only [kroneckerMap_apply, Matrix.sub_apply, mul_sub]
  rw [hs, Matrix.sub_mul, trace_sub, Complex.sub_re] at h
  rw [ht K, ht L]
  linarith

/-- A compressed filled-only projector is an orthogonal projection. -/
theorem conj_diagonal_projector_effect {C : Matrix S S ℂ} (hC : Cᴴ = C) (hCC : C * C = 1)
    (p : S → Prop) [DecidablePred p] :
    (C * diagonal (fun d ↦ if p d then (1 : ℂ) else 0) * C)ᴴ *
        (C * diagonal (fun d ↦ if p d then (1 : ℂ) else 0) * C) =
      C * diagonal (fun d ↦ if p d then (1 : ℂ) else 0) * C := by
  rw [conjTranspose_mul, conjTranspose_mul, hC, conjTranspose_diagonal_ite]
  rw [← Matrix.mul_assoc C, conj_diagonal_mul_conj_diagonal hCC]
  congr 3
  funext d
  split_ifs <;> simp

/-- The P3 overlap bound remains valid for an actual diagonal accepting amplitude that is
one on the filled-only pass event. The amplitude need not be projective. -/
theorem trace_re_conj_amplitude_ge_of_conj {C Q : Matrix S S ℂ}
    (hC : Cᴴ = C) (hCC : C * C = 1) (p : S → Prop) [DecidablePred p]
    (f : S → ℂ) (hf : ∀ d, p d → f d = 1) {a : ℝ}
    (ha : diagonal (fun d ↦ if p d then (1 : ℂ) else 0) *
      (C * diagonal (fun d ↦ if p d then (1 : ℂ) else 0) * C) *
      diagonal (fun d ↦ if p d then (1 : ℂ) else 0) =
        (a : ℂ) • diagonal (fun d ↦ if p d then (1 : ℂ) else 0))
    (hPQ : diagonal (fun d ↦ if p d then (1 : ℂ) else 0) * Q = Q)
    {φ : Matrix (B × S) (B × S) ℂ} (hφ : φ.PosSemidef)
    (hφQ : MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ Q) φ = φ) :
    a * φ.trace.re ≤
      (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (C * diagonal f * C)) φ).trace.re := by
  have h := trace_re_conj_one_kronecker_ge_of_conj hC hCC
    (conjTranspose_diagonal_ite p) (diagonal_ite_mul_self p)
    (conjTranspose_diagonal_ite p) (diagonal_ite_mul_self p) (diagonal_ite_mul_self p)
    ha hPQ hφ hφQ
  refine h.trans (trace_re_conj_one_kronecker_mono_effect ?_ hφ)
  rw [conj_diagonal_projector_effect hC hCC]
  exact conjugated_accept_effect_ge hC hCC f p hf

end trace

section challenger

variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)} (io : ∀ i, (VC i).CheckIOForm)
  (U : Matrix Y Y ℂ) (hU : U ∈ unitaryGroup Y ℂ)
  (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (Fin k → Database X Y))
  (code : TpDCode k (DmOf ℓ Msg Td) Z) {tdBot : ∀ i, Td i} {Pgood : Set (Database X Y)}

/-- The actual post-extraction checks reject with at most the exact overlap error on
states supported on their measured extraction outcome. -/
theorem outcomeMeasure_run₂_checks_le_extended [∀ i, DecidableEq (DmOf ℓ Msg Td i)]
    (hC : Conditions VC io ME tdBot Pgood) (hk : 1 ≤ k) (n : ℕ) (c : ExtractClaim k Cm)
    {B : QReg} (tdm : TpDLen k (DmOf ℓ Msg Td) (TpIC.full hk c.idx c.cm).1) (pf : ∀ i, Pf i)
    (hpf : ∀ i, pf i ∈ support ((VC i).opening (tdm i).1.dom (tdm i).2))
    (ρ : SubState (B × ((extendedVCOracle k X Y U hU).withExtract ME code).coherent.toRuntime.D))
    (hρ : MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ diagonal fun D : Fin k → Database X Y ↦
      if ME.extract (TpIC.full hk c.idx c.cm) D = tdm then 1 else 0) ρ.matrix = ρ.matrix) :
    (((extendedVCOracle k X Y U hU).withExtract ME code).coherent.toRuntime.run₂ .instruments
        ((QComp.allIn c.W fun i ↦ checkAt (Z := Z) VC B i (c.idx i) (c.cm i) (tdm i).1
          (pf i)).bind fun b ↦ QuantumComp₂.pure
            (!b && decide (c.W.card ≤ n) && decide (Function.Injective c.idx)))).outcomeMeasure
        ρ {true} ≤
      ENNReal.ofReal (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q2 io)) *
        ENNReal.ofReal ρ.matrix.trace.re := by
  rw [QuantumRuntime.run₂_bind, SubInstrument.outcomeMeasure_apply_singleton,
    SubInstrument.branch_bind_apply_univ, Fintype.sum_bool]
  simp only [QuantumRuntime.run₂_pure, Bool.not_true, Bool.false_and, Bool.not_false,
    Bool.true_and]
  rw [SubInstrument.branch_pure_of_ne (by decide : true ≠ false), LinearMap.zero_comp, zero_add]
  by_cases hcond : c.W.card ≤ n ∧ Function.Injective c.idx
  · obtain ⟨hW, hinj⟩ := hcond
    simp only [hW, hinj, decide_true, Bool.and_self, SubInstrument.branch_pure_self,
      LinearMap.id_comp]
    have hN : (0 : ℝ) ≤ 1 - (Fintype.card Y : ℝ)⁻¹ :=
      sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos))
    have hN1 : 1 - (Fintype.card Y : ℝ)⁻¹ ≤ 1 :=
      sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    have hCC := compressDatabases_mul_self (k := k) (X := X) (Y := Y)
    have hloss := QuantumRuntime.lossless_run₂
      ((extendedVCOracle k X Y U hU).withExtract ME code).coherent.toRuntime .instruments
      (QComp.lossless_allIn (W := c.W) (B := B) (f := fun i ↦ checkAt (Z := Z) VC B i (c.idx i)
        (c.cm i) (tdm i).1 (pf i)) fun i _ ↦ lossless_checkAt _ _ _ _ _ _)
      (EmulatedOracle.lossless_toRuntime_step _)
    have hsum := SubInstrument.trace_re_branch_add_of_lossless hloss ρ.matrix
    obtain ⟨a, ha0, ha⟩ := exists_le_checkPassProjector_conj io n c.W hW c.idx c.cm
      (fun i ↦ (tdm i).1) pf
    -- the checks on the partial tables pass under the extraction outcome (condition 3)
    have hPQ : checkPassProjector io c.W c.idx c.cm (fun i ↦ (tdm i).1) pf *
        (diagonal fun D : Fin k → Database X Y ↦
          if ME.extract (TpIC.full hk c.idx c.cm) D = tdm then 1 else 0) =
        diagonal fun D : Fin k → Database X Y ↦
          if ME.extract (TpIC.full hk c.idx c.cm) D = tdm then 1 else 0 := by
      rw [checkPassProjector, diagonal_ite_mul_diagonal_ite]
      congr 1
      funext D
      by_cases hD : ME.extract (TpIC.full hk c.idx c.cm) D = tdm
      · have hD' : @MultiExtractor.extract _ _ _ (Fin k → Database X Y) ME
            (TpIC.full hk c.idx c.cm) D = tdm := hD
        refine (ite_eq_left_iff.mpr fun h ↦ absurd ⟨fun i _ ↦ ?_, hD⟩ h).trans
          (ite_eq_left_iff.mpr fun h ↦ absurd hD h).symm
        have hv := hC.valid hk c.idx hinj c.cm D i
        rw [hD'] at hv
        exact hv (pf i) (hpf i)
      · simp [hD]
    let g : Fin k → (Fin k → Database X Y) → ℂ := fun i D ↦
      checkAcceptWeight io (fun z ↦ U z 0) i (c.cm i) (tdm i).1 (pf i) (D (c.idx i))
    have hg : ∀ D, (∀ i ∈ c.W,
        (io i).checkOn (D (c.idx i)) (c.cm i) (tdm i).1 (pf i) = true) →
        allCheckWeight c.W g D = 1 := by
      intro D hD
      apply allCheckWeight_eq_one
      intro i hi
      exact checkAcceptWeight_eq_one io _ i _ _ _ _ (hD i hi)
    have htrue : a * ρ.matrix.trace.re ≤
        ((((extendedVCOracle k X Y U hU).withExtract ME code).coherent.toRuntime.run₂
          .instruments (QComp.allIn c.W fun i ↦ checkAt (Z := Z) VC B i (c.idx i) (c.cm i)
            (tdm i).1 (pf i))).branch true ρ.matrix).trace.re := by
      rw [branch_run₂_allIn_amplitudes
        ((extendedVCOracle k X Y U hU).withExtract ME code).coherent.toRuntime c.W
        (fun i ↦ checkAt (Z := Z) VC B i (c.idx i) (c.cm i) (tdm i).1 (pf i)) hCC g
        (fun i _ ↦ branch_run₂_checkAt_extendedVCOracle io U hU ME code B i (c.idx i)
          (c.cm i) (tdm i).1 (pf i))]
      exact trace_re_conj_amplitude_ge_of_conj (conjTranspose_compressDatabases k X Y) hCC
        (fun D ↦ ∀ i ∈ c.W,
          (io i).checkOn (D (c.idx i)) (c.cm i) (tdm i).1 (pf i) = true)
        (allCheckWeight c.W g) hg ha hPQ ρ.posSemidef hρ
    have hmono : (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q2 io) * ρ.matrix.trace.re ≤
        a * ρ.matrix.trace.re := mul_le_mul_of_nonneg_right ha0 ρ.trace_re_nonneg
    rw [← ENNReal.ofReal_mul (sub_nonneg.mpr (pow_le_one₀ hN hN1))]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith
  · have hf : (decide (c.W.card ≤ n) && decide (Function.Injective c.idx)) = false := by
      simpa using hcond
    rw [hf, SubInstrument.branch_pure_of_ne (by decide), LinearMap.zero_comp,
      LinearMap.zero_apply, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero]
    exact zero_le


/-- Sampling the oracle-free openings preserves the exact rejection bound. -/
theorem outcomeMeasure_run₂_openings_le_extended [∀ i, DecidableEq (DmOf ℓ Msg Td i)]
    (hC : Conditions VC io ME tdBot Pgood) (hk : 1 ≤ k) (n : ℕ) (c : ExtractClaim k Cm)
    {B : QReg} (tdm : TpDLen k (DmOf ℓ Msg Td) (TpIC.full hk c.idx c.cm).1)
    (φ : SubState (B × ((extendedVCOracle k X Y U hU).withExtract ME code).coherent.toRuntime.D))
    (hφ : MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ diagonal fun D : Fin k → Database X Y ↦
      if ME.extract (TpIC.full hk c.idx c.cm) D = tdm then 1 else 0) φ.matrix = φ.matrix) :
    (((extendedVCOracle k X Y U hU).withExtract ME code).coherent.toRuntime.run₂ .instruments
        ((QComp.pi fun i : Fin k ↦ openAt VC B i (tdm i).1.dom (tdm i).2).bind fun pf ↦
          (QComp.allIn c.W fun i ↦ checkAt (Z := Z) VC B i (c.idx i) (c.cm i) (tdm i).1
            (pf i)).bind fun b ↦ QuantumComp₂.pure
              (!b && decide (c.W.card ≤ n) && decide (Function.Injective c.idx)))).outcomeMeasure
        φ {true} ≤
      ENNReal.ofReal (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q2 io)) *
        ENNReal.ofReal φ.matrix.trace.re := by
  rw [QuantumRuntime.run₂_bind]
  refine SubInstrument.outcomeMeasure_bind_le _ _ _ (measurableSet_singleton _) fun pf ↦ ?_
  obtain ⟨c₀, hc₀, hz⟩ := exists_branch_run₂_pi_eq_smul
    ((extendedVCOracle k X Y U hU).withExtract ME code).coherent.toRuntime
    (fun i ↦ openAt VC B i (tdm i).1.dom (tdm i).2)
    (fun i ↦ support ((VC i).opening (tdm i).1.dom (tdm i).2))
    (fun i b ↦ exists_branch_run₂_toQuantumAt_coinImpl_eq_smul _ _ b) pf
  by_cases hs : ∃ i, pf i ∉ support ((VC i).opening (tdm i).1.dom (tdm i).2)
  · rw [SubInstrument.outcomeMeasure_eq_zero_of_matrix_eq_zero _ (by
      rw [SubInstrument.matrix_post, hc₀, hz hs, zero_smul, LinearMap.zero_apply])]
    exact zero_le
  · refine outcomeMeasure_run₂_checks_le_extended io U hU ME code hC hk n c tdm pf
      (fun i ↦ Classical.byContradiction fun h ↦ hs ⟨i, h⟩) _ ?_
    rw [SubInstrument.matrix_post, hc₀, LinearMap.smul_apply, LinearMap.id_apply]
    exact (LinearMap.map_smul _ c₀ φ.matrix).trans (congrArg (c₀ • ·) hφ)


/-- The P3 challenger obeys the exact extraction bound on every joint input state. -/
theorem outcomeMeasure_run₂_extractChallenger_le_extended (hC : Conditions VC io ME tdBot Pgood)
    (hk : 1 ≤ k) (n : ℕ) (c : ExtractClaim k Cm) {B : QReg}
    (σ : SubState (B × ((extendedVCOracle k X Y U hU).withExtract ME code).coherent.toRuntime.D)) :
    (((extendedVCOracle k X Y U hU).withExtract ME code).coherent.toRuntime.run₂ .instruments
        (extractChallenger VC code hk n c B)).outcomeMeasure σ {true} ≤
      ENNReal.ofReal (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q2 io)) *
        ENNReal.ofReal σ.matrix.trace.re := by
  let _ : ∀ i, DecidableEq (DmOf ℓ Msg Td i) := fun _ ↦ Classical.decEq _
  rw [extractChallenger, QuantumRuntime.run₂_bind]
  refine SubInstrument.outcomeMeasure_bind_le _ _ _ (measurableSet_singleton _) fun o ↦ ?_
  cases o with
  | none =>
    rw [QuantumRuntime.run₂_pure, SubInstrument.outcomeMeasure_pure]
    simp
  | some tdm =>
    refine outcomeMeasure_run₂_openings_le_extended io U hU ME code hC hk n c tdm _ ?_
    rw [SubInstrument.matrix_post,
      run₂_extractQuery_branch (extendedVCOracle k X Y U hU) ME code B]
    have hK := (mul_kronecker_mul (1 : Matrix B B ℂ) (1 : Matrix B B ℂ)
      (extractProj ME (TpIC.full hk c.idx c.cm) tdm)
      (extractProj ME (TpIC.full hk c.idx c.cm) tdm)).symm.trans
      (congrArg₂ (· ⊗ₖ ·) (Matrix.one_mul 1) (extractProj_mul_self ME _ tdm))
    exact (LinearMap.congr_fun (MatrixMap.conj_mul _ _) σ.matrix).symm.trans
      (congrArg (fun M ↦ MatrixMap.conj M σ.matrix) hK)


/-- P3 for every unitary empty-sector extension, with exact error
`1 - (1 - 1/N)^(2 n q₂)`. No exponent-two or flat-column hypothesis is needed. -/
theorem extractionCorrect_extendedVCOracle (hC : Conditions VC io ME tdBot Pgood) :
    ExtractionCorrect.{v, w} VC (extendedVCOracle k X Y U hU) ME code
      fun _ _ _ n ↦ extractError io n := by
  intro hk t n wVC wME A W x claim ρ _ _ _ _
  exact outcomeLawWith_experiment_true_le _ x _ ρ fun u y σ ↦
    outcomeMeasure_run₂_extractChallenger_le_extended io U hU ME code hC hk n (claim u y) σ


end challenger

end Quantum
