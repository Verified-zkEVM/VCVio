/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.MaskedChain.RootBounds
public import VCVio.Quantum.Oracle.MaskedChain.Preprocessing.Model
public import VCVio.Quantum.Oracle.MaskedChain.Preprocessing.DropEmpty
public import VCVio.Quantum.Oracle.ParallelFinisher
public import VCVio.Quantum.Oracle.LocalExecution

/-!
# Masked-chain security with query-bounded preprocessing

Preprocessing shares the online oracle and retains its complete quantum memory. The
fresh hidden chain is sampled afterwards. Its input cells therefore have small incidence
against the reference preprocessing state, even when that state depends on the base oracle.
Only oracle queries are bounded; this is distinct from an auxiliary-input model with
unbounded preprocessing and bounded advice.
-/

public section
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal Kronecker
namespace Quantum.MaskedChain

section Incidence
variable {G : Type} [Fintype G] [Nonempty G]
open scoped Classical in
private theorem all_input_hit_sum_le (q : ℕ) (z : G) :
    (∑ xs : Fin (q + 2) → G,
      Set.indicator (tailInputs (fun i : Fin (q + 1) ↦ xs i.castSucc) 0)
        (fun _ ↦ (Fintype.card (Fin (q + 2) → G) : ℝ)⁻¹) z) ≤
      (q + 1 : ℝ) / Fintype.card G := by
  let : MeasurableSpace G := ⊤
  let s : Finset (Fin (q + 2)) := Finset.Iio (Fin.last (q + 1))
  have hcard : s.card = q + 1 := by simp [s]
  have he (xs : Fin (q + 2) → G) :
      (∃ i ∈ s, xs i = z) ↔
        z ∈ tailInputs (fun i : Fin (q + 1) ↦ xs i.castSucc) 0 := by
    constructor
    · rintro ⟨i, hi, he⟩
      have hi' : i < Fin.last (q + 1) := Finset.mem_Iio.mp hi
      exact ⟨⟨i.val, hi'⟩, Nat.zero_le _, he⟩
    · rintro ⟨i, _, he⟩
      exact ⟨i.castSucc, Finset.mem_Iio.mpr i.isLt, he⟩
  have hb := uniform_hit_sum_le s z
  rw [hcard] at hb
  norm_num only [Nat.cast_add, Nat.cast_one] at hb
  convert hb using 1
  apply Finset.sum_congr rfl
  intro xs _
  by_cases hx : ∃ i ∈ s, xs i = z
  · have hz := (he xs).mp hx
    simp [hx, hz]
  · have hz := mt (he xs).mpr hx
    simp [hx, hz]
end Incidence

variable {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- Event-probability loss from changing the oracle during query-bounded preprocessing.
The hidden chain has `q + 1` freshly sampled oracle-input vertices. -/
@[expose]
noncomputable def preprocessingError (G : Type) [Fintype G] (q r Q : ℕ) : ℝ≥0∞ :=
  4 * ((r : ℝ≥0∞) * Q * (((q + 1 : ℕ) : ℝ≥0∞) / Fintype.card G)) ^ (2⁻¹ : ℝ)

private theorem sum_reducedPost_mass_le_one {q : ℕ} (H : G → G)
    (adv : PreprocessingAdversary G q) :
    ∑' pre : Σ M, adv.State M,
      ((parallelOracleRuntime H).reducedPost .instruments adv.preprocess
        adv.initialState pre).mass ≤ 1 :=
  tsum_mass_reducedPost_parallel_le_one .instruments H adv.preprocess adv.initialState

private theorem averageHybridSuccess_zero_eq_sum {q : ℕ}
    (adv : OnlineAdversary LocalSig.instruments G q) (H : G → G)
    (masks : Fin (q + 1) → G) :
    averageHybridSuccess .instruments adv H masks 0 =
      ∑ vertices : Fin (q + 2) → G,
        (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
          (parallelOracleRuntime (fullOracle H vertices masks)).evalDistMap .instruments
            (adv.run (vertices 0, masks)) adv.initialState
            (fun leaf ↦ leaf.2 = vertices (Fin.last (q + 1))) {True} := by
  unfold averageHybridSuccess hybridSuccess
  apply Finset.sum_congr rfl
  intro vertices _
  have hs : hybridSchedule H vertices masks 0 = fun _ ↦ fullOracle H vertices masks := by
    funext j
    simp [hybridSchedule]
  rw [hs, evalDistMap_parallelScheduledRuntime_const]

private theorem evalDistMap_bind_observed {q : ℕ} (H₀ H₁ : G → G)
    (adv : PreprocessingAdversary G q) (puzzle : Puzzle G q) (key : G) :
    (parallelOracleRuntime H₀).evalDistMap .instruments
      (adv.preprocess.bind fun M state ↦ QuantumComp.localObservation
        (parallelRunUnit .instruments H₁ (adv.online M state puzzle)))
      adv.initialState (fun leaf ↦ leaf.2 = key) {True} =
    ∑' pre : Σ M, adv.State M,
      (parallelOracleRuntime H₁).evalDistMap .instruments
        (adv.online pre.1 pre.2 puzzle)
        ((parallelOracleRuntime H₀).reducedPost .instruments adv.preprocess adv.initialState pre)
        (fun leaf ↦ leaf.2 = key) {True} :=
  evalDistMap_bind_parallelLocalObservation H₀ H₁ adv.preprocess
    (fun M state ↦ adv.online M state puzzle) adv.initialState
    (fun leaf ↦ leaf = key) {True} (MeasurableSet.singleton True)

private theorem evalDistMap_bind_same_observed {q : ℕ} (H : G → G)
    (adv : PreprocessingAdversary G q) (puzzle : Puzzle G q) (key : G) :
    (parallelOracleRuntime H).evalDistMap .instruments
      (adv.preprocess.bind fun M state ↦ QuantumComp.localObservation
        (parallelRunUnit .instruments H (adv.online M state puzzle)))
      adv.initialState (fun leaf ↦ leaf.2 = key) {True} =
    (parallelOracleRuntime H).evalDistMap .instruments
      (preprocessedRecoveryProgram adv puzzle) adv.initialState
      (fun leaf ↦ leaf.2 = key) {True} := by
  simpa only [preprocessedRecoveryProgram] using
    evalDistMap_bind_same_parallelLocalObservation H adv.preprocess
      (fun M state ↦ adv.online M state puzzle) adv.initialState
      (fun leaf ↦ leaf = key) {True} (MeasurableSet.singleton True)

private noncomputable def referenceSuccess {q : ℕ} (H : G → G) (adv : PreprocessingAdversary G q)
    (masks : Fin (q + 1) → G) : ℝ≥0∞ :=
  ∑' pre : Σ M, adv.State M,
    ∑ vertices : Fin (q + 2) → G,
      (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
        (parallelOracleRuntime (fullOracle H vertices masks)).evalDistMap .instruments
          (adv.online pre.1 pre.2 (vertices 0, masks))
          ((parallelOracleRuntime H).reducedPost .instruments
            adv.preprocess adv.initialState pre)
          (fun leaf ↦ leaf.2 = vertices (Fin.last (q + 1))) {True}

private theorem referenceSuccess_le {q k : ℕ} (H : G → G) (adv : PreprocessingAdversary G q)
    (masks : Fin (q + 1) → G)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound q ∧
        (adv.online M state puzzle).IsWidthBound k) :
    referenceSuccess H adv masks ≤ patchedRecoveryBound G q k := by
  unfold referenceSuccess
  calc
    _ ≤ ∑' pre : Σ M, adv.State M,
        ((parallelOracleRuntime H).reducedPost .instruments adv.preprocess
          adv.initialState pre).mass * patchedRecoveryBound G q k := by
      apply tsum_le_tsum
      intro pre
      let online : OnlineAdversary LocalSig.instruments G q :=
        { initialReg := pre.1
          initialState := (parallelOracleRuntime H).reducedPost .instruments
            adv.preprocess adv.initialState pre
          run := adv.online pre.1 pre.2 }
      have hb := averageHybridSuccess_zero_le_mul_mass .instruments online H masks k
        (fun puzzle ↦ (honline pre.1 pre.2 puzzle).1)
        (fun puzzle ↦ (honline pre.1 pre.2 puzzle).2)
      rw [averageHybridSuccess_zero_eq_sum] at hb
      exact hb
    _ = (∑' pre : Σ M, adv.State M,
        ((parallelOracleRuntime H).reducedPost .instruments adv.preprocess
          adv.initialState pre).mass) * patchedRecoveryBound G q k :=
      ENNReal.tsum_mul_right
    _ ≤ patchedRecoveryBound G q k :=
      mul_le_of_le_one_left (by positivity) (sum_reducedPost_mass_le_one H adv)


private theorem averageHybridSuccess_preprocessing_le {q k r Q : ℕ}
    (adv : PreprocessingAdversary G q) (H : G → G) (masks : Fin (q + 1) → G)
    (hr : adv.preprocess.IsTotalQueryBound r) (hQ : adv.preprocess.IsPointBound Q)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound q ∧
        (adv.online M state puzzle).IsWidthBound k) :
    averageHybridSuccess .instruments (preprocessedRecoveryAdversary adv) H masks 0 ≤
      patchedRecoveryBound G q k + preprocessingError G q r Q := by
  let finish (xs : Fin (q + 2) → G) (M : QReg) (state : adv.State M) :=
    QuantumComp.localObservation (spec := qromBatchSpec G G)
      (parallelRunUnit .instruments (fullOracle H xs masks)
        (adv.online M state (xs 0, masks)))
  have hc : (0 : ℝ) < Fintype.card (Fin (q + 2) → G) := by
    exact_mod_cast Fintype.card_pos
  have hn : ∑ _xs : Fin (q + 2) → G,
      ENNReal.ofReal (Fintype.card (Fin (q + 2) → G) : ℝ)⁻¹ ≤ 1 := by
    simp only [ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact (ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)).le
  have hs (xs : Fin (q + 2) → G) (z : G)
      (hz : z ∉ tailInputs (fun i : Fin (q + 1) ↦ xs i.castSucc) 0) :
      fullOracle H xs masks z = H z := by
    rw [fullOracle_eq_prefixOracle_of_not_mem_tailInputs H xs masks 0 z hz]
    simp [prefixOracle]
  have hb := sum_mul_evalDistMap_bind_parallel_le .instruments H
    (fun xs : Fin (q + 2) → G ↦ fullOracle H xs masks)
    (fun _ ↦ (Fintype.card (Fin (q + 2) → G) : ℝ)⁻¹) (fun _ ↦ le_of_lt (inv_pos.mpr hc))
    hn (fun xs ↦ tailInputs (fun i : Fin (q + 1) ↦ xs i.castSucc) 0) hs
    ((q + 1 : ℝ) / Fintype.card G) (by positivity)
    (all_input_hit_sum_le q) hr hQ finish
    (fun xs M state ↦ QuantumComp.isTotalQueryBound_localObservation _ 0)
    adv.initialState (fun xs leaf ↦ leaf.2 = xs (Fin.last (q + 1)))
    (MeasurableSet.singleton True)
  have hd : ENNReal.ofReal ((q + 1 : ℝ) / Fintype.card G) =
      ((q + 1 : ℕ) : ℝ≥0∞) / Fintype.card G := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos)]
    simp [ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ q) zero_le_one]
  dsimp only [finish] at hb
  simp_rw [evalDistMap_bind_same_observed, evalDistMap_bind_observed] at hb
  simp only [ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast, hd] at hb
  have href :
      (∑ xs : Fin (q + 2) → G,
        (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
          ∑' pre : Σ M, adv.State M,
            (parallelOracleRuntime (fullOracle H xs masks)).evalDistMap .instruments
              (adv.online pre.1 pre.2 (xs 0, masks))
              ((parallelOracleRuntime H).reducedPost .instruments adv.preprocess
                adv.initialState pre)
              (fun leaf ↦ leaf.2 = xs (Fin.last (q + 1))) {True}) =
        referenceSuccess H adv masks := by
    simp only [← ENNReal.tsum_mul_left]
    exact (Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)).symm
  rw [href] at hb
  rw [averageHybridSuccess_zero_eq_sum]
  exact hb.trans (add_le_add (referenceSuccess_le H adv masks honline) le_rfl)

/-- Endpoint security with query-bounded preprocessing and unrestricted retained memory.
The same oracle answers both phases. Preprocessing has at most `r` rounds and `Q` points;
the online phase has at most `q` rounds of width `k`. Hidden vertices and the endpoint event
remain joint throughout the comparison. This does not bound unbounded preprocessing with
bounded auxiliary advice. -/
theorem preprocessedRecoveryAdvantage_le {q k r Q : ℕ}
    (adv : PreprocessingAdversary G q)
    (hr : adv.preprocess.IsTotalQueryBound r) (hQ : adv.preprocess.IsPointBound Q)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound q ∧
        (adv.online M state puzzle).IsWidthBound k) :
    preprocessedRecoveryAdvantage adv ≤
      min 1 (recoveryBound G q k + preprocessingError G q r Q) := by
  refine le_min (preprocessedRecoveryAdvantage_le_one adv) ?_
  have hb := recoveryAdvantage_le_of_patched_bound .instruments
    (preprocessedRecoveryAdversary adv)
    (patchedRecoveryBound G q k + preprocessingError G q r Q)
    (fun H masks ↦ averageHybridSuccess_preprocessing_le adv H masks hr hQ honline)
  rw [recoveryBound_eq_patchedRecoveryBound_add_collision]
  exact hb.trans_eq (by ac_rfl)

/-- A preprocessing point budget gives a linear error when it also bounds the number of
nonempty rounds. -/
theorem preprocessingError_self (G : Type) [Fintype G] (q Q : ℕ) :
    preprocessingError G q Q Q =
      4 * (Q : ℝ≥0∞) * (((q + 1 : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ) := by
  unfold preprocessingError
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← pow_two,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num [mul_assoc]

/-- Empty preprocessing calls can be removed before counting rounds. Thus the effective
round budget is the smaller of the stated round and point budgets, including for programs
with arbitrarily many zero-width calls across their branches. -/
theorem preprocessedRecoveryAdvantage_le_min {q k r Q : ℕ}
    (adv : PreprocessingAdversary G q)
    (hr : adv.preprocess.IsTotalQueryBound r) (hQ : adv.preprocess.IsPointBound Q)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound q ∧
        (adv.online M state puzzle).IsWidthBound k) :
    preprocessedRecoveryAdvantage adv ≤
      min 1 (recoveryBound G q k + preprocessingError G q (min r Q) Q) := by
  have hm : (dropEmptyPreprocessing adv).preprocess.IsTotalQueryBound (min r Q) := by
    rcases le_total r Q with h | h
    · rw [min_eq_left h]
      exact isTotalQueryBound_dropEmptyPreprocessing adv hr
    · rw [min_eq_right h]
      exact isTotalQueryBound_dropEmptyPreprocessing_of_isPointBound adv hQ
  have hb := preprocessedRecoveryAdvantage_le (dropEmptyPreprocessing adv) hm
    (isPointBound_dropEmptyPreprocessing adv hQ) honline
  rwa [preprocessedRecoveryAdvantage_dropEmptyPreprocessing_eq] at hb

/-- A preprocessing point budget alone yields a linear error. Zero-width calls may be
unbounded across branches: they are removed without changing the experiment before applying
the round-aware theorem. Retained quantum and classical memory remain unrestricted. -/
theorem preprocessedRecoveryAdvantage_le_points {q k Q : ℕ}
    (adv : PreprocessingAdversary G q) (hQ : adv.preprocess.IsPointBound Q)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound q ∧
        (adv.online M state puzzle).IsWidthBound k) :
    preprocessedRecoveryAdvantage adv ≤
      min 1 (recoveryBound G q k +
        4 * (Q : ℝ≥0∞) * (((q + 1 : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ)) := by
  have hb := preprocessedRecoveryAdvantage_le (dropEmptyPreprocessing adv)
    (isTotalQueryBound_dropEmptyPreprocessing_of_isPointBound adv hQ)
    (isPointBound_dropEmptyPreprocessing adv hQ) honline
  rwa [preprocessedRecoveryAdvantage_dropEmptyPreprocessing_eq, preprocessingError_self] at hb

/-- Root-accumulated recovery with query-bounded preprocessing. The complete online and
preprocessing root errors are combined before squaring; the vertex-collision allowance is
added once outside the square. -/
@[expose]
noncomputable def rootPreprocessedRecoveryBound (G : Type) [Fintype G]
    (q k r Q : ℕ) : ℝ≥0∞ :=
  (rootPatchedRecoveryBound G q k ^ (2⁻¹ : ℝ) +
    2 * ((r : ℝ≥0∞) * Q * (((q + 1 : ℕ) : ℝ≥0∞) / Fintype.card G)) ^ (2⁻¹ : ℝ)) ^ 2 +
      (((q + 1).choose 2 : ℕ) : ℝ≥0∞) / Fintype.card G

private theorem referenceSuccess_le_root {q k : ℕ} (H : G → G)
    (adv : PreprocessingAdversary G q) (masks : Fin (q + 1) → G)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound q ∧
        (adv.online M state puzzle).IsWidthBound k) :
    referenceSuccess H adv masks ≤ rootPatchedRecoveryBound G q k := by
  unfold referenceSuccess
  calc
    _ ≤ ∑' pre : Σ M, adv.State M,
        ((parallelOracleRuntime H).reducedPost .instruments adv.preprocess
          adv.initialState pre).mass * rootPatchedRecoveryBound G q k := by
      apply tsum_le_tsum
      intro pre
      let online : OnlineAdversary LocalSig.instruments G q :=
        { initialReg := pre.1
          initialState := (parallelOracleRuntime H).reducedPost .instruments
            adv.preprocess adv.initialState pre
          run := adv.online pre.1 pre.2 }
      have hb := averageHybridSuccess_zero_le_root_mul_mass .instruments online H masks k
        (fun puzzle ↦ (honline pre.1 pre.2 puzzle).1)
        (fun puzzle ↦ (honline pre.1 pre.2 puzzle).2)
      rw [averageHybridSuccess_zero_eq_sum] at hb
      exact hb
    _ = (∑' pre : Σ M, adv.State M,
        ((parallelOracleRuntime H).reducedPost .instruments adv.preprocess
          adv.initialState pre).mass) * rootPatchedRecoveryBound G q k :=
      ENNReal.tsum_mul_right
    _ ≤ rootPatchedRecoveryBound G q k :=
      mul_le_of_le_one_left (by positivity) (sum_reducedPost_mass_le_one H adv)

private theorem averageHybridSuccess_preprocessing_le_root {q k r Q : ℕ}
    (adv : PreprocessingAdversary G q) (H : G → G) (masks : Fin (q + 1) → G)
    (hr : adv.preprocess.IsTotalQueryBound r) (hQ : adv.preprocess.IsPointBound Q)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound q ∧
        (adv.online M state puzzle).IsWidthBound k) :
    averageHybridSuccess .instruments (preprocessedRecoveryAdversary adv) H masks 0 ≤
      (rootPatchedRecoveryBound G q k ^ (2⁻¹ : ℝ) +
        2 * ((r : ℝ≥0∞) * Q * (((q + 1 : ℕ) : ℝ≥0∞) / Fintype.card G)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  let finish (xs : Fin (q + 2) → G) (M : QReg) (state : adv.State M) :=
    QuantumComp.localObservation (spec := qromBatchSpec G G)
      (parallelRunUnit .instruments (fullOracle H xs masks)
        (adv.online M state (xs 0, masks)))
  have hc : (0 : ℝ) < Fintype.card (Fin (q + 2) → G) := by
    exact_mod_cast Fintype.card_pos
  have hs (xs : Fin (q + 2) → G) (z : G)
      (hz : z ∉ tailInputs (fun i : Fin (q + 1) ↦ xs i.castSucc) 0) :
      fullOracle H xs masks z = H z := by
    rw [fullOracle_eq_prefixOracle_of_not_mem_tailInputs H xs masks 0 z hz]
    simp [prefixOracle]
  have hb := rpow_inv_two_sum_mul_evalDistMap_bind_parallel_le .instruments H
    (fun xs : Fin (q + 2) → G ↦ fullOracle H xs masks)
    (fun _ ↦ (Fintype.card (Fin (q + 2) → G) : ℝ)⁻¹) (fun _ ↦ le_of_lt (inv_pos.mpr hc))
    (fun xs ↦ tailInputs (fun i : Fin (q + 1) ↦ xs i.castSucc) 0) hs
    ((q + 1 : ℝ) / Fintype.card G) (by positivity)
    (all_input_hit_sum_le q) hr hQ finish
    (fun xs M state ↦ QuantumComp.isTotalQueryBound_localObservation _ 0)
    adv.initialState (fun xs leaf ↦ leaf.2 = xs (Fin.last (q + 1)))
    (MeasurableSet.singleton True)
  have hd : ENNReal.ofReal ((q + 1 : ℝ) / Fintype.card G) =
      ((q + 1 : ℕ) : ℝ≥0∞) / Fintype.card G := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos)]
    simp [ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ q) zero_le_one]
  dsimp only [finish] at hb
  simp_rw [evalDistMap_bind_same_observed, evalDistMap_bind_observed] at hb
  simp only [ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast, hd] at hb
  have href :
      (∑ xs : Fin (q + 2) → G,
        (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
          ∑' pre : Σ M, adv.State M,
            (parallelOracleRuntime (fullOracle H xs masks)).evalDistMap .instruments
              (adv.online pre.1 pre.2 (xs 0, masks))
              ((parallelOracleRuntime H).reducedPost .instruments adv.preprocess
                adv.initialState pre)
              (fun leaf ↦ leaf.2 = xs (Fin.last (q + 1))) {True}) =
        referenceSuccess H adv masks := by
    simp only [← ENNReal.tsum_mul_left]
    exact (Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)).symm
  rw [href] at hb
  have hroot := hb.trans (add_le_add
    (ENNReal.rpow_le_rpow (referenceSuccess_le_root H adv masks honline) (by norm_num)) le_rfl)
  rw [averageHybridSuccess_zero_eq_sum]
  rw [← ENNReal.rpow_two,
    ← rpow_inv_two_rpow_two (∑ vertices : Fin (q + 2) → G,
      (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
        (parallelOracleRuntime (fullOracle H vertices masks)).evalDistMap .instruments
          ((preprocessedRecoveryAdversary adv).run (vertices 0, masks))
          (preprocessedRecoveryAdversary adv).initialState
          (fun leaf ↦ leaf.2 = vertices (Fin.last (q + 1))) {True})]
  exact ENNReal.rpow_le_rpow hroot (by norm_num)

/-- Endpoint security with one shared oracle and query-bounded preprocessing, accumulating
online and preprocessing root errors before squaring. Retained memory is unrestricted and
the vertex-collision allowance is charged once outside that square. -/
theorem preprocessedRecoveryAdvantage_le_root {q k r Q : ℕ}
    (adv : PreprocessingAdversary G q)
    (hr : adv.preprocess.IsTotalQueryBound r) (hQ : adv.preprocess.IsPointBound Q)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound q ∧
        (adv.online M state puzzle).IsWidthBound k) :
    preprocessedRecoveryAdvantage adv ≤ min 1 (rootPreprocessedRecoveryBound G q k r Q) := by
  refine le_min (preprocessedRecoveryAdvantage_le_one adv) ?_
  exact recoveryAdvantage_le_of_patched_bound .instruments
    (preprocessedRecoveryAdversary adv)
    ((rootPatchedRecoveryBound G q k ^ (2⁻¹ : ℝ) +
      2 * ((r : ℝ≥0∞) * Q * (((q + 1 : ℕ) : ℝ≥0∞) / Fintype.card G)) ^ (2⁻¹ : ℝ)) ^ 2)
    (fun H masks ↦ averageHybridSuccess_preprocessing_le_root adv H masks hr hQ honline)

/-- Empty preprocessing calls can be omitted before applying the root-accumulated bound,
so only the smaller of the supplied round and point budgets is needed. -/
theorem preprocessedRecoveryAdvantage_le_root_min {q k r Q : ℕ}
    (adv : PreprocessingAdversary G q)
    (hr : adv.preprocess.IsTotalQueryBound r) (hQ : adv.preprocess.IsPointBound Q)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound q ∧
        (adv.online M state puzzle).IsWidthBound k) :
    preprocessedRecoveryAdvantage adv ≤
      min 1 (rootPreprocessedRecoveryBound G q k (min r Q) Q) := by
  have hm : (dropEmptyPreprocessing adv).preprocess.IsTotalQueryBound (min r Q) := by
    rcases le_total r Q with h | h
    · rw [min_eq_left h]
      exact isTotalQueryBound_dropEmptyPreprocessing adv hr
    · rw [min_eq_right h]
      exact isTotalQueryBound_dropEmptyPreprocessing_of_isPointBound adv hQ
  have hb := preprocessedRecoveryAdvantage_le_root (dropEmptyPreprocessing adv) hm
    (isPointBound_dropEmptyPreprocessing adv hQ) honline
  rwa [preprocessedRecoveryAdvantage_dropEmptyPreprocessing_eq] at hb

end Quantum.MaskedChain
