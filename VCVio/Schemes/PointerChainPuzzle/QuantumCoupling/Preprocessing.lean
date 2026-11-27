/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.Scheme
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.RankBounds
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.PreprocessingIncidence
public import VCVio.Quantum.Oracle.ParallelFinisher

/-!
# Quantum delay of the byte-encoded pointer-chain puzzle

The exact finite-window experiment uses one raw oracle for preprocessing, honest generation
and online recovery. A comparison replaces preprocessing under the programmed oracle by
preprocessing under the independent base table, retaining the actual branch register and
classical state. The full online execution remains under the programmed oracle and is treated
as a common physical finishing operation in that comparison.

Fresh salt, link and path-response sampling bounds the preprocessing incidence. The online
rank bound then applies separately to each retained reference branch, weighted by its successful
mass. Root probabilities are accumulated before squaring; path-input collisions are charged
once, outside that square. Preprocessing is query-bounded with unrestricted retained memory,
rather than unbounded preprocessing with bounded auxiliary advice.
-/

public section

open Quantum MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PointerChainPuzzle.LeanSeal

variable {b n m B : ℕ}

private abbrev Challenge (b n m : ℕ) :=
  Bytes 16 × (Bytes b × (Fin (n - 1) → Bytes b)) × (PathValue n m → Bytes 32)

private theorem uniform_sum_prod {A C : Type*} [Fintype A] [Fintype C]
    (f : A × C → ℝ≥0∞) :
    ∑ p, (Fintype.card (A × C) : ℝ≥0∞)⁻¹ * f p =
      ∑ a, (Fintype.card A : ℝ≥0∞)⁻¹ *
        ∑ c, (Fintype.card C : ℝ≥0∞)⁻¹ * f (a, c) := by
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))]
  ring

private theorem uniform_sum_const {A : Type*} [Fintype A] [Nonempty A] (a : ℝ≥0∞) :
    ∑ _x : A, (Fintype.card A : ℝ≥0∞)⁻¹ * a = a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), one_mul]

/-- The exact construction's query-bounded preprocessing error, combined with online recovery
and the single path-input collision allowance. The raw byte-window length does not occur. -/
@[expose]
noncomputable def rankDelayBound (b n m r k rpre Qpre : ℕ) : ℝ≥0∞ :=
  (solvePoints n m : ℝ≥0∞) ^ 2 / Fintype.card (Bytes 32) +
    (rankRecoveryBound b n m r k ^ (2⁻¹ : ℝ) +
      2 * ((rpre : ℝ≥0∞) * Qpre * preprocessingIncidence b n m) ^ (2⁻¹ : ℝ)) ^ 2

variable [NeZero n]

private noncomputable def programmedSample (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (adv : WindowAdversary b n B) (H : ByteArray.Bounded B → Bytes 32) : ℝ≥0∞ :=
  ∑ ω : Challenge b n m, (Fintype.card (Challenge b n m) : ℝ≥0∞)⁻¹ *
    windowRecoveryAt adv (programPath hb hB ω.1 ω.2.1.1 ω.2.1.2 H ω.2.2)
      (labelPuzzle ω.1 ω.2.1.1 ω.2.1.2 (pathLabels hb ω.2.2)) (ω.2.2 .key)

private noncomputable def referenceSample (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (adv : WindowAdversary b n B) (H : ByteArray.Bounded B → Bytes 32) : ℝ≥0∞ :=
  ∑ ω : Challenge b n m, (Fintype.card (Challenge b n m) : ℝ≥0∞)⁻¹ *
    ∑' pre : Σ M, adv.State M,
      (parallelOracleRuntime (programPath hb hB ω.1 ω.2.1.1 ω.2.1.2 H ω.2.2)).evalDistMap
        .instruments (adv.online pre.1 pre.2
          (labelPuzzle ω.1 ω.2.1.1 ω.2.1.2 (pathLabels hb ω.2.2)))
        ((parallelOracleRuntime H).reducedPost .instruments adv.preprocess adv.initialState pre)
        (fun leaf ↦ leaf.2 = ω.2.2 .key) {True}

private theorem referenceSample_le (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B) (adv : WindowAdversary b n B)
    (H : ByteArray.Bounded B → Bytes 32) {r k : ℕ}
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound r ∧
        (adv.online M state puzzle).IsWidthBound k) (hkey : r < keyRound n m) :
    referenceSample (m := m) hb hB adv H ≤ rankRecoveryBound b n m r k := by
  have hbranch (pre : Σ M, adv.State M) :
      ∑ ω : Challenge b n m, (Fintype.card (Challenge b n m) : ℝ≥0∞)⁻¹ *
        (parallelOracleRuntime (programPath hb hB ω.1 ω.2.1.1 ω.2.1.2 H ω.2.2)).evalDistMap
          .instruments (adv.online pre.1 pre.2
            (labelPuzzle ω.1 ω.2.1.1 ω.2.1.2 (pathLabels hb ω.2.2)))
          ((parallelOracleRuntime H).reducedPost .instruments adv.preprocess adv.initialState pre)
          (fun leaf ↦ leaf.2 = ω.2.2 .key) {True} ≤
      ((parallelOracleRuntime H).reducedPost .instruments adv.preprocess
        adv.initialState pre).mass * rankRecoveryBound b n m r k := by
    rw [uniform_sum_prod]
    calc
      _ ≤ ∑ salt : Bytes 16, (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ *
          (((parallelOracleRuntime H).reducedPost .instruments adv.preprocess
            adv.initialState pre).mass * rankRecoveryBound b n m r k) := by
        apply Finset.sum_le_sum
        intro salt _
        apply mul_le_mul le_rfl _ bot_le bot_le
        rw [uniform_sum_prod]
        calc
          _ ≤ ∑ _p : Bytes b × (Fin (n - 1) → Bytes b),
              (Fintype.card (Bytes b × (Fin (n - 1) → Bytes b)) : ℝ≥0∞)⁻¹ *
                (((parallelOracleRuntime H).reducedPost .instruments adv.preprocess
                  adv.initialState pre).mass * rankRecoveryBound b n m r k) := by
            apply Finset.sum_le_sum
            intro p _
            apply mul_le_mul le_rfl _ bot_le bot_le
            exact sum_programmedRecovery_le_mul_mass .instruments hb hn hB salt p.1 p.2 H
              (adv.online pre.1 pre.2) _
              (fun P ↦ (honline pre.1 pre.2 P).1)
              (fun P ↦ (honline pre.1 pre.2 P).2) hkey
          _ = _ := uniform_sum_const _
      _ = _ := uniform_sum_const _
  unfold referenceSample
  simp only [← ENNReal.tsum_mul_left]
  rw [← tsum_fintype (L := SummationFilter.unconditional (Challenge b n m)),
    tsum_comm]
  simp only [tsum_fintype]
  calc
    _ ≤ ∑' pre : Σ M, adv.State M,
        ((parallelOracleRuntime H).reducedPost .instruments adv.preprocess
          adv.initialState pre).mass * rankRecoveryBound b n m r k :=
      tsum_le_tsum hbranch
    _ = (∑' pre : Σ M, adv.State M,
        ((parallelOracleRuntime H).reducedPost .instruments adv.preprocess
          adv.initialState pre).mass) * rankRecoveryBound b n m r k :=
      ENNReal.tsum_mul_right
    _ ≤ _ := mul_le_of_le_one_left (by positivity)
      (tsum_mass_reducedPost_parallel_le_one .instruments H adv.preprocess adv.initialState)

private theorem programmedSample_le (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B) (adv : WindowAdversary b n B)
    (H : ByteArray.Bounded B → Bytes 32) {r k rpre Qpre : ℕ}
    (hr : adv.preprocess.IsTotalQueryBound rpre) (hQ : adv.preprocess.IsPointBound Qpre)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound r ∧
        (adv.online M state puzzle).IsWidthBound k) (hkey : r < keyRound n m) :
    programmedSample (m := m) hb hB adv H ≤
      (rankRecoveryBound b n m r k ^ (2⁻¹ : ℝ) +
        2 * ((rpre : ℝ≥0∞) * Qpre * preprocessingIncidence b n m) ^ (2⁻¹ : ℝ)) ^ 2 := by
  classical
  let finish (ω : Challenge b n m) (M : QReg) (state : adv.State M) :=
    QuantumComp.localObservation
      (spec := qromBatchSpec (ByteArray.Bounded B) (Bytes 32))
      (parallelRunUnit .instruments (programPath hb hB ω.1 ω.2.1.1 ω.2.1.2 H ω.2.2)
        (adv.online M state (labelPuzzle ω.1 ω.2.1.1 ω.2.1.2 (pathLabels hb ω.2.2))))
  have hc : (0 : ℝ) < Fintype.card (Challenge b n m) := by
    exact_mod_cast Fintype.card_pos
  have hs (ω : Challenge b n m) (d : ByteArray.Bounded B)
      (hd : d ∉ {t | ∃ v, t = rawPathInput hb hB ω.1 ω.2.1.1 ω.2.1.2 v ω.2.2}) :
      programPath hb hB ω.1 ω.2.1.1 ω.2.1.2 H ω.2.2 d = H d :=
    programPath_apply_of_avoids hb hB ω.1 ω.2.1.1 ω.2.1.2 H ω.2.2 d
      (fun v he ↦ hd ⟨v, he.symm⟩)
  have hh := rpow_inv_two_sum_mul_evalDistMap_bind_parallel_le .instruments H
    (fun ω : Challenge b n m ↦ programPath hb hB ω.1 ω.2.1.1 ω.2.1.2 H ω.2.2)
    (fun _ ↦ (Fintype.card (Challenge b n m) : ℝ)⁻¹)
    (fun _ ↦ le_of_lt (inv_pos.mpr hc))
    (fun ω ↦ {t | ∃ v, t = rawPathInput hb hB ω.1 ω.2.1.1 ω.2.1.2 v ω.2.2}) hs
    (preprocessingIncidenceReal b n m) (preprocessingIncidenceReal_nonneg b n m)
    (sum_indicator_rawPathInputs_seed_le (m := m) hb hn hB) hr hQ finish
    (fun ω M state ↦ QuantumComp.isTotalQueryBound_localObservation _ 0)
    adv.initialState (fun ω leaf ↦ leaf.2 = ω.2.2 .key) (MeasurableSet.singleton True)
  have hactual (ω : Challenge b n m) :
      (parallelOracleRuntime (programPath hb hB ω.1 ω.2.1.1 ω.2.1.2 H ω.2.2)).evalDistMap
        .instruments (adv.preprocess.bind (finish ω)) adv.initialState
        (fun leaf ↦ leaf.2 = ω.2.2 .key) {True} =
      windowRecoveryAt adv (programPath hb hB ω.1 ω.2.1.1 ω.2.1.2 H ω.2.2)
        (labelPuzzle ω.1 ω.2.1.1 ω.2.1.2 (pathLabels hb ω.2.2)) (ω.2.2 .key) :=
    evalDistMap_bind_same_parallelLocalObservation _ adv.preprocess
      (fun M state ↦ adv.online M state
        (labelPuzzle ω.1 ω.2.1.1 ω.2.1.2 (pathLabels hb ω.2.2))) adv.initialState
      (fun out ↦ out = ω.2.2 .key) {True} (MeasurableSet.singleton True)
  have href (ω : Challenge b n m) :=
    evalDistMap_bind_parallelLocalObservation H
      (programPath hb hB ω.1 ω.2.1.1 ω.2.1.2 H ω.2.2) adv.preprocess
      (fun M state ↦ adv.online M state
        (labelPuzzle ω.1 ω.2.1.1 ω.2.1.2 (pathLabels hb ω.2.2))) adv.initialState
      (fun out ↦ out = ω.2.2 .key) {True} (MeasurableSet.singleton True)
  simp_rw [hactual] at hh
  dsimp only [finish] at hh
  simp_rw [href] at hh
  simp only [ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast,
    ofReal_preprocessingIncidenceReal] at hh
  change programmedSample (m := m) hb hB adv H ^ (2⁻¹ : ℝ) ≤
    referenceSample (m := m) hb hB adv H ^ (2⁻¹ : ℝ) +
      2 * ((rpre : ℝ≥0∞) * Qpre * preprocessingIncidence b n m) ^ (2⁻¹ : ℝ) at hh
  have hbnd := hh.trans (add_le_add
    (ENNReal.rpow_le_rpow (referenceSample_le hb hn hB adv H honline hkey) (by norm_num)) le_rfl)
  rw [← ENNReal.rpow_two, ← rpow_inv_two_rpow_two (programmedSample (m := m) hb hB adv H)]
  exact ENNReal.rpow_le_rpow hbnd (by norm_num)

section Average

variable (saltSpace : MeasurableSpace (Bytes 16))
  [@MeasurableSingletonClass (Bytes 16) saltSpace]
  [MeasurableSpace (Bytes b)] [MeasurableSingletonClass (Bytes b)]
  (keySpace : MeasurableSpace (Bytes 32))
  [@MeasurableSingletonClass (Bytes 32) keySpace]

private theorem programmedSample_eq_lintegral (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (adv : WindowAdversary b n B) (H : ByteArray.Bounded B → Bytes 32) :
    letI := saltSpace
    letI := keySpace
    programmedSample (m := m) hb hB adv H =
      ∫⁻ salt, ∫⁻ p : Bytes b × (Fin (n - 1) → Bytes b), ∫⁻ W : PathValue n m → Bytes 32,
        windowRecoveryAt adv (programPath hb hB salt p.1 p.2 H W)
          (labelPuzzle salt p.1 p.2 (pathLabels hb W)) (W .key)
        ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32))
        ∂(uniformOn Set.univ : Measure (Bytes b × (Fin (n - 1) → Bytes b)))
        ∂(uniformOn Set.univ : Measure (Bytes 16)) := by
  let : MeasurableSpace (Bytes 16) := saltSpace
  let : MeasurableSpace (Bytes 32) := keySpace
  have h (f : Challenge b n m → ℝ≥0∞) :
      (∑ ω, (Fintype.card (Challenge b n m) : ℝ≥0∞)⁻¹ * f ω) =
      ∫⁻ ω, f ω ∂(uniformOn Set.univ : Measure (Challenge b n m)) := by
    rw [lintegral_uniformOn_univ, div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  rw [programmedSample, h, uniformOn_univ_prod,
    lintegral_prod _ Measurable.of_discrete.aemeasurable]
  simp_rw [uniformOn_univ_prod, lintegral_prod _ Measurable.of_discrete.aemeasurable]

end Average

private theorem programmedWindowRecoveryAdvantage_eq_lintegral (hb : b ≤ 32)
    (hB : hashInputBound b ≤ B) (adv : WindowAdversary b n B) :
    letI : MeasurableSpace (Bytes 32) := ⊤
    programmedWindowRecoveryAdvantage (m := m) hb hB adv =
      ∫⁻ H, programmedSample (m := m) hb hB adv H
        ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32)) := by
  let : MeasurableSpace (Bytes 32) := ⊤
  let : MeasurableSpace (Bytes 16) := ⊤
  let : MeasurableSpace (Bytes b) := ⊤
  unfold programmedWindowRecoveryAdvantage
  symm
  simp_rw [programmedSample_eq_lintegral
    (saltSpace := inferInstance) (keySpace := inferInstance)]
  rw [lintegral_lintegral_swap Measurable.of_discrete.aemeasurable]
  apply lintegral_congr
  intro salt
  exact lintegral_lintegral_swap Measurable.of_discrete.aemeasurable

/-- Quantum delay of the exact finite-window construction against query-bounded preprocessing
when every online branch stops before the key's honest receipt round. Retained classical and
quantum memory are unrestricted, and unsuccessful branches are not normalized. -/
theorem qromDelayAdvantage_quantumWindowScheme_le_of_preprocessing
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (adv : WindowAdversary b n B) {r k rpre Qpre : ℕ}
    (hr : adv.preprocess.IsTotalQueryBound rpre) (hQ : adv.preprocess.IsPointBound Qpre)
    (honline : ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound r ∧
        (adv.online M state puzzle).IsWidthBound k) (hkey : r < keyRound n m) :
    Quantum.TimeLockPuzzle.qromDelayAdvantage (quantumWindowScheme (n := n) hB m) adv ≤
      min 1 (rankDelayBound b n m r k rpre Qpre) := by
  let : MeasurableSpace (Bytes 32) := ⊤
  let : MeasurableSpace (Bytes 16) := ⊤
  let : MeasurableSpace (Bytes b) := ⊤
  refine le_min (Quantum.TimeLockPuzzle.sampledDelayAdvantage_le_one
    parallelOracleRuntime (quantumWindowScheme hB m) adv) ?_
  have hp : programmedWindowRecoveryAdvantage (m := m) hb hB adv ≤
      (rankRecoveryBound b n m r k ^ (2⁻¹ : ℝ) +
        2 * ((rpre : ℝ≥0∞) * Qpre * preprocessingIncidence b n m) ^ (2⁻¹ : ℝ)) ^ 2 := by
    rw [programmedWindowRecoveryAdvantage_eq_lintegral hb hB adv]
    calc
      _ ≤ ∫⁻ _H : ByteArray.Bounded B → Bytes 32,
          (rankRecoveryBound b n m r k ^ (2⁻¹ : ℝ) +
            2 * ((rpre : ℝ≥0∞) * Qpre * preprocessingIncidence b n m) ^ (2⁻¹ : ℝ)) ^ 2
          ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32)) :=
        lintegral_mono fun H ↦ programmedSample_le hb hn hB adv H hr hQ honline hkey
      _ = _ := by simp
  exact (qromDelayAdvantage_quantumWindowScheme_le_programmed hb hn hB adv).trans
    ((add_le_add hp le_rfl).trans_eq (by unfold rankDelayBound; ac_rfl))

/-- Security of the exact finite-window puzzle against every adversary satisfying the stated
phase-local query budgets before the honest key round. Retained memory is unrestricted. -/
theorem qromDelaySecure_quantumWindowScheme (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B) (budget : Quantum.TimeLockPuzzle.DelayBudget)
    (hkey : budget.onlineRounds < keyRound n m) :
    Quantum.TimeLockPuzzle.QROMDelaySecure (quantumWindowScheme (n := n) hB m) budget
      (min 1 (rankDelayBound b n m budget.onlineRounds budget.onlineWidth
        budget.preprocessingRounds budget.preprocessingPoints)) := by
  intro adv hbound
  exact qromDelayAdvantage_quantumWindowScheme_le_of_preprocessing hb hn hB adv hbound.1
    hbound.2.1 (fun M state puzzle ↦
      ⟨(hbound.2.2 M state puzzle).1, (hbound.2.2 M state puzzle).2.2⟩) hkey

/-- Security with the effective online width bounded by both the width cap and the total point
budget. The adversary class is unchanged: both constraints already hold on every online branch.
In particular, a zero point budget removes the online hybrid error even with a loose width cap. -/
theorem qromDelaySecure_quantumWindowScheme_min_width_points
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (budget : Quantum.TimeLockPuzzle.DelayBudget)
    (hkey : budget.onlineRounds < keyRound n m) :
    Quantum.TimeLockPuzzle.QROMDelaySecure (quantumWindowScheme (n := n) hB m) budget
      (min 1 (rankDelayBound b n m budget.onlineRounds
        (min budget.onlineWidth budget.onlinePoints)
        budget.preprocessingRounds budget.preprocessingPoints)) := by
  intro adv hbound
  apply qromDelayAdvantage_quantumWindowScheme_le_of_preprocessing hb hn hB adv
    hbound.1 hbound.2.1 _ hkey
  intro M state puzzle
  obtain ⟨hr, hp, hw⟩ := hbound.2.2 M state puzzle
  refine ⟨hr, ?_⟩
  rcases le_total budget.onlineWidth budget.onlinePoints with h | h
  · simpa [min_eq_left h] using hw
  · simpa [min_eq_right h] using hp.isWidthBound

end PointerChainPuzzle.LeanSeal
