/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.RankSchedule
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.Incidence
public import VCVio.Quantum.Oracle.ParallelSchedule
public import VCVio.Quantum.Comp.Homogeneous
public import ToMathlib.MeasureTheory.Measure.UniformTable.Bounds

/-!
# Quantum hybrids at pointer-chain rank cutoffs

Before its cutoff, each scheduled oracle call programs only the raw path responses available
in the corresponding honest round. Earlier answers therefore depend on the complete raw words
in the reached rank prefix. Independent resampling beyond that prefix preserves the pre-query
state and public commitment, while future oracle inputs remain fresh. The initial state and
non-public program data are held fixed while future words are resampled; they may depend on
the fixed base oracle. A state obtained by preprocessing under the complete programmed oracle
does not satisfy this independence requirement without a separate preprocessing hybrid.

The full hidden key stays in the final observation. Below its honest receipt round, the final
cutoff execution is invariant under changing that key's auxiliary word. These statements allow
subnormalized inputs and arbitrary quantum private memory.
-/

public section

open Quantum Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal Kronecker

namespace PointerChainPuzzle.LeanSeal

universe u v w

variable {b n m B : ℕ} [NeZero n]
  {L : LocalSig.{u, v}} {V : QReg → Type w} {A : QReg}

/-- Before the cutoff, call `j` exposes path responses through rank `j + 1`.
At and after the cutoff it uses the complete programmed raw oracle. -/
@[expose]
def rankHybridSchedule (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (cutoff j : ℕ) : ByteArray.Bounded B → Bytes 32 :=
  if j < cutoff then prefixProgram hb hB salt x z (j + 1) H W
  else programPath hb hB salt x z H W

/-- Adjacent rank hybrids differ only in the call at the cutoff. -/
theorem rankHybridSchedule_eq_off_cutoff (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (h j : ℕ) (hj : j ≠ h) :
    rankHybridSchedule hb hB salt x z H W (h + 1) j =
      rankHybridSchedule hb hB salt x z H W h j := by
  by_cases hjh : j < h
  · simp [rankHybridSchedule, hjh, show j < h + 1 by omega]
  · simp [rankHybridSchedule, hjh, show ¬j < h + 1 by omega]

/-- A single rank-hybrid change is supported on path inputs beyond the next honest round.
The common observation may retain the full path words, including the hidden key. -/
theorem rpow_inv_two_evalDistMap_rankHybridSchedule_le (I : L.Interp)
    (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (prog : QuantumComp L (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) V A)
    (h : ℕ) (ρ : SubState A) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ C, V C) → γ) {s : Set γ} (hs : MeasurableSet s) :
    (parallelScheduledRuntime (rankHybridSchedule hb hB salt x z H W h)).evalDistMap I
      (prog.numberQueries 0) ρ f s ^ (2⁻¹ : ℝ) ≤
    (parallelScheduledRuntime (rankHybridSchedule hb hB salt x z H W (h + 1))).evalDistMap I
      (prog.numberQueries 0) ρ f s ^ (2⁻¹ : ℝ) +
      (4 * (parallelScheduledRuntime
        (rankHybridSchedule hb hB salt x z H W (h + 1))).queryWeight I
        (fun p ↦ parallelInputWeight (D := QReg.of Unit)
          (futureRawPathInputs hb hB salt x z W (h + 1)) p.2)
        (prog.numberQueries 0) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) h) ^ (2⁻¹ : ℝ) := by
  apply rpow_inv_two_evalDistMap_parallelSchedule_le_support
  · exact rankHybridSchedule_eq_off_cutoff hb hB salt x z H W h
  · intro d hd
    simpa [rankHybridSchedule] using
      (programPath_eq_prefixProgram_of_avoids_future hb hB salt x z (h + 1) H W d hd).symm
  · exact hs

/-- The query weight before call `h` depends only on full raw path words reached by rank `h`.
The weight itself is unchanged and may depend on the complete hidden challenge. -/
theorem queryWeight_rankHybridSchedule_eq_of_prefix (I : L.Interp)
    (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) {W W' : PathValue n m → Bytes 32} (h : ℕ)
    (hW : ∀ v ∈ PathValue.rankPrefix n m h, W v = W' v)
    (weight : ∀ p, Matrix (((qromBatchSpec (ByteArray.Bounded B) (Bytes 32)).numbered.In p)
      × QReg.of Unit) (((qromBatchSpec (ByteArray.Bounded B) (Bytes 32)).numbered.In p)
      × QReg.of Unit) ℂ → ℝ≥0∞)
    (prog : QuantumComp L (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) V A)
    (ρ : Matrix (A × QReg.of Unit) (A × QReg.of Unit) ℂ) :
    (parallelScheduledRuntime (rankHybridSchedule hb hB salt x z H W (h + 1))).queryWeight
      I weight (prog.numberQueries 0) ρ h =
    (parallelScheduledRuntime (rankHybridSchedule hb hB salt x z H W' (h + 1))).queryWeight
      I weight (prog.numberQueries 0) ρ h := by
  apply queryWeight_parallelScheduledRuntime_eq_of_prefix
  intro j hj
  simp only [rankHybridSchedule, show j < h + 1 by omega, ↓reduceIte]
  apply prefixProgram_eq_of_eq_on_rankPrefix
  intro v hv
  exact hW v (PathValue.rankPrefix_mono (by omega) hv)

/-- Independently resample unreached raw words, retaining the complete public commitment.
Full raw responses at reached nodes, including mask tails, stay fixed. -/
@[expose]
def resampleFuturePathWords (h : ℕ) (W W' : PathValue n m → Bytes 32) :
    PathValue n m → Bytes 32 :=
  resample (fun v ↦ v.rho ≤ h ∨ v = .commit) W W'

omit [NeZero n] in
/-- The typed projections of fresh raw words are the classical rank-prefix resampling. -/
theorem pathLabels_resampleFuturePathWords (hb : b ≤ 32) (h : ℕ)
    (W W' : PathValue n m → Bytes 32) :
    pathLabels hb (resampleFuturePathWords h W W') =
      mixLabels (PathValue.rankPrefix n m h) (pathLabels hb W) (pathLabels hb W') := by
  funext v
  by_cases hv : v.rho ≤ h ∨ v = .commit
  · simp [pathLabels, resampleFuturePathWords, resample, mixLabels, hv]
  · simp [pathLabels, resampleFuturePathWords, resample, mixLabels, hv]

omit [NeZero n] in
/-- Freshening future raw words preserves the structured public puzzle. -/
theorem labelPuzzle_resampleFuturePathWords (hb : b ≤ 32) (salt : Bytes 16)
    (x : Bytes b) (z : Fin (n - 1) → Bytes b) (h : ℕ)
    (W W' : PathValue n m → Bytes 32) :
    labelPuzzle salt x z (pathLabels hb (resampleFuturePathWords h W W')) =
      labelPuzzle salt x z (pathLabels hb W) := by
  rw [pathLabels_resampleFuturePathWords, labelPuzzle_mixLabels]

/-- The current pre-query weight is unchanged by freshening unreached raw responses.
The disagreement weight is retained as given, with its full challenge dependence. -/
theorem queryWeight_resampleFuturePathWords (I : L.Interp)
    (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (h : ℕ) (W W' : PathValue n m → Bytes 32)
    (weight : ∀ p, Matrix (((qromBatchSpec (ByteArray.Bounded B) (Bytes 32)).numbered.In p)
      × QReg.of Unit) (((qromBatchSpec (ByteArray.Bounded B) (Bytes 32)).numbered.In p)
      × QReg.of Unit) ℂ → ℝ≥0∞)
    (prog : QuantumComp L (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) V A)
    (ρ : Matrix (A × QReg.of Unit) (A × QReg.of Unit) ℂ) :
    (parallelScheduledRuntime
      (rankHybridSchedule hb hB salt x z H (resampleFuturePathWords h W W') (h + 1))).queryWeight
      I weight (prog.numberQueries 0) ρ h =
    (parallelScheduledRuntime (rankHybridSchedule hb hB salt x z H W (h + 1))).queryWeight
      I weight (prog.numberQueries 0) ρ h := by
  apply queryWeight_rankHybridSchedule_eq_of_prefix
  intro v hv
  simp [resampleFuturePathWords, resample, PathValue.mem_rankPrefix.mp hv]

/-- Below the key's receipt round, the final cutoff run is independent of its raw key word.
This is equality of complete instruments, including private memory. -/
theorem run_rankHybridSchedule_update_key (I : L.Interp)
    (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (key : Bytes 32) {r : ℕ}
    {prog : QuantumComp L (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) V A}
    (hr : prog.IsTotalQueryBound r) (hkey : r < keyRound n m) :
    (parallelScheduledRuntime
      (rankHybridSchedule hb hB salt x z H (Function.update W .key key) r)).run I
      (prog.numberQueries 0) =
    (parallelScheduledRuntime (rankHybridSchedule hb hB salt x z H W r)).run I
      (prog.numberQueries 0) := by
  apply Quantum.run_parallelScheduledRuntime_eq_of_prefix I _ _ hr
  intro j hj
  simp only [rankHybridSchedule, hj, ↓reduceIte]
  apply prefixProgram_eq_of_eq_on_rankPrefix
  intro v hv
  apply Function.update_of_ne
  intro he
  subst v
  have hh := PathValue.mem_rankPrefix.mp hv
  simp only [PathValue.rho_key] at hh
  omega


/-- Endpoint recovery with a fixed base oracle, public challenge coordinates and rank cutoff.
The hidden key is the same raw path word that determines the programmed key response. -/
@[expose]
noncomputable def rankHybridSuccess (I : L.Interp)
    (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32)
    (programs : Puzzle b n → QuantumComp L
      (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) (fun _ ↦ Bytes 32) A)
    (ρ : SubState A) (cutoff : ℕ) (W : PathValue n m → Bytes 32) : ℝ≥0∞ :=
  (parallelScheduledRuntime (rankHybridSchedule hb hB salt x z H W cutoff)).evalDistMap I
    ((programs (labelPuzzle salt x z (pathLabels hb W))).numberQueries 0) ρ
    (fun leaf ↦ leaf.2 = W .key) {True}

/-- The complete uniform path-word average retains the hidden key jointly with the output. -/
@[expose]
noncomputable def averageRankHybridSuccess (I : L.Interp)
    (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32)
    (programs : Puzzle b n → QuantumComp L
      (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) (fun _ ↦ Bytes 32) A)
    (ρ : SubState A) (cutoff : ℕ) : ℝ≥0∞ :=
  ∑ W : PathValue n m → Bytes 32, (Fintype.card (PathValue n m → Bytes 32) : ℝ≥0∞)⁻¹ *
    rankHybridSuccess I hb hB salt x z H programs ρ cutoff W

omit [NeZero n] in
private theorem freshKeyGuess_le_mass
    {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) (I : L.Interp)
    (prog : QuantumComp L spec (fun _ ↦ Bytes 32) A) (ρ : SubState A) :
    ∑ W : PathValue n m → Bytes 32, (Fintype.card (PathValue n m → Bytes 32) : ℝ≥0∞)⁻¹ *
      R.evalDistMap I prog ρ (fun leaf ↦ leaf.2 = W .key) {True} ≤
        ρ.mass / Fintype.card (Bytes 32) := by
  classical
  have hm : ∑' leaf, ENNReal.ofReal (R.jointPost I prog ρ leaf).matrix.trace.re ≤ ρ.mass := by
    have he := R.evalDistMap_apply_eq_mass_mul_normalize I prog ρ (fun _ ↦ ()) Set.univ
    have h := measure_univ_le (R.evalDistMap I prog ρ.normalize (fun _ ↦ ()))
    have hmass : R.evalDistMap I prog ρ (fun _ ↦ ()) Set.univ ≤ ρ.mass := by
      rw [he]
      exact mul_le_of_le_one_right (by positivity) h
    simpa only [QuantumRuntime.evalDistMap_apply _ _ _ _ _ MeasurableSet.univ,
      Set.indicator_univ, Pi.one_apply, mul_one] using hmass
  simp only [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (MeasurableSet.singleton True)]
  rw [Quantum.sum_tsum_guess]
  exact mul_le_mul hm le_rfl bot_le bot_le

/-- Before the key's honest receipt round, the last hybrid can recover that key only by
uniform guessing. Its bound scales with the input's successful mass. -/
theorem averageRankHybridSuccess_last_le (I : L.Interp)
    (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32)
    (programs : Puzzle b n → QuantumComp L
      (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) (fun _ ↦ Bytes 32) A)
    (ρ : SubState A) {r : ℕ} (hr : ∀ P, (programs P).IsTotalQueryBound r)
    (hkey : r < keyRound n m) :
    averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ r ≤
      ρ.mass / Fintype.card (Bytes 32) := by
  classical
  let : MeasurableSpace (Bytes 32) := ⊤
  let c : ℝ≥0∞ := (Fintype.card (PathValue n m → Bytes 32) : ℝ≥0∞)⁻¹
  let p := rankHybridSuccess (m := m) I hb hB salt x z H programs ρ r
  change (∑ W, c * p W) ≤ _
  rw [average_resample (fun v : PathValue n m ↦ v ≠ .key) p]
  have hi (W : PathValue n m → Bytes 32) :
      ∑ W', c * p (resample (fun v : PathValue n m ↦ v ≠ .key) W W') ≤
        ρ.mass / Fintype.card (Bytes 32) := by
    have hp (W' : PathValue n m → Bytes 32) :
        p (resample (fun v : PathValue n m ↦ v ≠ .key) W W') =
          (parallelScheduledRuntime (rankHybridSchedule hb hB salt x z H W r)).evalDistMap I
            ((programs (labelPuzzle salt x z (pathLabels hb W))).numberQueries 0) ρ
            (fun leaf ↦ leaf.2 = W' .key) {True} := by
      have ht : resample (fun v : PathValue n m ↦ v ≠ .key) W W' =
          Function.update W .key (W' .key) := by
        funext v
        by_cases hv : v = .key <;> simp [resample, hv]
      have hP : labelPuzzle salt x z (pathLabels hb (Function.update W .key (W' .key))) =
          labelPuzzle salt x z (pathLabels hb W) := by
        simp [labelPuzzle, pathLabels_update]
      have hrun := run_rankHybridSchedule_update_key I hb hB salt x z H W (W' .key)
        (hr (labelPuzzle salt x z (pathLabels hb W))) hkey
      simp only [p, rankHybridSuccess, ht, hP, Function.update_self,
        QuantumRuntime.evalDistMap, QuantumRuntime.matrix_jointPost]
      rw [hrun]
    simp_rw [hp]
    exact freshKeyGuess_le_mass _ I _ ρ
  calc
    _ ≤ ∑ _W : PathValue n m → Bytes 32, c *
        (ρ.mass / Fintype.card (Bytes 32)) := by
      apply Finset.sum_le_sum
      intro W _
      exact mul_le_mul le_rfl (hi W) bot_le bot_le
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _), one_mul]


omit [NeZero n] in
private theorem pointerHitBound_ne_top : hitBound n m (Bytes 32) (Bytes b) ≠ ⊤ := by
  unfold hitBound
  split_ifs <;> finiteness

section IncidenceMeasure

variable [MeasurableSpace (Bytes 32)] [MeasurableSingletonClass (Bytes 32)]

/-- Fresh raw path words satisfy the classical incidence bound after their typed projection.
The public commitment and every reached raw response stay fixed during resampling. -/
theorem uniformOn_mem_futureRawPathInputs_resample_le
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (W : PathValue n m → Bytes 32) (h : ℕ) (d : ByteArray.Bounded B) :
    (uniformOn Set.univ : Measure (PathValue n m → Bytes 32))
      {W' | d ∈ futureRawPathInputs hb hB salt x z
        (resampleFuturePathWords h W W') (h + 1)} ≤
      hitBound n m (Bytes 32) (Bytes b) := by
  classical
  let : MeasurableSpace (Labels n m (Bytes 32) (Bytes b)) := ⊤
  let ev : Set (Labels n m (Bytes 32) (Bytes b)) :=
    {ℓ' | ∃ v : PathValue n m, h + 1 < v.rho ∧
      d = pathWindowInput hB salt x z v
        (mixLabels (PathValue.rankPrefix n m h) (pathLabels hb W) ℓ')}
  have he := congrArg (fun μ : Measure (Labels n m (Bytes 32) (Bytes b)) ↦ μ ev)
    (uniformOn_univ_map_pathLabels (n := n) (m := m) hb)
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete] at he
  have hev : {W' | d ∈ futureRawPathInputs hb hB salt x z
        (resampleFuturePathWords h W W') (h + 1)} = (pathLabels hb) ⁻¹' ev := by
    ext W'
    simp only [futureRawPathInputs, Set.mem_ofPred_eq, rawPathInput,
      pathLabels_resampleFuturePathWords, Set.mem_preimage, ev]
  rw [hev, he]
  have hi := prEvent_eq_futurePathWindowInput_mixLabels_le hn hB salt x z (pathLabels hb W) h d
  rwa [prEvent_eq_evalDist_of_discrete, SampleableType.evalDist_uniformSample] at hi

end IncidenceMeasure

/-- Finite real incidence weights for a fresh rank suffix of full raw path words. -/
theorem sum_indicator_futureRawPathInputs_resample_le
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (W : PathValue n m → Bytes 32) (h : ℕ) (d : ByteArray.Bounded B) :
    ∑ W' : PathValue n m → Bytes 32,
      (futureRawPathInputs hb hB salt x z (resampleFuturePathWords h W W') (h + 1)).indicator
        (fun _ ↦ (Fintype.card (PathValue n m → Bytes 32) : ℝ)⁻¹) d ≤
      (hitBound n m (Bytes 32) (Bytes b)).toReal := by
  classical
  let : MeasurableSpace (Bytes 32) := ⊤
  have hi := uniformOn_mem_futureRawPathInputs_resample_le hb hn hB salt x z W h d
  rw [uniformOn_univ_apply_setOf] at hi
  have hr := ENNReal.toReal_mono pointerHitBound_ne_top hi
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at hr
  convert hr using 1
  simp only [Set.indicator_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- The expected future-input query weight is width times the classical rank incidence.
Its reference pre-query state is fixed before the fresh suffix is sampled. -/
theorem sum_queryWeight_resampleFuturePathWords_le (I : L.Interp)
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (h : ℕ) (W : PathValue n m → Bytes 32)
    (k : ℕ) {prog : QuantumComp L (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) V A}
    (hk : prog.IsWidthBound k) (ρ : SubState A) :
    ∑ W' : PathValue n m → Bytes 32,
      (Fintype.card (PathValue n m → Bytes 32) : ℝ≥0∞)⁻¹ *
      (parallelScheduledRuntime
        (rankHybridSchedule hb hB salt x z H
          (resampleFuturePathWords h W W') (h + 1))).queryWeight I
        (fun p ↦ parallelInputWeight (D := QReg.of Unit)
          (futureRawPathInputs hb hB salt x z (resampleFuturePathWords h W W') (h + 1)) p.2)
        (prog.numberQueries 0) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) h ≤
      (k : ℝ≥0∞) * hitBound n m (Bytes 32) (Bytes b) := by
  simp_rw [queryWeight_resampleFuturePathWords]
  have hc : ENNReal.ofReal ((Fintype.card (PathValue n m → Bytes 32) : ℝ)⁻¹) =
      (Fintype.card (PathValue n m → Bytes 32) : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
  have hh := sum_mul_queryWeight_parallelInputWeight_numberQueries_le
    (parallelScheduledRuntime (rankHybridSchedule hb hB salt x z H W (h + 1))) I
    (fun _ : PathValue n m → Bytes 32 ↦ (Fintype.card (PathValue n m → Bytes 32) : ℝ)⁻¹)
    (by intro W'; positivity)
    (fun W' ↦ futureRawPathInputs hb hB salt x z (resampleFuturePathWords h W W') (h + 1))
    (hitBound n m (Bytes 32) (Bytes b)).toReal ENNReal.toReal_nonneg
    (sum_indicator_futureRawPathInputs_resample_le hb hn hB salt x z W h)
    k hk (ρ.prod (SubState.basis ())) 0 h
  simpa only [hc, SubState.matrix_prod,
    ENNReal.ofReal_toReal pointerHitBound_ne_top] using hh

end PointerChainPuzzle.LeanSeal
