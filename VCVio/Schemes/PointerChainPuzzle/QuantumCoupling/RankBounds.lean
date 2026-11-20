/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.RankHybrid

/-!
# Recovery bounds from pointer-chain rank hybrids

The full hidden path-word average is retained through every oracle hybrid. Square-root
probabilities are accumulated before converting to an event bound. The initial state is
independent of the fresh path words, but may depend on the fixed base oracle; preprocessing
under a programmed oracle requires a separate comparison before using this bound.
-/

public section

open Quantum Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal Kronecker

namespace PointerChainPuzzle.LeanSeal

universe u v

private theorem uniform_average_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (a : ℝ≥0∞) :
    ∑ _ω : Ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * a = a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), one_mul]

/-- The online rank-hybrid error before the separate path-input collision allowance.
The root probability is accumulated across rounds and squared once at the end. -/
@[expose]
noncomputable def rankRecoveryBound (b n m r k : ℕ) : ℝ≥0∞ :=
  ((Fintype.card (Bytes 32) : ℝ≥0∞)⁻¹ ^ (2⁻¹ : ℝ) +
    (r : ℝ≥0∞) * (4 * (k : ℝ≥0∞) * hitBound n m (Bytes 32) (Bytes b)) ^ (2⁻¹ : ℝ)) ^ 2

private theorem le_last_add_mul (p : ℕ → ℝ≥0∞) (e : ℝ≥0∞) (r : ℕ)
    (h : ∀ j < r, p j ≤ p (j + 1) + e) : p 0 ≤ p r + r * e := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      p 0 ≤ p r + r * e := ih (fun j hj ↦ h j (by omega))
      _ ≤ (p (r + 1) + e) + r * e := add_le_add (h r (by omega)) le_rfl
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]; ac_rfl

variable {b n m B : ℕ} [NeZero n] {L : LocalSig.{u, v}} {A : QReg}

/-- One averaged rank-hybrid step, conditional on a fixed reached raw prefix. The program
family sees only the unchanged public puzzle; its input state is independent of the fresh
suffix. The final observation retains the fresh key word jointly with the output. -/
theorem sqrt_sum_rankHybridSuccess_resample_le (I : L.Interp)
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32)
    (programs : Puzzle b n → QuantumComp L
      (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) (fun _ ↦ Bytes 32) A)
    (ρ : SubState A) (h k : ℕ) (hk : ∀ P, (programs P).IsWidthBound k)
    (W : PathValue n m → Bytes 32) :
    (∑ W' : PathValue n m → Bytes 32,
      (Fintype.card (PathValue n m → Bytes 32) : ℝ≥0∞)⁻¹ *
        rankHybridSuccess I hb hB salt x z H programs ρ h
          (resampleFuturePathWords h W W')) ^ (2⁻¹ : ℝ) ≤
    (∑ W' : PathValue n m → Bytes 32,
      (Fintype.card (PathValue n m → Bytes 32) : ℝ≥0∞)⁻¹ *
        rankHybridSuccess I hb hB salt x z H programs ρ (h + 1)
          (resampleFuturePathWords h W W')) ^ (2⁻¹ : ℝ) +
      (4 * (k : ℝ≥0∞) * hitBound n m (Bytes 32) (Bytes b)) ^ (2⁻¹ : ℝ) := by
  classical
  let c : ℝ≥0∞ := (Fintype.card (PathValue n m → Bytes 32) : ℝ≥0∞)⁻¹
  let p (W' : PathValue n m → Bytes 32) :=
    rankHybridSuccess I hb hB salt x z H programs ρ h (resampleFuturePathWords h W W')
  let a (W' : PathValue n m → Bytes 32) :=
    rankHybridSuccess I hb hB salt x z H programs ρ (h + 1) (resampleFuturePathWords h W W')
  let mass (W' : PathValue n m → Bytes 32) :=
    (parallelScheduledRuntime (rankHybridSchedule hb hB salt x z H
      (resampleFuturePathWords h W W') (h + 1))).queryWeight I
      (fun port ↦ parallelInputWeight (D := QReg.of Unit)
        (futureRawPathInputs hb hB salt x z (resampleFuturePathWords h W W') (h + 1)) port.2)
      ((programs (labelPuzzle salt x z (pathLabels hb W))).numberQueries 0)
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) h
  have hprogram (W' : PathValue n m → Bytes 32) :
      programs (labelPuzzle salt x z (pathLabels hb (resampleFuturePathWords h W W'))) =
        programs (labelPuzzle salt x z (pathLabels hb W)) := by
    rw [labelPuzzle_resampleFuturePathWords]
  have hh (W' : PathValue n m → Bytes 32) :
      p W' ^ (2⁻¹ : ℝ) ≤ a W' ^ (2⁻¹ : ℝ) + (4 * mass W') ^ (2⁻¹ : ℝ) := by
    simpa only [p, a, mass, rankHybridSuccess, hprogram] using
      rpow_inv_two_evalDistMap_rankHybridSchedule_le I hb hB salt x z H
        (resampleFuturePathWords h W W')
        (programs (labelPuzzle salt x z (pathLabels hb W))) h ρ
        (fun leaf ↦ leaf.2 = resampleFuturePathWords h W W' .key)
        (MeasurableSet.singleton True)
  have hm : ∑ W', c * (4 * mass W') ≤
      4 * (k : ℝ≥0∞) * hitBound n m (Bytes 32) (Bytes b) := by
    calc
      _ = 4 * ∑ W', c * mass W' := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro W' _
        ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul (le_rfl : (4 : ℝ≥0∞) ≤ 4)
          (sum_queryWeight_resampleFuturePathWords_le I hb hn hB salt x z H h W k
            (hk (labelPuzzle salt x z (pathLabels hb W))) ρ) bot_le bot_le
  have havg := rpow_inv_two_tsum_mul_le_of_le_add (fun _ ↦ c) p a
    (fun W' ↦ 4 * mass W') hh
  simp only [tsum_fintype] at havg
  exact havg.trans
    (add_le_add le_rfl (ENNReal.rpow_le_rpow hm (by norm_num)))

/-- Average a one-call root comparison over the complete unconditional raw path-word law. -/
theorem sqrt_averageRankHybridSuccess_le_succ (I : L.Interp)
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32)
    (programs : Puzzle b n → QuantumComp L
      (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) (fun _ ↦ Bytes 32) A)
    (ρ : SubState A) (h k : ℕ) (hk : ∀ P, (programs P).IsWidthBound k) :
    averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ h ^ (2⁻¹ : ℝ) ≤
      averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ (h + 1) ^ (2⁻¹ : ℝ) +
        (4 * (k : ℝ≥0∞) * hitBound n m (Bytes 32) (Bytes b)) ^ (2⁻¹ : ℝ) := by
  classical
  let : MeasurableSpace (Bytes 32) := ⊤
  let c : ℝ≥0∞ := (Fintype.card (PathValue n m → Bytes 32) : ℝ≥0∞)⁻¹
  let p (W : PathValue n m → Bytes 32) :=
    ∑ W', c * rankHybridSuccess I hb hB salt x z H programs ρ h
      (resampleFuturePathWords h W W')
  let a (W : PathValue n m → Bytes 32) :=
    ∑ W', c * rankHybridSuccess I hb hB salt x z H programs ρ (h + 1)
      (resampleFuturePathWords h W W')
  let err : ℝ≥0∞ := 4 * (k : ℝ≥0∞) * hitBound n m (Bytes 32) (Bytes b)
  have hh := rpow_inv_two_tsum_mul_le_of_le_add (fun _ ↦ c) p a (fun _ ↦ err)
    (fun W ↦ sqrt_sum_rankHybridSuccess_resample_le I hb hn hB salt x z H programs ρ h k hk W)
  simp only [tsum_fintype] at hh
  have hp : (∑ W, c * p W) = averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ h := by
    exact (average_resample (fun v : PathValue n m ↦ v.rho ≤ h ∨ v = .commit)
      (rankHybridSuccess I hb hB salt x z H programs ρ h)).symm
  have ha : (∑ W, c * a W) =
      averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ (h + 1) := by
    exact (average_resample (fun v : PathValue n m ↦ v.rho ≤ h ∨ v = .commit)
      (rankHybridSuccess I hb hB salt x z H programs ρ (h + 1))).symm
  have he : (∑ _W : PathValue n m → Bytes 32, c * err) = err :=
    uniform_average_const err
  change (∑ W, c * p W) ^ (2⁻¹ : ℝ) ≤
    (∑ W, c * a W) ^ (2⁻¹ : ℝ) + (∑ _W : PathValue n m → Bytes 32, c * err) ^ (2⁻¹ : ℝ)
    at hh
  rw [hp, ha, he] at hh
  exact hh


/-- Accumulate root probabilities through the online round budget. The last hybrid leaves
its key uniformly fresh, and no intermediate step converts a root error to an event error. -/
theorem sqrt_averageRankHybridSuccess_zero_le (I : L.Interp)
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32)
    (programs : Puzzle b n → QuantumComp L
      (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) (fun _ ↦ Bytes 32) A)
    (ρ : SubState A) {r k : ℕ} (hr : ∀ P, (programs P).IsTotalQueryBound r)
    (hk : ∀ P, (programs P).IsWidthBound k) (hkey : r < keyRound n m) :
    averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ 0 ^ (2⁻¹ : ℝ) ≤
      (Fintype.card (Bytes 32) : ℝ≥0∞)⁻¹ ^ (2⁻¹ : ℝ) +
        (r : ℝ≥0∞) *
          (4 * (k : ℝ≥0∞) * hitBound n m (Bytes 32) (Bytes b)) ^ (2⁻¹ : ℝ) := by
  have ht := le_last_add_mul
    (fun h ↦ averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ h ^ (2⁻¹ : ℝ))
    ((4 * (k : ℝ≥0∞) * hitBound n m (Bytes 32) (Bytes b)) ^ (2⁻¹ : ℝ)) r
    (fun h _ ↦ sqrt_averageRankHybridSuccess_le_succ I hb hn hB salt x z H programs ρ h k hk)
  have hlast : averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ r ≤
      (Fintype.card (Bytes 32) : ℝ≥0∞)⁻¹ := by
    refine (averageRankHybridSuccess_last_le I hb hB salt x z H programs ρ hr hkey).trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity)
      (ENNReal.ofReal_le_one.mpr ρ.trace_re_le_one)
  exact ht.trans (add_le_add (ENNReal.rpow_le_rpow hlast (by norm_num)) le_rfl)

/-- The root-accumulated rank bound on the full programmed-word recovery average. -/
theorem averageRankHybridSuccess_zero_le (I : L.Interp)
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32)
    (programs : Puzzle b n → QuantumComp L
      (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) (fun _ ↦ Bytes 32) A)
    (ρ : SubState A) {r k : ℕ} (hr : ∀ P, (programs P).IsTotalQueryBound r)
    (hk : ∀ P, (programs P).IsWidthBound k) (hkey : r < keyRound n m) :
    averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ 0 ≤
      rankRecoveryBound b n m r k := by
  have hh := sqrt_averageRankHybridSuccess_zero_le I hb hn hB salt x z H programs ρ hr hk hkey
  unfold rankRecoveryBound
  rw [← ENNReal.rpow_two]
  rw [← rpow_inv_two_rpow_two
    (averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ 0)]
  exact ENNReal.rpow_le_rpow hh (by norm_num)

/-- The online programmed bound scales with the successful input mass. This form supports
summing retained preprocessing branches after replacing their oracle by the independent base. -/
theorem averageRankHybridSuccess_zero_le_mul_mass (I : L.Interp)
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32)
    (programs : Puzzle b n → QuantumComp L
      (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) (fun _ ↦ Bytes 32) A)
    (ρ : SubState A) {r k : ℕ} (hr : ∀ P, (programs P).IsTotalQueryBound r)
    (hk : ∀ P, (programs P).IsWidthBound k) (hkey : r < keyRound n m) :
    averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ 0 ≤
      ρ.mass * rankRecoveryBound b n m r k := by
  have he : averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ 0 =
      ρ.mass * averageRankHybridSuccess (m := m) I hb hB salt x z H programs ρ.normalize 0 := by
    unfold averageRankHybridSuccess
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro W _
    unfold rankHybridSuccess
    rw [QuantumRuntime.evalDistMap_apply_eq_mass_mul_normalize]
    ring
  rw [he]
  exact mul_le_mul le_rfl
    (averageRankHybridSuccess_zero_le I hb hn hB salt x z H programs ρ.normalize hr hk hkey)
    bot_le bot_le

/-- The zero-cutoff hybrid is the actual fixed programmed raw oracle experiment. -/
theorem rankHybridSuccess_zero (I : L.Interp)
    (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32)
    (programs : Puzzle b n → QuantumComp L
      (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) (fun _ ↦ Bytes 32) A)
    (ρ : SubState A) (W : PathValue n m → Bytes 32) :
    rankHybridSuccess I hb hB salt x z H programs ρ 0 W =
      (parallelOracleRuntime (programPath hb hB salt x z H W)).evalDistMap I
        (programs (labelPuzzle salt x z (pathLabels hb W))) ρ
        (fun leaf ↦ leaf.2 = W .key) {True} := by
  unfold rankHybridSuccess
  have he : rankHybridSchedule hb hB salt x z H W 0 =
      fun _ ↦ programPath hb hB salt x z H W := by
    funext j
    simp [rankHybridSchedule]
  rw [he, Quantum.evalDistMap_parallelScheduledRuntime_const]

/-- A concrete online bound under the unconditionally programmed oracle. The adversary sees
only its structured public puzzle; the hidden word law stays uniform throughout the proof. -/
theorem sum_programmedRecovery_le_mul_mass (I : L.Interp)
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32)
    (programs : Puzzle b n → QuantumComp L
      (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) (fun _ ↦ Bytes 32) A)
    (ρ : SubState A) {r k : ℕ} (hr : ∀ P, (programs P).IsTotalQueryBound r)
    (hk : ∀ P, (programs P).IsWidthBound k) (hkey : r < keyRound n m) :
    ∑ W : PathValue n m → Bytes 32, (Fintype.card (PathValue n m → Bytes 32) : ℝ≥0∞)⁻¹ *
      (parallelOracleRuntime (programPath hb hB salt x z H W)).evalDistMap I
        (programs (labelPuzzle salt x z (pathLabels hb W))) ρ
        (fun leaf ↦ leaf.2 = W .key) {True} ≤
      ρ.mass * rankRecoveryBound b n m r k := by
  simpa only [averageRankHybridSuccess, rankHybridSuccess_zero] using
    averageRankHybridSuccess_zero_le_mul_mass I hb hn hB salt x z H programs ρ hr hk hkey

end PointerChainPuzzle.LeanSeal
