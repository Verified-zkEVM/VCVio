/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.MaskedChain.Homogeneous

/-!
# Root-accumulated masked-chain recovery bounds

Square-root event probabilities are compared across adjacent oracle schedules and averaged
before their errors are accumulated. Squaring once at the end gives an online error of order
`kq³ / |G|`. The hidden endpoint remains joint with the output throughout the proof. The
classical coupling adds its vertex-collision allowance outside the square.

The conditional online bound permits arbitrary subnormalized input states and scales with
their successful mass. Its input and public-puzzle program family are fixed independently
of the sampled vertices; they may depend on the fixed base function and masks.
-/

public section

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal Kronecker

namespace Quantum.MaskedChain

/-- Online guessing and root-hybrid errors before the vertex-collision allowance. -/
@[expose]
noncomputable def rootPatchedRecoveryBound (G : Type) [Fintype G] (q k : ℕ) : ℝ≥0∞ :=
  ((Fintype.card G : ℝ≥0∞)⁻¹ ^ (2⁻¹ : ℝ) +
    2 * ∑ h ∈ Finset.range q,
      ((k : ℝ≥0∞) * ((q - h : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ)) ^ 2

/-- Root-accumulated online recovery with one external vertex-collision allowance. -/
@[expose]
noncomputable def rootRecoveryBound (G : Type) [Fintype G] (q k : ℕ) : ℝ≥0∞ :=
  rootPatchedRecoveryBound G q k +
    (((q + 2).choose 2 : ℕ) : ℝ≥0∞) / Fintype.card G

private theorem uniform_average_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (a : ℝ≥0∞) :
    ∑ _ω : Ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * a = a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), one_mul]

private theorem four_rpow_inv_two : (4 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 2 := by
  apply ENNReal.rpow_left_injective (show (2 : ℝ) ≠ 0 by norm_num)
  change ((4 : ℝ≥0∞) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = (2 : ℝ≥0∞) ^ (2 : ℝ)
  rw [rpow_inv_two_rpow_two, ENNReal.rpow_two]
  norm_num

universe u v w
variable {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- A root comparison conditional on one reached vertex prefix. The complete fresh endpoint
is retained by the common observation while the query state is independent of that suffix. -/
theorem sqrt_sum_evalDistMap_resampleFutureVertices_le {q : ℕ} (I : L.Interp) (H : G → G)
    (masks : Fin (q + 1) → G) (h : ℕ) (a : Fin (q + 2) → G)
    (k : ℕ) {x : QuantumComp L (qromBatchSpec G G) W A} (hx : x.IsWidthBound k)
    (ρ : SubState A) (δ : ℝ) (hδ : 0 ≤ δ)
    (hS : ∀ z, ∑ b : Fin (q + 2) → G,
      (tailInputs (fun i : Fin (q + 1) ↦ b i.castSucc) (h + 1)).indicator
        (fun _ ↦ (Fintype.card (Fin (q + 2) → G) : ℝ)⁻¹) z ≤ δ)
    {γ : Type*} [MeasurableSpace γ]
    (f : (Fin (q + 2) → G) → (Σ B, W B) → γ) {s : Set γ} (hs : MeasurableSet s) :
    (∑ b : Fin (q + 2) → G, (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
      (parallelScheduledRuntime
        (hybridSchedule H (resampleFutureVertices h a b) masks h)).evalDistMap I
        (x.numberQueries 0) ρ (f b) s) ^ (2⁻¹ : ℝ) ≤
    (∑ b : Fin (q + 2) → G, (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
      (parallelScheduledRuntime
        (hybridSchedule H (resampleFutureVertices h a b) masks (h + 1))).evalDistMap I
        (x.numberQueries 0) ρ (f b) s) ^ (2⁻¹ : ℝ) +
      2 * ((k : ℝ≥0∞) * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ) := by
  classical
  let c : ℝ≥0∞ := (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹
  let p (b : Fin (q + 2) → G) :=
    (parallelScheduledRuntime
      (hybridSchedule H (resampleFutureVertices h a b) masks h)).evalDistMap I
        (x.numberQueries 0) ρ (f b) s
  let a' (b : Fin (q + 2) → G) :=
    (parallelScheduledRuntime
      (hybridSchedule H (resampleFutureVertices h a b) masks (h + 1))).evalDistMap I
        (x.numberQueries 0) ρ (f b) s
  let mass (b : Fin (q + 2) → G) :=
    (parallelScheduledRuntime
      (hybridSchedule H (resampleFutureVertices h a b) masks (h + 1))).queryWeight I
      (fun port ↦ parallelInputWeight (D := QReg.of Unit)
        (tailInputs (fun i : Fin (q + 1) ↦ b i.castSucc) (h + 1)) port.2)
      (x.numberQueries 0) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) h
  have hh (b : Fin (q + 2) → G) :
      p b ^ (2⁻¹ : ℝ) ≤ a' b ^ (2⁻¹ : ℝ) + (4 * mass b) ^ (2⁻¹ : ℝ) := by
    simpa only [p, a', mass, tailInputs_resampleFutureVertices] using
      rpow_inv_two_evalDistMap_hybridSchedule_le I H
        (resampleFutureVertices h a b) masks x h ρ (f b) hs
  have hm : ∑ b, c * (4 * mass b) ≤ 4 * ((k : ℝ≥0∞) * ENNReal.ofReal δ) := by
    calc
      _ = 4 * ∑ b, c * mass b := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ ≤ _ := mul_le_mul le_rfl
        (by simpa only [mass, c, tailInputs_resampleFutureVertices] using
          sum_queryWeight_resampleFutureVertices_le I H masks h a k hx ρ δ hδ hS)
        bot_le bot_le
  have havg := rpow_inv_two_tsum_mul_le_of_le_add (fun _ ↦ c) p a'
    (fun b ↦ 4 * mass b) hh
  simp only [tsum_fintype] at havg
  have he : (4 * ((k : ℝ≥0∞) * ENNReal.ofReal δ)) ^ (2⁻¹ : ℝ) =
      2 * ((k : ℝ≥0∞) * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), four_rpow_inv_two]
  exact havg.trans (add_le_add le_rfl
    ((ENNReal.rpow_le_rpow hm (by norm_num)).trans_eq he))

/-- Average an adjacent-hybrid root comparison over the complete unconditional vertex law. -/
theorem sqrt_averageHybridSuccess_le_succ {q : ℕ} (I : L.Interp)
    (adv : OnlineAdversary L G q) (H : G → G) (masks : Fin (q + 1) → G) (h k : ℕ)
    (hk : ∀ p, (adv.run p).IsWidthBound k) (δ : ℝ) (hδ : 0 ≤ δ)
    (hS : ∀ z, ∑ b : Fin (q + 2) → G,
      (tailInputs (fun i : Fin (q + 1) ↦ b i.castSucc) (h + 1)).indicator
        (fun _ ↦ (Fintype.card (Fin (q + 2) → G) : ℝ)⁻¹) z ≤ δ) :
    averageHybridSuccess I adv H masks h ^ (2⁻¹ : ℝ) ≤
      averageHybridSuccess I adv H masks (h + 1) ^ (2⁻¹ : ℝ) +
        2 * ((k : ℝ≥0∞) * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ) := by
  classical
  let : MeasurableSpace G := ⊤
  let c : ℝ≥0∞ := (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹
  let p (a : Fin (q + 2) → G) :=
    ∑ b, c * hybridSuccess I adv H masks h (resampleFutureVertices h a b)
  let a' (a : Fin (q + 2) → G) :=
    ∑ b, c * hybridSuccess I adv H masks (h + 1) (resampleFutureVertices h a b)
  let err : ℝ≥0∞ := 4 * ((k : ℝ≥0∞) * ENNReal.ofReal δ)
  have hcond (a : Fin (q + 2) → G) :
      p a ^ (2⁻¹ : ℝ) ≤ a' a ^ (2⁻¹ : ℝ) + err ^ (2⁻¹ : ℝ) := by
    have hprogram (b : Fin (q + 2) → G) :
        adv.run (resampleFutureVertices h a b 0, masks) = adv.run (a 0, masks) := by
      simp [resampleFutureVertices, resample]
    have hh := sqrt_sum_evalDistMap_resampleFutureVertices_le I H masks h a k
      (x := adv.run (a 0, masks)) (hk (a 0, masks)) adv.initialState δ hδ hS
      (fun b leaf ↦ leaf.2 = resampleFutureVertices h a b (Fin.last (q + 1)))
      (MeasurableSet.singleton True)
    have he : err ^ (2⁻¹ : ℝ) =
        2 * ((k : ℝ≥0∞) * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), four_rpow_inv_two]
    simpa only [p, a', hybridSuccess, hprogram, ← he] using hh
  have havg := rpow_inv_two_tsum_mul_le_of_le_add (fun _ ↦ c) p a' (fun _ ↦ err) hcond
  simp only [tsum_fintype] at havg
  have hp : (∑ a, c * p a) = averageHybridSuccess I adv H masks h :=
    (average_resample (fun i : Fin (q + 2) ↦ i.val ≤ h) (hybridSuccess I adv H masks h)).symm
  have ha : (∑ a, c * a' a) = averageHybridSuccess I adv H masks (h + 1) :=
    (average_resample (fun i : Fin (q + 2) ↦ i.val ≤ h)
      (hybridSuccess I adv H masks (h + 1))).symm
  have he : (∑ _a : Fin (q + 2) → G, c * err) = err := uniform_average_const err
  change (∑ a, c * p a) ^ (2⁻¹ : ℝ) ≤
    (∑ a, c * a' a) ^ (2⁻¹ : ℝ) + (∑ _a : Fin (q + 2) → G, c * err) ^ (2⁻¹ : ℝ)
    at havg
  rw [hp, ha, he] at havg
  have he' : err ^ (2⁻¹ : ℝ) =
      2 * ((k : ℝ≥0∞) * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), four_rpow_inv_two]
  exact havg.trans_eq (by rw [he'])

private theorem le_last_add_sum (p e : ℕ → ℝ≥0∞) (q : ℕ)
    (h : ∀ j < q, p j ≤ p (j + 1) + e j) :
    p 0 ≤ p q + ∑ j ∈ Finset.range q, e j := by
  induction q with
  | zero => simp
  | succ q ih =>
    calc
      p 0 ≤ p q + ∑ j ∈ Finset.range q, e j := ih (fun j hj ↦ h j (by omega))
      _ ≤ (p (q + 1) + e q) + ∑ j ∈ Finset.range q, e j :=
        add_le_add (h q (by omega)) le_rfl
      _ = _ := by rw [Finset.sum_range_succ]; ac_rfl

/-- The complete masked-chain root probability accumulates the width-sensitive per-round
errors before squaring. Its last hybrid is bounded by uniform endpoint guessing. -/
theorem sqrt_averageHybridSuccess_zero_le {q : ℕ} (I : L.Interp)
    (adv : OnlineAdversary L G q) (H : G → G) (masks : Fin (q + 1) → G) (k : ℕ)
    (hq : ∀ p, (adv.run p).IsTotalQueryBound q)
    (hk : ∀ p, (adv.run p).IsWidthBound k) :
    averageHybridSuccess I adv H masks 0 ^ (2⁻¹ : ℝ) ≤
      (Fintype.card G : ℝ≥0∞)⁻¹ ^ (2⁻¹ : ℝ) +
        2 * ∑ h ∈ Finset.range q,
          ((k : ℝ≥0∞) * ((q - h : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ) := by
  let : MeasurableSpace G := ⊤
  have hop (h : ℕ) (hh : h < q) :
      averageHybridSuccess I adv H masks h ^ (2⁻¹ : ℝ) ≤
        averageHybridSuccess I adv H masks (h + 1) ^ (2⁻¹ : ℝ) +
          2 * ((k : ℝ≥0∞) * ((q - h : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ) := by
    have hb := sqrt_averageHybridSuccess_le_succ I adv H masks h k hk
      (((q - h : ℕ) : ℝ) / Fintype.card G) (by positivity) (future_hit_sum_le q h (by omega))
    simpa only [ENNReal.ofReal_div_of_pos (show 0 < (Fintype.card G : ℝ) by positivity),
      ENNReal.ofReal_natCast, mul_div_assoc] using hb
  have ht := le_last_add_sum (fun h ↦ averageHybridSuccess I adv H masks h ^ (2⁻¹ : ℝ))
    (fun h ↦ 2 * ((k : ℝ≥0∞) * ((q - h : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ)) q hop
  exact ht.trans (add_le_add
    (ENNReal.rpow_le_rpow (averageHybridSuccess_last_le I adv H masks hq) (by norm_num)) le_rfl)
    |>.trans_eq (by rw [Finset.mul_sum])

/-- The conditioned mask-first recovery bound with root errors squared only at the end. -/
theorem averageHybridSuccess_zero_le_root {q : ℕ} (I : L.Interp)
    (adv : OnlineAdversary L G q) (H : G → G) (masks : Fin (q + 1) → G) (k : ℕ)
    (hq : ∀ p, (adv.run p).IsTotalQueryBound q)
    (hk : ∀ p, (adv.run p).IsWidthBound k) :
    averageHybridSuccess I adv H masks 0 ≤ rootPatchedRecoveryBound G q k := by
  have hh := sqrt_averageHybridSuccess_zero_le I adv H masks k hq hk
  unfold rootPatchedRecoveryBound
  rw [← ENNReal.rpow_two,
    ← rpow_inv_two_rpow_two (averageHybridSuccess I adv H masks 0)]
  exact ENNReal.rpow_le_rpow hh (by norm_num)

/-- The conditioned root bound scales with the input mass, permitting retained preprocessing
branches to be summed without renormalizing them. -/
theorem averageHybridSuccess_zero_le_root_mul_mass {q : ℕ} (I : L.Interp)
    (adv : OnlineAdversary L G q) (H : G → G) (masks : Fin (q + 1) → G) (k : ℕ)
    (hq : ∀ p, (adv.run p).IsTotalQueryBound q)
    (hk : ∀ p, (adv.run p).IsWidthBound k) :
    averageHybridSuccess I adv H masks 0 ≤
      adv.initialState.mass * rootPatchedRecoveryBound G q k := by
  let normalized : OnlineAdversary L G q :=
    { adv with initialState := adv.initialState.normalize }
  have he : averageHybridSuccess I adv H masks 0 =
      adv.initialState.mass * averageHybridSuccess I normalized H masks 0 := by
    unfold averageHybridSuccess
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro vertices _
    unfold hybridSuccess
    rw [QuantumRuntime.evalDistMap_apply_eq_mass_mul_normalize]
    ring
  rw [he]
  exact mul_le_mul le_rfl (averageHybridSuccess_zero_le_root I normalized H masks k hq hk)
    bot_le bot_le

/-- Endpoint-only masked-chain recovery with root accumulation and one external collision
allowance. One shared random function supplies the challenge and every oracle call. -/
theorem recoveryAdvantage_le_root {q k : ℕ} (I : L.Interp)
    (adv : OnlineAdversary L G q) (hbound : adv.IsQueryBound q k) :
    recoveryAdvantage I adv ≤ min 1 (rootRecoveryBound G q k) := by
  refine le_min (recoveryAdvantage_le_one I adv) ?_
  exact recoveryAdvantage_le_of_patched_bound I adv (rootPatchedRecoveryBound G q k)
    (fun H masks ↦ averageHybridSuccess_zero_le_root I adv H masks k
      (fun p ↦ (hbound p).1) (fun p ↦ (hbound p).2))

end Quantum.MaskedChain
