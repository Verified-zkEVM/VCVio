/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.MaskedChain.Hybrid

/-!
# Endpoint recovery bounds for idealized masked chains

`recoveryAdvantage_le` bounds an online adversary's probability of recovering the last vertex
of a `q + 1`-link masked chain in at most `q` adaptive rounds of width at most `k`. The bound
is `min 1 (recoveryBound G q k)`: a uniform-guessing term, a vertex-collision term, and a sum
of single-round hybrid errors of order `sqrt(kq³ / |G|)`.

The actual experiment samples one oracle and a complete hidden vertex tuple. That same oracle
supplies the public masks and every online answer. The event compares only the adversary's
output with the hidden endpoint; the tuple remains joint with the output throughout the proof.
The initial state and online program family are fixed before sampling. Oracle preprocessing
and the exact `PointerChainPuzzle` encoding are outside this theorem's scope.

Resampling vertices beyond a round's known prefix preserves the full joint challenge law.
Earlier scheduled calls depend only on the retained prefix, so their current query state is
independent of the fresh future inputs. Averaging their incidence bounds each hybrid error;
in the final hybrid, the endpoint is fresh. The classical coupling charges repeated hidden
vertices to the explicit collision term, without assuming that all inputs are distinct.

## References

* Afshar et al., *On the (Im)possibility of Time-Lock Puzzles in the Quantum Random Oracle
  Model*, Asiacrypt 2023, §5, Theorem 5.3 and Lemmas 5.4–5.5. The hybrid comparison here
  retains the hidden endpoint jointly with the quantum output and observes endpoint recovery.
-/

public section
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal Kronecker ComplexOrder
namespace Quantum.MaskedChain
universe u v w
variable {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G]
 {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}
/-- Retain the known prefix through index `h`, independently resampling all later vertices. -/
@[expose]
def resampleFutureVertices {q : ℕ} (h : ℕ) (a b : Fin (q + 2) → G) : Fin (q + 2) → G :=
  resample (fun i ↦ i.val ≤ h) a b

omit [Fintype G] [DecidableEq G] [AddCommGroup G] in
/-- Every input after the known prefix comes from the fresh table. -/
theorem tailInputs_resampleFutureVertices {q : ℕ} (h : ℕ) (a b : Fin (q + 2) → G) :
    tailInputs (fun i : Fin (q + 1) ↦ resampleFutureVertices h a b i.castSucc) (h + 1) =
      tailInputs (fun i : Fin (q + 1) ↦ b i.castSucc) (h + 1) := by
  ext z
  simp only [tailInputs, Set.mem_ofPred_eq]
  apply exists_congr
  intro i
  constructor
  · rintro ⟨hi, he⟩
    exact ⟨hi, by simpa [resampleFutureVertices, resample, show ¬ i.val ≤ h by omega] using he⟩
  · rintro ⟨hi, he⟩
    exact ⟨hi, by simpa [resampleFutureVertices, resample, show ¬ i.val ≤ h by omega] using he⟩

/-- The query state before round `h` is unchanged by resampling its unknown future.
The disagreement projector still retains the fresh table as its index. -/
theorem queryWeight_resampleFutureVertices {q : ℕ} (I : L.Interp) (H : G → G)
    (masks : Fin (q + 1) → G)
    (h : ℕ) (a b : Fin (q + 2) → G) (x : QuantumComp L (qromBatchSpec G G) W A)
    (ρ : Matrix (A × QReg.of Unit) (A × QReg.of Unit) ℂ) :
    (parallelScheduledRuntime
      (hybridSchedule H (resampleFutureVertices h a b) masks (h + 1))).queryWeight I
        (fun p ↦ parallelInputWeight (D := QReg.of Unit)
          (tailInputs (fun i : Fin (q + 1) ↦ resampleFutureVertices h a b i.castSucc) (h + 1)) p.2)
        (x.numberQueries 0) ρ h =
      (parallelScheduledRuntime (hybridSchedule H a masks (h + 1))).queryWeight I
        (fun p ↦ parallelInputWeight (D := QReg.of Unit)
          (tailInputs (fun i : Fin (q + 1) ↦ b i.castSucc) (h + 1)) p.2)
        (x.numberQueries 0) ρ h := by
  rw [tailInputs_resampleFutureVertices]
  apply queryWeight_hybridSchedule_eq_of_vertices_prefix
  intro i hi
  simp [resampleFutureVertices, resample, hi]

/-- A conditional expected query-weight bound from future-input incidence. All prior
quantum computation is retained; only the independent future vertices are averaged. -/
theorem sum_queryWeight_resampleFutureVertices_le {q : ℕ} (I : L.Interp) (H : G → G)
    (masks : Fin (q + 1) → G) (h : ℕ) (a : Fin (q + 2) → G)
    (k : ℕ) {x : QuantumComp L (qromBatchSpec G G) W A} (hx : x.IsWidthBound k)
    (ρ : SubState A) (δ : ℝ) (hδ : 0 ≤ δ)
    (hS : ∀ z, ∑ b : Fin (q + 2) → G,
      (tailInputs (fun i : Fin (q + 1) ↦ b i.castSucc) (h + 1)).indicator
        (fun _ ↦ (Fintype.card (Fin (q + 2) → G) : ℝ)⁻¹) z ≤ δ) :
    ∑ b : Fin (q + 2) → G, (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
      (parallelScheduledRuntime
        (hybridSchedule H (resampleFutureVertices h a b) masks (h + 1))).queryWeight I
        (fun p ↦ parallelInputWeight (D := QReg.of Unit)
          (tailInputs (fun i : Fin (q + 1) ↦ resampleFutureVertices h a b i.castSucc) (h + 1)) p.2)
        (x.numberQueries 0) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) h ≤
      (k : ℝ≥0∞) * ENNReal.ofReal δ := by
  simp_rw [queryWeight_resampleFutureVertices]
  have hc : ENNReal.ofReal ((Fintype.card (Fin (q + 2) → G) : ℝ)⁻¹) =
      (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
  simpa only [hc, SubState.matrix_prod] using
    sum_mul_queryWeight_parallelInputWeight_numberQueries_le
    (parallelScheduledRuntime (hybridSchedule H a masks (h + 1))) I
    (fun _ : Fin (q + 2) → G ↦ (Fintype.card (Fin (q + 2) → G) : ℝ)⁻¹)
    (by intro b; positivity)
    (fun b ↦ tailInputs (fun i : Fin (q + 1) ↦ b i.castSucc) (h + 1))
    δ hδ hS k hx (ρ.prod (SubState.basis ())) 0 h
private theorem four_rpow_inv_two : (4 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 2 := by
  apply ENNReal.rpow_left_injective (show (2 : ℝ) ≠ 0 by norm_num)
  change ((4 : ℝ≥0∞) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = (2 : ℝ≥0∞) ^ (2 : ℝ)
  rw [rpow_inv_two_rpow_two, ENNReal.rpow_two]
  norm_num

/-- Averaged one-round event comparison after independently resampling future vertices.
The final observation may depend on the full fresh table, including its endpoint. -/
theorem sum_evalDistMap_resampleFutureVertices_le {q : ℕ} (I : L.Interp) (H : G → G)
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
        (x.numberQueries 0) ρ (f b) s) ≤
    (∑ b : Fin (q + 2) → G, (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
      (parallelScheduledRuntime
        (hybridSchedule H (resampleFutureVertices h a b) masks (h + 1))).evalDistMap I
        (x.numberQueries 0) ρ (f b) s) + 4 * ((k : ℝ≥0∞) * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ) := by
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
  let m (b : Fin (q + 2) → G) :=
    (parallelScheduledRuntime
      (hybridSchedule H (resampleFutureVertices h a b) masks (h + 1))).queryWeight I
      (fun z ↦ parallelInputWeight (D := QReg.of Unit)
        (tailInputs (fun i : Fin (q + 1) ↦ resampleFutureVertices h a b i.castSucc) (h + 1)) z.2)
      (x.numberQueries 0) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) h
  have hm : c * ∑ b, m b ≤ (k : ℝ≥0∞) * ENNReal.ofReal δ := by
    simpa only [Finset.mul_sum] using
      sum_queryWeight_resampleFutureVertices_le I H masks h a k hx ρ δ hδ hS
  change (∑ b, c * p b) ≤ (∑ b, c * a' b) + _
  calc
    _ ≤ ∑ b, c * (a' b + 2 * (4 * m b) ^ (2⁻¹ : ℝ)) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul le_rfl
        (evalDistMap_hybridSchedule_le I H (resampleFutureVertices h a b) masks x h ρ (f b) hs)
        bot_le bot_le
    _ = (∑ b, c * a' b) + 2 * (c * ∑ b, (4 * m b) ^ (2⁻¹ : ℝ)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ (∑ b, c * a' b) + 2 * (c * ∑ b, 4 * m b) ^ (2⁻¹ : ℝ) := by
      gcongr
      exact average_rpow_inv_two_le (fun b ↦ 4 * m b)
    _ ≤ (∑ b, c * a' b) + 2 * (4 * ((k : ℝ≥0∞) * ENNReal.ofReal δ)) ^ (2⁻¹ : ℝ) := by
      apply add_le_add le_rfl
      apply mul_le_mul le_rfl _ bot_le bot_le
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      calc
        c * ∑ b, 4 * m b = 4 * (c * ∑ b, m b) := by
          rw [← Finset.mul_sum]
          ring
        _ ≤ _ := mul_le_mul le_rfl hm bot_le bot_le
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), four_rpow_inv_two]
      ring

/-! ## Complete challenge averages -/

/-- Endpoint success in one scheduled hybrid, with the complete hidden tuple fixed. -/
@[expose]
noncomputable def hybridSuccess {q : ℕ} (I : L.Interp) (adv : OnlineAdversary L G q)
    (H : G → G) (masks : Fin (q + 1) → G) (cutoff : ℕ) (vertices : Fin (q + 2) → G) : ℝ≥0∞ :=
  (parallelScheduledRuntime (hybridSchedule H vertices masks cutoff)).evalDistMap I
    ((adv.run (vertices 0, masks)).numberQueries 0) adv.initialState
    (fun leaf ↦ leaf.2 = vertices (Fin.last (q + 1))) {True}

/-- Uniform vertex average of a scheduled hybrid, retaining the endpoint in the observer. -/
@[expose]
noncomputable def averageHybridSuccess {q : ℕ} (I : L.Interp) (adv : OnlineAdversary L G q)
    (H : G → G) (masks : Fin (q + 1) → G) (cutoff : ℕ) : ℝ≥0∞ :=
  ∑ vertices, (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
    hybridSuccess I adv H masks cutoff vertices

/-- One adjacent-hybrid comparison after averaging the full hidden vertex tuple. -/
theorem averageHybridSuccess_le_succ {q : ℕ} (I : L.Interp) (adv : OnlineAdversary L G q)
    (H : G → G) (masks : Fin (q + 1) → G) (h k : ℕ)
    (hk : ∀ p, (adv.run p).IsWidthBound k) (δ : ℝ) (hδ : 0 ≤ δ)
    (hS : ∀ z, ∑ b : Fin (q + 2) → G,
      (tailInputs (fun i : Fin (q + 1) ↦ b i.castSucc) (h + 1)).indicator
        (fun _ ↦ (Fintype.card (Fin (q + 2) → G) : ℝ)⁻¹) z ≤ δ) :
    averageHybridSuccess I adv H masks h ≤ averageHybridSuccess I adv H masks (h + 1) +
      4 * ((k : ℝ≥0∞) * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ) := by
  let : MeasurableSpace G := ⊤
  let c : ℝ≥0∞ := (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹
  let cost := 4 * ((k : ℝ≥0∞) * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ)
  have hh (a : Fin (q + 2) → G) :
      (∑ b, c * hybridSuccess I adv H masks h (resampleFutureVertices h a b)) ≤
        (∑ b, c * hybridSuccess I adv H masks (h + 1) (resampleFutureVertices h a b)) + cost := by
    have hprogram (b : Fin (q + 2) → G) :
        adv.run (resampleFutureVertices h a b 0, masks) = adv.run (a 0, masks) := by
      simp [resampleFutureVertices, resample]
    simpa only [hybridSuccess, hprogram] using
      sum_evalDistMap_resampleFutureVertices_le I H masks h a k
      (x := adv.run (a 0, masks)) (hk (a 0, masks)) adv.initialState δ hδ hS
      (fun b leaf ↦ leaf.2 = resampleFutureVertices h a b (Fin.last (q + 1)))
      (MeasurableSet.singleton True)
  have hc : c * (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  calc
    _ = ∑ a, c * ∑ b, c * hybridSuccess I adv H masks h (resampleFutureVertices h a b) :=
      average_resample (fun i : Fin (q + 2) ↦ i.val ≤ h) (hybridSuccess I adv H masks h)
    _ ≤ ∑ a, c * ((∑ b, c * hybridSuccess I adv H masks (h + 1)
        (resampleFutureVertices h a b)) + cost) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul le_rfl (hh a) bot_le bot_le
    _ = (∑ a, c * ∑ b, c * hybridSuccess I adv H masks (h + 1)
        (resampleFutureVertices h a b)) + cost := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, mul_comm (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞) c, hc, one_mul]
    _ = _ := congrArg (fun z ↦ z + cost)
      (average_resample (fun i : Fin (q + 2) ↦ i.val ≤ h)
        (hybridSuccess I adv H masks (h + 1))).symm

private theorem le_last_add_sum (p c : ℕ → ℝ≥0∞) (n : ℕ)
    (h : ∀ i < n, p i ≤ p (i + 1) + c i) :
    p 0 ≤ p n + ∑ i ∈ Finset.range n, c i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      p 0 ≤ p n + ∑ i ∈ Finset.range n, c i := ih (fun i hi ↦ h i (by omega))
      _ ≤ (p (n + 1) + c n) + ∑ i ∈ Finset.range n, c i :=
        add_le_add (h n (by omega)) le_rfl
      _ = _ := by rw [Finset.sum_range_succ]; ac_rfl

/-- Sum the width-sensitive hybrid errors through the final cutoff. -/
theorem averageHybridSuccess_le_last {q : ℕ} (I : L.Interp)
    (adv : OnlineAdversary L G q) (H : G → G) (masks : Fin (q + 1) → G) (k : ℕ)
    (hk : ∀ p, (adv.run p).IsWidthBound k) :
    averageHybridSuccess I adv H masks 0 ≤ averageHybridSuccess I adv H masks q +
      4 * ∑ h ∈ Finset.range q,
        ((k : ℝ≥0∞) * ((q - h : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ) := by
  let : MeasurableSpace G := ⊤
  have hop (h : ℕ) (hh : h < q) :
      averageHybridSuccess I adv H masks h ≤ averageHybridSuccess I adv H masks (h + 1) +
        4 * ((k : ℝ≥0∞) * ((q - h : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ) := by
    have hb := averageHybridSuccess_le_succ I adv H masks h k hk
      (((q - h : ℕ) : ℝ) / Fintype.card G) (by positivity)
      (future_hit_sum_le q h (by omega))
    simpa only [ENNReal.ofReal_div_of_pos (show 0 < (Fintype.card G : ℝ) by positivity),
      ENNReal.ofReal_natCast, mul_div_assoc] using hb
  have ht := le_last_add_sum (averageHybridSuccess I adv H masks)
    (fun h ↦ 4 * ((k : ℝ≥0∞) * ((q - h : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ)) q hop
  simpa only [Finset.mul_sum] using ht

/-! ## Fresh endpoint -/

omit [DecidableEq G] in
private theorem freshCoordinateGuess
    {spec : QuantumOracleSpec.{0, 0}} {T : Type} [Fintype T] [DecidableEq T]
    (R : QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A)
    (guess : (Σ B, W B) → G) (t : T) :
    ∑ b : T → G, (Fintype.card (T → G) : ℝ≥0∞)⁻¹ *
      R.evalDistMap I x ρ (fun leaf ↦ guess leaf = b t) {True} ≤
        (Fintype.card G : ℝ≥0∞)⁻¹ := by
  classical
  have hm : ∑' p, ENNReal.ofReal (R.jointPost I x ρ p).matrix.trace.re ≤ 1 := by
    have h := measure_univ_le (R.evalDistMap I x ρ (fun _ ↦ ()))
    rw [R.evalDistMap_apply I x ρ (fun _ ↦ ()) MeasurableSet.univ] at h
    simpa only [Set.indicator_univ, Pi.one_apply, mul_one] using h
  simp only [QuantumRuntime.evalDistMap_apply _ _ _ _ _
    (MeasurableSet.singleton True)]
  rw [Quantum.sum_tsum_guess]
  simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul hm (le_rfl : (Fintype.card G : ℝ≥0∞)⁻¹ ≤ (Fintype.card G : ℝ≥0∞)⁻¹)
      bot_le bot_le

/-- With at most `q` calls, the final hybrid leaves the endpoint uniformly fresh. -/
theorem averageHybridSuccess_last_le {q : ℕ} (I : L.Interp) (adv : OnlineAdversary L G q)
    (H : G → G) (masks : Fin (q + 1) → G)
    (hq : ∀ p, (adv.run p).IsTotalQueryBound q) :
    averageHybridSuccess I adv H masks q ≤
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace G := ⊤
  let c : ℝ≥0∞ := (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹
  let p (vertices : Fin (q + 2) → G) :=
    (parallelScheduledRuntime (hybridSchedule H vertices masks q)).evalDistMap I
      ((adv.run (vertices 0, masks)).numberQueries 0) adv.initialState
      (fun leaf ↦ leaf.2 = vertices (Fin.last (q + 1))) {True}
  change (∑ vertices, c * p vertices) ≤ _
  rw [average_resample (fun i : Fin (q + 2) ↦ i ≠ Fin.last (q + 1)) p]
  have hi (a : Fin (q + 2) → G) :
      (∑ b, c * p (resample (fun i : Fin (q + 2) ↦ i ≠ Fin.last (q + 1)) a b)) ≤
        (Fintype.card G : ℝ≥0∞)⁻¹ := by
    have hp (b : Fin (q + 2) → G) :
        p (resample (fun i : Fin (q + 2) ↦ i ≠ Fin.last (q + 1)) a b) =
          (parallelScheduledRuntime (hybridSchedule H a masks q)).evalDistMap I
            ((adv.run (a 0, masks)).numberQueries 0) adv.initialState
            (fun leaf ↦ leaf.2 = b (Fin.last (q + 1))) {True} := by
      have ht : resample (fun i : Fin (q + 2) ↦ i ≠ Fin.last (q + 1)) a b =
          Function.update a (Fin.last (q + 1)) (b (Fin.last (q + 1))) := by
        funext i
        by_cases h : i = Fin.last (q + 1) <;> simp [resample, h]
      have h0 : (0 : Fin (q + 2)) ≠ Fin.last (q + 1) := by
        simp [Fin.ext_iff]
      have hr := run_hybridSchedule_last_update I H masks a (b (Fin.last (q + 1)))
        (hq (a 0, masks))
      simp only [p, ht, Function.update_of_ne h0, Function.update_self,
        QuantumRuntime.evalDistMap, QuantumRuntime.matrix_jointPost]
      rw [← hr]
    simp_rw [hp]
    exact freshCoordinateGuess
      (spec := (qromBatchSpec G G).numbered) (W := fun _ ↦ G)
      (T := Fin (q + 2))
      (parallelScheduledRuntime (hybridSchedule H a masks q)) I
      ((adv.run (a 0, masks)).numberQueries 0) adv.initialState
      (fun leaf ↦ leaf.2) (Fin.last (q + 1))
  calc
    _ ≤ ∑ _a : Fin (q + 2) → G, c * (Fintype.card G : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul le_rfl (hi a) bot_le bot_le
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _), one_mul]

/-! ## Coupling to the real challenge -/

private theorem average_eq_lintegral {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Fintype Ω] (f : Ω → ℝ≥0∞) :
    (∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * f ω) =
      ∫⁻ ω, f ω ∂(uniformOn Set.univ : Measure Ω) := by
  rw [lintegral_uniformOn_univ, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  exact mul_comm _ _

private theorem game_le_of_patched_bound {q : ℕ} (I : L.Interp)
    (adv : OnlineAdversary L G q) (B : ℝ≥0∞)
    (hB : ∀ H masks,
      (∑ vertices : Fin (q + 2) → G,
        (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
          (parallelScheduledRuntime (hybridSchedule H vertices masks 0)).evalDistMap I
            ((adv.run (vertices 0, masks)).numberQueries 0) adv.initialState
            (fun leaf ↦ leaf.2 = vertices (Fin.last (q + 1))) {True}) ≤ B) :
    recoveryAdvantage I adv ≤ B + (((q + 2).choose 2 : ℕ) : ℝ≥0∞) / Fintype.card G := by
  classical
  let : MeasurableSpace G := ⊤
  let F (H : G → G) (xs : Fin (q + 2) → G) (masks : Fin (q + 1) → G) :=
    (parallelOracleRuntime H).evalDistMap I (adv.run (xs 0, masks)) adv.initialState
      (fun leaf ↦ leaf.2 = xs (Fin.last (q + 1))) {True}
  have hF (H : G → G) (xs : Fin (q + 2) → G) (masks : Fin (q + 1) → G) :
      F H xs masks ≤ 1 := measure_le_one _ _
  have hc := real_le_maskFirst_add_collision (q + 1) F hF
  have hreal : recoveryAdvantage I adv =
      ∫⁻ xs, ∫⁻ H, F H xs (oracleMasks H xs)
        ∂(uniformOn Set.univ : Measure (G → G))
        ∂(uniformOn Set.univ : Measure (Fin (q + 2) → G)) := by
    rw [recoveryAdvantage_eq_sum]
    simp_rw [average_eq_lintegral]
    exact lintegral_lintegral_swap Measurable.of_discrete.aemeasurable
  rw [hreal]
  refine hc.trans (add_le_add ?_ le_rfl)
  rw [lintegral_lintegral_swap Measurable.of_discrete.aemeasurable]
  calc
    _ ≤ ∫⁻ _H : G → G, ∫⁻ _masks : Fin (q + 1) → G, B
        ∂(uniformOn Set.univ : Measure (Fin (q + 1) → G))
        ∂(uniformOn Set.univ : Measure (G → G)) := by
      apply lintegral_mono
      intro H
      dsimp only
      rw [lintegral_lintegral_swap Measurable.of_discrete.aemeasurable]
      apply lintegral_mono
      intro masks
      have h := hB H masks
      rw [average_eq_lintegral] at h
      convert h using 1
      apply lintegral_congr
      intro xs
      have hs : hybridSchedule H xs masks 0 = fun _ ↦ fullOracle H xs masks := by
        funext j
        simp [hybridSchedule]
      rw [hs, evalDistMap_parallelScheduledRuntime_const]
      rfl
    _ = B := by simp

/-! ## Endpoint recovery bound -/

/-- Guessing, collision, and hybrid errors for a `q + 1`-link chain attacked in `q` rounds.
The hybrid term is at most `4q * sqrt(kq / |G|)`, so its order is `sqrt(kq³ / |G|)`.
The collision term permits repeated hidden vertices without a distinctness assumption. -/
@[expose]
noncomputable def recoveryBound (G : Type) [Fintype G] (q k : ℕ) : ℝ≥0∞ :=
  (Fintype.card G : ℝ≥0∞)⁻¹ + (((q + 2).choose 2 : ℕ) : ℝ≥0∞) / Fintype.card G +
    4 * ∑ h ∈ Finset.range q,
      ((k : ℝ≥0∞) * ((q - h : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ)

/-- Endpoint-only sequentiality of the idealized masked chain without oracle preprocessing.
The oracle, the complete hidden tuple, the public challenge and the endpoint check remain
joint throughout the comparison. Online calls are adaptive and have variable width at most
`k`; zero-width calls and subnormalized initial states are allowed. -/
theorem recoveryAdvantage_le {q k : ℕ} (I : L.Interp) (adv : OnlineAdversary L G q)
    (hbound : adv.IsQueryBound q k) :
    recoveryAdvantage I adv ≤ min 1 (recoveryBound G q k) := by
  refine le_min (recoveryAdvantage_le_one I adv) ?_
  calc
    _ ≤ ((Fintype.card G : ℝ≥0∞)⁻¹ +
          4 * ∑ h ∈ Finset.range q,
            ((k : ℝ≥0∞) * ((q - h : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ)) +
        (((q + 2).choose 2 : ℕ) : ℝ≥0∞) / Fintype.card G := by
      apply game_le_of_patched_bound I adv
      intro H masks
      change averageHybridSuccess I adv H masks 0 ≤ _
      exact (averageHybridSuccess_le_last I adv H masks k (fun p ↦ (hbound p).2)).trans
        (add_le_add (averageHybridSuccess_last_le I adv H masks (fun p ↦ (hbound p).1))
          le_rfl)
    _ = _ := by unfold recoveryBound; ac_rfl

end Quantum.MaskedChain
