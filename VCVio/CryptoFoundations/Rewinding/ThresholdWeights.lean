/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.WithoutReplacement.Weighted

/-!
# Weighted work of a threshold attempt

A threshold attempt stops on its first rejection or collects enough accepting challenges.
Its expected work is bounded by the threshold times the average weight in the challenge pool.
-/

public section

open scoped ENNReal NNReal
open MeasureTheory

namespace ProbComp

variable {S : Type}

/-- All challenges inspected by a threshold attempt. The first rejection ends the attempt;
a first acceptance starts sampling the remaining pool without replacement. -/
@[expose] noncomputable def thresholdDraws (accept : S → Bool) : ℕ → List S → ProbComp (List S)
  | 0, _ => pure []
  | _ + 1, [] => pure []
  | r + 1, x :: xs => do
      let i ← uniformFin xs.length
      let y := (x :: xs)[(i : ℕ)]'(by simpa using i.isLt)
      if accept y then
        (y :: ·) <$> drawUntil accept r ((x :: xs).eraseIdx i)
      else pure [y]

@[simp] theorem thresholdDraws_zero (accept : S → Bool) (l : List S) :
    thresholdDraws accept 0 l = pure [] := by rw [thresholdDraws]

@[simp] theorem thresholdDraws_nil (accept : S → Bool) (r : ℕ) :
    thresholdDraws accept r [] = pure [] := by cases r <;> rw [thresholdDraws]

theorem thresholdDraws_cons (accept : S → Bool) (r : ℕ) (x : S) (xs : List S) :
    thresholdDraws accept (r + 1) (x :: xs) = (do
      let i ← uniformFin xs.length
      let y := (x :: xs)[(i : ℕ)]'(by simpa using i.isLt)
      if accept y then
        (y :: ·) <$> drawUntil accept r ((x :: xs).eraseIdx i)
      else pure [y]) := by rw [thresholdDraws]

/-- The expected work of the threshold attempt's first draw and continuation. -/
@[expose] noncomputable def thresholdWeight (accept : S → Bool) (w : S → ℝ≥0) :
    ℕ → List S → ℝ≥0
  | 0, _ => 0
  | _ + 1, [] => 0
  | r + 1, x :: xs =>
      (∑ i : Fin (xs.length + 1),
        let y := (x :: xs)[(i : ℕ)]'(by simpa using i.isLt)
        w y + if accept y then drawWeight accept w r ((x :: xs).eraseIdx i) else 0) /
          (xs.length + 1)

/-- The finite first-draw decomposition computes the weighted integral of the threshold attempt.
-/
theorem lintegral_listWeight_thresholdDraws (accept : S → Bool) (w : S → ℝ≥0)
    (k : ℕ) (l : List S) :
    (∫⁻ t, (t : ENNReal) ∂𝒟[listWeight w <$> thresholdDraws accept k l]) =
      (thresholdWeight accept w k l : ENNReal) := by
  cases k with
  | zero => simp [thresholdWeight]
  | succ r =>
    cases l with
    | nil => simp [thresholdWeight]
    | cons x xs =>
      have hstep : ∀ i : Fin (xs.length + 1),
          (∫⁻ t, (t : ENNReal) ∂𝒟[listWeight w <$>
            (if accept (x :: xs)[(i : ℕ)] then
              ((x :: xs)[(i : ℕ)] :: ·) <$>
                drawUntil accept r ((x :: xs).eraseIdx i)
            else pure [(x :: xs)[(i : ℕ)]] : ProbComp (List S))]) =
          (w (x :: xs)[(i : ℕ)] + if accept (x :: xs)[(i : ℕ)] then
            drawWeight accept w r ((x :: xs).eraseIdx i) else 0 : ℝ≥0) := by
        intro i
        split
        · have hmap : listWeight w <$> (((x :: xs)[(i : ℕ)] :: ·) <$>
              drawUntil accept r ((x :: xs).eraseIdx i)) =
            (fun a : ℝ≥0 => w (x :: xs)[(i : ℕ)] + a) <$>
              (listWeight w <$> drawUntil accept r ((x :: xs).eraseIdx i)) := by
            simp only [Functor.map_map, listWeight_cons]
          rw [hmap, lintegral_evalDist_map _
            (f := fun a : ℝ≥0 => w (x :: xs)[(i : ℕ)] + a)
            (g := fun a : ℝ≥0 => (a : ENNReal))
            (measurable_const.add measurable_id) measurable_coe_nnreal_ennreal]
          simp only [ENNReal.coe_add]
          rw [lintegral_add_left measurable_const _, lintegral_const,
            measure_univ, mul_one, lintegral_listWeight_drawUntil accept w _ _ _ rfl]
        · simp
      rw [thresholdDraws_cons, map_bind,
        lintegral_evalDist_bind_of_discrete _ _ measurable_coe_nnreal_ennreal]
      simp only [hstep]
      rw [lintegral_evalDist_uniformFin, thresholdWeight]
      simp

/-- A threshold attempt's weighted expected work is bounded unconditionally by the threshold
multiplied by the pool's average weight. -/
theorem thresholdWeight_le (accept : S → Bool) (w : S → ℝ≥0) (k : ℕ) (l : List S) :
    thresholdWeight accept w k l ≤ (k : ℝ≥0) * listWeight w l / l.length := by
  cases k with
  | zero => simp [thresholdWeight]
  | succ r =>
    cases l with
    | nil => simp [thresholdWeight]
    | cons x xs =>
      rw [thresholdWeight]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      apply (div_le_div_iff_of_pos_right (by positivity : (xs.length + 1 : ℝ≥0) > 0)).2
      have hs := sum_fin_listWeight w (x :: xs)
      change (∑ i : Fin (xs.length + 1), w (x :: xs)[(i : ℕ)]) = _ at hs
      rw [Finset.sum_add_distrib, hs]
      by_cases hr : r + 1 ≤ (x :: xs).countP accept
      · have hstep : ∀ i : Fin (xs.length + 1),
            (if accept (x :: xs)[(i : ℕ)] then
              drawWeight accept w r ((x :: xs).eraseIdx i) else 0) =
            (if accept (x :: xs)[(i : ℕ)] then
              (r : ℝ≥0) / ((x :: xs).countP accept - 1 : ℕ) *
                listWeight (fun y => if accept y then w y else 0) ((x :: xs).eraseIdx i) +
              (r : ℝ≥0) / (x :: xs).countP accept *
                listWeight (fun y => if !accept y then w y else 0) ((x :: xs).eraseIdx i)
            else 0) := by
          intro i
          split
          · rename_i ha
            have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
            have hc := List.countP_eraseIdx_of_pos hi ha
            have hc' : ((x :: xs).eraseIdx i).countP accept =
                (x :: xs).countP accept - 1 := by omega
            rw [drawWeight_eq accept w _ r _ rfl (by omega), hc']
            have hcast : (((((x :: xs).countP accept - 1 : ℕ) : ℝ≥0)) + 1) =
                ((x :: xs).countP accept : ℝ≥0) := by
              exact_mod_cast (show (x :: xs).countP accept - 1 + 1 =
                (x :: xs).countP accept by omega)
            rw [hcast]
          · rfl
        simp only [hstep]
        have he := sum_fin_weighted_eraseIdx accept w (x :: xs)
          ((r : ℝ≥0) / ((x :: xs).countP accept - 1 : ℕ))
          ((r : ℝ≥0) / (x :: xs).countP accept) 0 0
        simp only [zero_mul, add_zero] at he
        dsimp only [List.length_cons] at he
        rw [he]
        have hG : ((x :: xs).countP accept : ℝ≥0) ≠ 0 := by
          exact_mod_cast (show (x :: xs).countP accept ≠ 0 by omega)
        have hcancel : (r : ℝ≥0) / (((x :: xs).countP accept - 1 : ℕ) : ℝ≥0) *
            (((x :: xs).countP accept - 1 : ℕ) : ℝ≥0) = r := by
          by_cases hz : (x :: xs).countP accept - 1 = 0
          · have : r = 0 := by omega
            simp [this]
          · exact div_mul_cancel₀ _ (by exact_mod_cast hz)
        rw [hcancel, div_mul_cancel₀ _ hG, listWeight_eq_ite_add_not accept w (x :: xs)]
        exact le_of_eq (by ring)
      · have hbound : (∑ i : Fin (xs.length + 1),
            if accept (x :: xs)[(i : ℕ)] then
              drawWeight accept w r ((x :: xs).eraseIdx i) else 0) ≤
            (∑ i : Fin (xs.length + 1), if accept (x :: xs)[(i : ℕ)] then
              listWeight w ((x :: xs).eraseIdx i) else 0) := by
          apply Finset.sum_le_sum
          intro i _
          split
          · exact drawWeight_le accept w _ r _ rfl
          · rfl
        apply le_trans (add_le_add le_rfl hbound) _
        have he := sum_ite_listWeight_eraseIdx accept w (x :: xs)
        dsimp only [List.length_cons] at he
        have hg : ((x :: xs).countP accept + 1 : ℝ≥0) ≤ r + 1 := by
          exact_mod_cast (show (x :: xs).countP accept + 1 ≤ r + 1 by omega)
        calc
          _ ≤ listWeight w (x :: xs) +
              (((x :: xs).countP accept : ℝ≥0) * listWeight w (x :: xs)) := by
            exact add_le_add le_rfl (le_trans (le_add_of_nonneg_right zero_le) (le_of_eq he))
          _ = (((x :: xs).countP accept : ℝ≥0) + 1) * listWeight w (x :: xs) := by ring
          _ ≤ _ := mul_le_mul' hg le_rfl

/-- The threshold attempt inspects at most `k` times the average pool weight in expectation,
including unsuccessful attempts. -/
theorem lintegral_listWeight_thresholdDraws_le (accept : S → Bool) (w : S → ℝ≥0)
    (k : ℕ) (l : List S) :
    (∫⁻ t, (t : ENNReal) ∂𝒟[listWeight w <$> thresholdDraws accept k l]) ≤
      (k : ENNReal) * (listWeight w l : ENNReal) / l.length := by
  rw [lintegral_listWeight_thresholdDraws]
  calc
    _ ≤ (((k : ℝ≥0) * listWeight w l / l.length : ℝ≥0) : ENNReal) :=
      ENNReal.coe_le_coe.mpr (thresholdWeight_le accept w k l)
    _ ≤ _ := by simpa using
      (ENNReal.coe_div_le (p := (k : ℝ≥0) * listWeight w l) (r := l.length))

/-- An unconditional threshold bound for natural work attached to each inspected challenge. -/
theorem lintegral_sum_nat_thresholdDraws_le (accept : S → Bool) (w : S → ℕ)
    (k : ℕ) (l : List S) :
    (∫⁻ t, (t : ENNReal) ∂𝒟[(fun d => ((d.map w).sum : ℕ)) <$> thresholdDraws accept k l]) ≤
      (k : ENNReal) * (((l.map w).sum : ℕ) : ENNReal) / l.length := by
  have hmap : listWeight (fun x => (w x : ℝ≥0)) <$> thresholdDraws accept k l =
      (fun n : ℕ => (n : ℝ≥0)) <$>
        ((fun d => ((d.map w).sum : ℕ)) <$> thresholdDraws accept k l) := by
    rw [Functor.map_map]
    congr 1
    funext d
    exact listWeight_natCast w d
  have h := lintegral_listWeight_thresholdDraws_le accept (fun x => (w x : ℝ≥0)) k l
  rw [hmap, lintegral_evalDist_map _ Measurable.of_discrete
    measurable_coe_nnreal_ennreal] at h
  simp only [listWeight_natCast, ENNReal.coe_natCast] at h
  exact h

end ProbComp
