/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.WithoutReplacement.Basic
import ToMathlib.Data.List.Count

/-!
# Weighted sampling without replacement

Finite nonnegative weights measure the cost of each sampled list position. The expected total
weight of draws until enough successes is bounded by the corresponding weighted recurrence.
-/

public section

open scoped ENNReal NNReal
open MeasureTheory

namespace ProbComp

variable {S : Type}

/-- The sum of the weights in a list, counting each position separately. -/
@[expose] def listWeight (w : S → ℝ≥0) (l : List S) : ℝ≥0 := (l.map w).sum

@[simp] theorem listWeight_nil (w : S → ℝ≥0) : listWeight w [] = 0 := rfl

@[simp] theorem listWeight_cons (w : S → ℝ≥0) (x : S) (l : List S) :
    listWeight w (x :: l) = w x + listWeight w l := rfl

/-- Removing a position removes exactly its weight. -/
theorem listWeight_eraseIdx_add (w : S → ℝ≥0) (l : List S) (i : ℕ)
    (hi : i < l.length) : listWeight w (l.eraseIdx i) + w l[i] = listWeight w l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => simp [add_comm]
      | succ i =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
        simpa only [List.eraseIdx_cons_succ, listWeight_cons, List.getElem_cons_succ,
          add_assoc] using congrArg (w x + ·) (ih i hi)

/-- Integrating over positions sums the list's weights. -/
theorem sum_fin_listWeight (w : S → ℝ≥0) (l : List S) :
    (∑ i : Fin l.length, w l[(i : ℕ)]) = listWeight w l := by
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]
  rfl

/-- A constant at the positions satisfying a Boolean predicate contributes its count. -/
theorem sum_fin_ite_countP (p : S → Bool) (l : List S) (a : ℝ≥0) :
    (∑ i : Fin l.length, if p l[(i : ℕ)] then a else 0) = l.countP p * a := by
  have hc : (∑ i : Fin l.length, if p l[(i : ℕ)] then (1 : ℝ≥0) else 0) =
      (l.countP p : ℝ≥0) := by
    exact_mod_cast List.countP_eq_sum_fin_ite l p
  rw [← hc, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all

/-- Summing the removal equation over all positions selected by a predicate. -/
theorem sum_ite_listWeight_eraseIdx (p : S → Bool) (w : S → ℝ≥0) (l : List S) :
    (∑ i : Fin l.length,
      if p l[(i : ℕ)] then listWeight w (l.eraseIdx i) else 0) +
        listWeight (fun x => if p x then w x else 0) l = l.countP p * listWeight w l := by
  rw [← sum_fin_listWeight, ← Finset.sum_add_distrib, ← sum_fin_ite_countP]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all [listWeight_eraseIdx_add w l i i.isLt]

/-- The total weight selected by a predicate is zero when no position satisfies it. -/
theorem listWeight_ite_eq_zero_of_countP_eq_zero (p : S → Bool) (w : S → ℝ≥0)
    (l : List S) (h : l.countP p = 0) :
    listWeight (fun x => if p x then w x else 0) l = 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.countP_cons] at h
      cases hp : p x with
      | false => simp_all
      | true => simp [hp] at h

/-- Removing an unselected position leaves the selected weight unchanged. -/
theorem listWeight_ite_eraseIdx_of_false (p : S → Bool) (w : S → ℝ≥0)
    (l : List S) (i : ℕ) (hi : i < l.length) (hp : p l[i] = false) :
    listWeight (fun x => if p x then w x else 0) (l.eraseIdx i) =
      listWeight (fun x => if p x then w x else 0) l := by
  simpa [hp] using listWeight_eraseIdx_add (fun x => if p x then w x else 0) l i hi

/-- Summing the remaining selected weight over selected removals. -/
theorem sum_ite_listWeight_ite_eraseIdx (p : S → Bool) (w : S → ℝ≥0) (l : List S) :
    (∑ i : Fin l.length, if p l[(i : ℕ)] then
      listWeight (fun x => if p x then w x else 0) (l.eraseIdx i) else 0) =
        ((l.countP p - 1 : ℕ) : ℝ≥0) * listWeight (fun x => if p x then w x else 0) l := by
  have h := sum_ite_listWeight_eraseIdx p (fun x => if p x then w x else 0) l
  have hw : (fun x => if p x then (if p x then w x else 0) else 0) =
      (fun x => if p x then w x else 0) := by
    funext x
    split <;> simp_all
  rw [hw] at h
  cases hg : l.countP p with
  | zero =>
      have hz := listWeight_ite_eq_zero_of_countP_eq_zero p w l hg
      simpa [hg, hz] using h
  | succ g =>
      rw [hg] at h
      simpa only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        add_left_inj] using h

/-- Summing unselected weights over selected removals multiplies by the selected count. -/
theorem sum_ite_listWeight_not_eraseIdx (p : S → Bool) (w : S → ℝ≥0) (l : List S) :
    (∑ i : Fin l.length, if p l[(i : ℕ)] then
      listWeight (fun x => if !p x then w x else 0) (l.eraseIdx i) else 0) =
        l.countP p * listWeight (fun x => if !p x then w x else 0) l := by
  rw [← sum_fin_ite_countP]
  apply Finset.sum_congr rfl
  intro i _
  split
  · rename_i hi
    rw [listWeight_ite_eraseIdx_of_false (fun x => !p x) w l i i.isLt (by simp [hi])]
  · rfl

/-- Separating a finite sum according to a Boolean predicate. -/
theorem sum_fin_ite_add (p : S → Bool) (l : List S) (f g : Fin l.length → ℝ≥0) :
    (∑ i : Fin l.length, if p l[(i : ℕ)] then f i else g i) =
      (∑ i : Fin l.length, if p l[(i : ℕ)] then f i else 0) +
      (∑ i : Fin l.length, if !p l[(i : ℕ)] then g i else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases p l[(i : ℕ)] <;> simp

/-- The four sums produced by a weighted first-draw decomposition. -/
theorem sum_fin_weighted_eraseIdx (p : S → Bool) (w : S → ℝ≥0) (l : List S)
    (a b c d : ℝ≥0) :
    (∑ i : Fin l.length, if p l[(i : ℕ)] then
      a * listWeight (fun x => if p x then w x else 0) (l.eraseIdx i) +
        b * listWeight (fun x => if !p x then w x else 0) (l.eraseIdx i)
      else
      c * listWeight (fun x => if p x then w x else 0) (l.eraseIdx i) +
        d * listWeight (fun x => if !p x then w x else 0) (l.eraseIdx i)) =
      a * ((l.countP p - 1 : ℕ) : ℝ≥0) * listWeight (fun x => if p x then w x else 0) l +
      b * l.countP p * listWeight (fun x => if !p x then w x else 0) l +
      c * l.countP (fun x => !p x) * listWeight (fun x => if p x then w x else 0) l +
      d * ((l.countP (fun x => !p x) - 1 : ℕ) : ℝ≥0) *
        listWeight (fun x => if !p x then w x else 0) l := by
  rw [sum_fin_ite_add]
  have hsplit (q : Bool) (a b x y : ℝ≥0) :
      (if q then a * x + b * y else 0) =
        a * (if q then x else 0) + b * (if q then y else 0) := by
    cases q <;> simp
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  rw [sum_ite_listWeight_ite_eraseIdx, sum_ite_listWeight_not_eraseIdx,
    sum_ite_listWeight_ite_eraseIdx (fun x => !p x)]
  have hcross := sum_ite_listWeight_not_eraseIdx (fun x => !p x) w l
  simp only [Bool.not_not] at hcross
  rw [hcross]
  ring

/-- The finite recursion for the expected weight drawn before collecting the requested successes.
-/
@[expose] noncomputable def drawWeight (accept : S → Bool) (w : S → ℝ≥0) : ℕ → List S → ℝ≥0
  | 0, _ => 0
  | _ + 1, [] => 0
  | r + 1, x :: xs =>
      (∑ i : Fin (xs.length + 1),
        let y := (x :: xs)[(i : ℕ)]'(by simpa using i.isLt)
        w y + drawWeight accept w (if accept y then r else r + 1)
          ((x :: xs).eraseIdx i)) / (xs.length + 1)
  termination_by _ l => l.length
  decreasing_by
    have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
    rw [List.length_eraseIdx_of_lt hi]
    simp only [List.length_cons] at hi ⊢
    omega

@[simp] theorem drawWeight_zero (accept : S → Bool) (w : S → ℝ≥0) (l : List S) :
    drawWeight accept w 0 l = 0 := by rw [drawWeight]

@[simp] theorem drawWeight_nil (accept : S → Bool) (w : S → ℝ≥0) (r : ℕ) :
    drawWeight accept w r [] = 0 := by cases r <;> rw [drawWeight]

/-- The finite weighted recursion agrees with the measure semantics of `drawUntil`. -/
theorem lintegral_listWeight_drawUntil (accept : S → Bool) (w : S → ℝ≥0) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n →
      (∫⁻ t, (t : ENNReal) ∂𝒟[listWeight w <$> drawUntil accept r l]) =
        (drawWeight accept w r l : ENNReal) := by
  induction n with
  | zero =>
      intro r l hl
      obtain rfl := List.length_eq_zero_iff.mp hl
      simp
  | succ n ih =>
      intro r l hl
      cases r with
      | zero => simp
      | succ r =>
        cases l with
        | nil => simp
        | cons x xs =>
          have hxs : xs.length = n := by simpa using hl
          have hstep : ∀ i : Fin (xs.length + 1),
              (∫⁻ t, (t : ENNReal) ∂𝒟[listWeight w <$>
                (((x :: xs)[(i : ℕ)] :: ·) <$>
                  drawUntil accept (if accept (x :: xs)[(i : ℕ)] then r else r + 1)
                    ((x :: xs).eraseIdx i))]) =
                (w (x :: xs)[(i : ℕ)] + drawWeight accept w
                  (if accept (x :: xs)[(i : ℕ)] then r else r + 1)
                  ((x :: xs).eraseIdx i) : ℝ≥0) := by
            intro i
            have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
            have hlen : ((x :: xs).eraseIdx i).length = n := by
              rw [List.length_eraseIdx_of_lt hi, List.length_cons, hxs]
              omega
            simp only [Functor.map_map, listWeight_cons]
            have hmap : (fun a => w (x :: xs)[(i : ℕ)] + listWeight w a) <$>
                drawUntil accept (if accept (x :: xs)[(i : ℕ)] then r else r + 1)
                  ((x :: xs).eraseIdx i) =
                (fun a : ℝ≥0 => w (x :: xs)[(i : ℕ)] + a) <$>
                  (listWeight w <$> drawUntil accept
                    (if accept (x :: xs)[(i : ℕ)] then r else r + 1)
                    ((x :: xs).eraseIdx i)) := by
              rw [Functor.map_map]
            rw [hmap, lintegral_evalDist_map _
                (f := fun a : ℝ≥0 => w (x :: xs)[(i : ℕ)] + a)
                (g := fun a : ℝ≥0 => (a : ENNReal))
                (measurable_const.add measurable_id) measurable_coe_nnreal_ennreal]
            simp only [ENNReal.coe_add]
            rw [lintegral_add_left measurable_const _,
              lintegral_const, measure_univ, mul_one, ih _ _ hlen]
          rw [drawUntil_cons, map_bind,
            lintegral_evalDist_bind_of_discrete _ _ measurable_coe_nnreal_ennreal]
          simp only [hstep]
          rw [lintegral_evalDist_uniformFin, drawWeight]
          simp

/-- Partitioning a pool partitions its total weight. -/
theorem listWeight_eq_ite_add_not (p : S → Bool) (w : S → ℝ≥0) (l : List S) :
    listWeight w l = listWeight (fun x => if p x then w x else 0) l +
      listWeight (fun x => if !p x then w x else 0) l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [listWeight_cons, ih]
      cases p x <;> simp <;> ring

/-- Exact expected weighted work when the pool contains enough accepting positions. -/
theorem drawWeight_eq (accept : S → Bool) (w : S → ℝ≥0) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → r ≤ l.countP accept →
      drawWeight accept w r l =
        (r : ℝ≥0) / l.countP accept *
          listWeight (fun x => if accept x then w x else 0) l +
        (r : ℝ≥0) / (l.countP accept + 1) *
          listWeight (fun x => if !accept x then w x else 0) l := by
  induction n with
  | zero =>
      intro r l hl hr
      obtain rfl := List.length_eq_zero_iff.mp hl
      simp at hr
      subst r
      simp
  | succ n ih =>
      intro r l hl hr
      cases r with
      | zero => simp
      | succ r =>
        cases l with
        | nil => simp
        | cons x xs =>
          have hstep : ∀ i : Fin (xs.length + 1),
              drawWeight accept w (if accept (x :: xs)[(i : ℕ)] then r else r + 1)
                  ((x :: xs).eraseIdx i) =
              if accept (x :: xs)[(i : ℕ)] then
                (r : ℝ≥0) / ((x :: xs).countP accept - 1 : ℕ) *
                    listWeight (fun y => if accept y then w y else 0) ((x :: xs).eraseIdx i) +
                  (r : ℝ≥0) / (x :: xs).countP accept *
                    listWeight (fun y => if !accept y then w y else 0) ((x :: xs).eraseIdx i)
              else
                ((r + 1 : ℕ) : ℝ≥0) / (x :: xs).countP accept *
                    listWeight (fun y => if accept y then w y else 0) ((x :: xs).eraseIdx i) +
                  ((r + 1 : ℕ) : ℝ≥0) / ((x :: xs).countP accept + 1) *
                    listWeight (fun y => if !accept y then w y else 0) ((x :: xs).eraseIdx i) := by
            intro i
            have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
            have hlen : ((x :: xs).eraseIdx i).length = n := by
              rw [List.length_eraseIdx_of_lt hi]
              omega
            cases ha : accept (x :: xs)[(i : ℕ)] with
            | false =>
                simp only [Bool.false_eq_true, ite_false]
                have hc := List.countP_eraseIdx_of_neg hi ha
                rw [ih _ _ hlen (by omega), hc]
            | true =>
                simp only [ite_true]
                have hc := List.countP_eraseIdx_of_pos hi ha
                have hc' : ((x :: xs).eraseIdx i).countP accept =
                    (x :: xs).countP accept - 1 := by omega
                rw [ih _ _ hlen (by omega), hc']
                have hcast : (((((x :: xs).countP accept - 1 : ℕ) : ℝ≥0)) + 1) =
                    ((x :: xs).countP accept : ℝ≥0) := by
                  exact_mod_cast (show (x :: xs).countP accept - 1 + 1 =
                    (x :: xs).countP accept by omega)
                rw [hcast]
          rw [drawWeight]
          simp only [hstep]
          rw [Finset.sum_add_distrib]
          have hs := sum_fin_listWeight w (x :: xs)
          change (∑ i : Fin (xs.length + 1), w (x :: xs)[(i : ℕ)]) = _ at hs
          rw [hs]
          have he := sum_fin_weighted_eraseIdx accept w (x :: xs)
            ((r : ℝ≥0) / ((x :: xs).countP accept - 1 : ℕ))
            ((r : ℝ≥0) / (x :: xs).countP accept)
            (((r + 1 : ℕ) : ℝ≥0) / (x :: xs).countP accept)
            (((r + 1 : ℕ) : ℝ≥0) / ((x :: xs).countP accept + 1))
          dsimp only [List.length_cons] at he
          rw [he]
          set G := (x :: xs).countP accept
          set B := (x :: xs).countP (fun y => !accept y)
          set A := listWeight (fun y => if accept y then w y else 0) (x :: xs)
          set D := listWeight (fun y => if !accept y then w y else 0) (x :: xs)
          have hGB : G + B = xs.length + 1 := by
            simpa only [G, B, List.length_cons, decide_not, Bool.decide_eq_true] using
              (List.length_eq_countP_add_countP accept (l := x :: xs)).symm
          have hweight : listWeight w (x :: xs) = A + D :=
            listWeight_eq_ite_add_not accept w (x :: xs)
          rw [hweight]
          have hG : (G : ℝ≥0) ≠ 0 := by
            exact_mod_cast (show G ≠ 0 by omega)
          have hG1 : (G + 1 : ℝ≥0) ≠ 0 := by positivity
          have hN : (xs.length + 1 : ℝ≥0) ≠ 0 := by positivity
          have hrG : r ≤ G - 1 := by omega
          have hcancel : (r : ℝ≥0) / ((G - 1 : ℕ) : ℝ≥0) * ((G - 1 : ℕ) : ℝ≥0) = r := by
            by_cases hz : G - 1 = 0
            · have : r = 0 := by omega
              simp [this]
            · exact div_mul_cancel₀ _ (by exact_mod_cast hz)
          rw [mul_assoc ((r : ℝ≥0) / ((G - 1 : ℕ) : ℝ≥0)),
            ← mul_assoc ((r : ℝ≥0) / ((G - 1 : ℕ) : ℝ≥0)), hcancel]
          have hBD : (((B - 1 : ℕ) : ℝ≥0) + 1) * D = (B : ℝ≥0) * D := by
            cases hb : B with
            | zero =>
                have : D = 0 := listWeight_ite_eq_zero_of_countP_eq_zero
                  (fun y => !accept y) w (x :: xs) hb
                simp [this]
            | succ b => simp
          have hGB' : (G : ℝ≥0) + B = xs.length + 1 := by exact_mod_cast hGB
          apply (div_eq_iff hN).2
          field_simp
          apply NNReal.eq
          push_cast
          have hBD' := congrArg (fun z : ℝ≥0 => (z : ℝ)) hBD
          push_cast at hBD'
          have hGB'' : (G : ℝ) + B = xs.length + 1 := by exact_mod_cast hGB
          linear_combination
            (G : ℝ) * (r + 1) * hBD' +
              (r + 1) * ((A : ℝ) * (G + 1) + D * G) * hGB''


/-- Drawing without replacement never exceeds the pool's total weight. -/
theorem drawWeight_le (accept : S → Bool) (w : S → ℝ≥0) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → drawWeight accept w r l ≤ listWeight w l := by
  induction n with
  | zero =>
      intro r l hl
      obtain rfl := List.length_eq_zero_iff.mp hl
      simp
  | succ n ih =>
      intro r l hl
      cases r with
      | zero => simp
      | succ r =>
        cases l with
        | nil => simp
        | cons x xs =>
          rw [drawWeight]
          apply (div_le_iff₀ (by positivity : (xs.length + 1 : ℝ≥0) > 0)).2
          calc
            _ ≤ ∑ _i : Fin (xs.length + 1), listWeight w (x :: xs) := by
              apply Finset.sum_le_sum
              intro i _
              have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
              have hlen : ((x :: xs).eraseIdx i).length = n := by
                rw [List.length_eraseIdx_of_lt hi]
                omega
              calc
                _ ≤ w (x :: xs)[(i : ℕ)] + listWeight w ((x :: xs).eraseIdx i) :=
                  add_le_add le_rfl (ih _ _ hlen)
                _ = listWeight w (x :: xs) := by
                  rw [add_comm, listWeight_eraseIdx_add w (x :: xs) i hi]
            _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]; push_cast; ring

/-- Summing natural weights commutes with their inclusion in the nonnegative reals. -/
@[simp] theorem listWeight_natCast (w : S → ℕ) (l : List S) :
    listWeight (fun x => (w x : ℝ≥0)) l = (((l.map w).sum : ℕ) : ℝ≥0) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

end ProbComp
