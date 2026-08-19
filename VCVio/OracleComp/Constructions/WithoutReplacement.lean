/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.NegativeHypergeometric
public import VCVio.OracleComp.ProbComp

/-!
# Drawing without replacement until enough successes

`drawUntil accept r pool` draws uniformly from `pool` without replacement and stops as soon as `r`
accepting values have been collected, or when the pool runs out. It returns the values drawn, in
order, so a caller can read off both how many draws it made and which of them accepted.

`expectedLength_drawUntil` identifies its expected number of draws with the negative
hypergeometric recursion `NegHypergeom.expectedDraws`, and `expectedLength_drawUntil_le` gives the
resulting closed-form bound. Exhaustion needs no separate treatment: the loop simply returns the
whole pool, and `NegHypergeom.expectedDraws_le` already covers that case.

The pool is a `List`, not a `Finset`, because a draw is an index rather than a value: that keeps
the loop in `ProbComp` with no failure branch, makes the recursion terminate on the pool's length,
and costs nothing, since positions are what the counting argument uses anyway. Duplicates in the
pool are allowed and are counted as distinct.

`expectedLength` is the expected length of a list-valued computation, which is how the draw count
is read here. It is not a general expectation operator; its three laws below are exactly what the
recursion consumes.
-/

@[expose] public section

open scoped ENNReal

universe u

namespace List

variable {α : Type u} {p : α → Bool}

/-- Every position either satisfies `p` or does not. -/
theorem length_eq_countP_add_countP_not (l : List α) (p : α → Bool) :
    l.length = l.countP p + l.countP (fun x => !p x) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [countP_cons, countP_cons, length_cons, ih]
      cases hx : p x <;> simp <;> omega

/-- Deleting an accepting position lowers the accepting count by one. -/
theorem countP_eraseIdx_of_pos {l : List α} {i : ℕ} (hi : i < l.length) (hp : p l[i] = true) :
    (l.eraseIdx i).countP p + 1 = l.countP p := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [eraseIdx_eq_take_drop_succ, countP_append, countP_append, ← List.getElem_cons_drop hi,
    countP_cons, hp]
  simp
  omega

/-- Deleting a rejecting position leaves the accepting count alone. -/
theorem countP_eraseIdx_of_neg {l : List α} {i : ℕ} (hi : i < l.length) (hp : p l[i] = false) :
    (l.eraseIdx i).countP p = l.countP p := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [eraseIdx_eq_take_drop_succ, countP_append, countP_append, ← List.getElem_cons_drop hi,
    countP_cons, hp]
  simp

end List

namespace ProbComp

variable {S : Type}

/-! ## Expected length of a list-valued computation -/

/-- The expected length of a list-valued computation. -/
noncomputable def expectedLength (mx : ProbComp (List S)) : ℝ≥0∞ :=
  ∑' d : List S, Pr[= d | mx] * d.length

@[simp] theorem expectedLength_pure (d : List S) :
    expectedLength (pure d : ProbComp (List S)) = d.length := by
  classical
  rw [expectedLength]
  refine (tsum_eq_single d fun d' hd' => ?_).trans ?_
  · rw [probOutput_pure, if_neg hd', zero_mul]
  · rw [probOutput_pure_self, one_mul]

theorem expectedLength_bind {α : Type} (mx : ProbComp α) (f : α → ProbComp (List S)) :
    expectedLength (mx >>= f) = ∑' x : α, Pr[= x | mx] * expectedLength (f x) := by
  simp only [expectedLength, probOutput_bind_eq_tsum]
  calc ∑' d : List S, (∑' x : α, Pr[= x | mx] * Pr[= d | f x]) * (d.length : ℝ≥0∞)
      = ∑' (d : List S) (x : α), Pr[= x | mx] * (Pr[= d | f x] * (d.length : ℝ≥0∞)) := by
        refine tsum_congr fun d => ?_
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun x => by ring
    _ = ∑' (x : α) (d : List S), Pr[= x | mx] * (Pr[= d | f x] * (d.length : ℝ≥0∞)) :=
        ENNReal.tsum_comm
    _ = ∑' x : α, Pr[= x | mx] * ∑' d : List S, Pr[= d | f x] * (d.length : ℝ≥0∞) :=
        tsum_congr fun _ => ENNReal.tsum_mul_left

theorem expectedLength_map {α : Type} (mx : ProbComp α) (f : α → List S) :
    expectedLength (f <$> mx) = ∑' x : α, Pr[= x | mx] * (f x).length := by
  rw [map_eq_bind_pure_comp, expectedLength_bind]
  exact tsum_congr fun x => by rw [Function.comp_apply, expectedLength_pure]

/-- Prefixing a fixed value adds exactly one to the expected length. -/
theorem expectedLength_cons_map (y : S) (mc : ProbComp (List S)) :
    expectedLength ((y :: ·) <$> mc) = expectedLength mc + 1 := by
  rw [expectedLength_map]
  simp only [List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
  rw [ENNReal.tsum_add, tsum_probOutput_eq_one' (probFailure_of_liftM_PMF mc)]
  rfl

/-! ## The loop -/

/-- Draw uniformly at random from `pool` without replacement, keeping every value drawn, until `r`
of them have been accepted or the pool is exhausted. -/
noncomputable def drawUntil (accept : S → Bool) : ℕ → List S → ProbComp (List S)
  | 0, _ => pure []
  | _ + 1, [] => pure []
  | r + 1, x :: xs => do
      let i ← $[0..xs.length]
      let y := (x :: xs)[(i : ℕ)]'(by simpa using i.isLt)
      (y :: ·) <$> drawUntil accept (if accept y then r else r + 1) ((x :: xs).eraseIdx i)
  termination_by _ l => l.length
  decreasing_by
    have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
    rw [List.length_eraseIdx_of_lt hi]
    simp only [List.length_cons] at hi ⊢
    omega

@[simp] theorem drawUntil_zero (accept : S → Bool) (l : List S) :
    drawUntil accept 0 l = pure [] := by rw [drawUntil]

@[simp] theorem drawUntil_nil (accept : S → Bool) (r : ℕ) :
    drawUntil accept r [] = pure [] := by cases r <;> rw [drawUntil]

theorem drawUntil_cons (accept : S → Bool) (r : ℕ) (x : S) (xs : List S) :
    drawUntil accept (r + 1) (x :: xs) =
      (do
        let i ← $[0..xs.length]
        let y := (x :: xs)[(i : ℕ)]'(by simpa using i.isLt)
        (y :: ·) <$>
          drawUntil accept (if accept y then r else r + 1) ((x :: xs).eraseIdx i)) := by
  rw [drawUntil]

/-! ## Expected number of draws -/

private theorem sum_map_ite (l : List S) (p : S → Bool) (a b : ℝ≥0∞) :
    (l.map fun x => if p x then a else b).sum
      = (l.countP p : ℝ≥0∞) * a + (l.countP (fun x => !p x) : ℝ≥0∞) * b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons, List.countP_cons]
      cases hx : p x <;>
        · simp only [Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true]
          push_cast
          ring

private theorem sum_fin_ite (l : List S) (p : S → Bool) (a b : ℝ≥0∞) :
    ∑ i : Fin l.length, (if p l[(i : ℕ)] then a else b)
      = (l.countP p : ℝ≥0∞) * a + (l.countP (fun x => !p x) : ℝ≥0∞) * b := by
  rw [← List.sum_ofFn (f := fun i : Fin l.length => if p l[(i : ℕ)] then a else b),
    show (List.ofFn fun i : Fin l.length => if p l[(i : ℕ)] then a else b)
      = l.map (fun y => if p y then a else b) from
      List.ofFn_getElem_eq_map l (fun y => if p y then a else b),
    sum_map_ite]

/-- The loop's expected number of draws is the negative hypergeometric expectation at the pool's
size and accepting count. -/
theorem expectedLength_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n →
      expectedLength (drawUntil accept r l)
        = NegHypergeom.expectedDraws n (l.countP accept) r := by
  induction n with
  | zero =>
      intro r l hl
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      simp
  | succ n ih =>
      intro r l hl
      cases r with
      | zero => simp
      | succ r =>
        obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
          cases l with
          | nil => simp at hl
          | cons x xs => exact ⟨x, xs, rfl⟩
        have hxs : xs.length = n := by simpa using hl
        subst hxs
        set G : ℕ := (x :: xs).countP accept with hG
        set B : ℕ := (x :: xs).countP (fun y => !accept y) with hB
        have hGB : xs.length + 1 = G + B := List.length_eq_countP_add_countP_not (x :: xs) accept
        have hne : ((xs.length : ℝ≥0∞) + 1) ≠ 0 := by positivity
        have htop : ((xs.length : ℝ≥0∞) + 1) ≠ ⊤ := by finiteness
        -- Drawing at index `i` leaves a pool one shorter, with one fewer accepting value exactly
        -- when the drawn value accepted.
        have hstep : ∀ i : Fin (xs.length + 1),
            expectedLength ((((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) :: ·) <$>
                drawUntil accept
                  (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then r else r + 1)
                  ((x :: xs).eraseIdx i))
              = (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then
                  NegHypergeom.expectedDraws xs.length (G - 1) r
                else NegHypergeom.expectedDraws xs.length G (r + 1)) + 1 := by
          intro i
          have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
          have hlen : ((x :: xs).eraseIdx i).length = xs.length := by
            rw [List.length_eraseIdx_of_lt hi]; simp
          rw [expectedLength_cons_map, ih _ _ hlen]
          congr 1
          cases hacc : accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              rw [List.countP_eraseIdx_of_neg hi hacc]
          | true =>
              simp only [if_true]
              have hcount : ((x :: xs).eraseIdx i).countP accept = G - 1 := by
                have h := List.countP_eraseIdx_of_pos hi hacc
                omega
              rw [hcount]
        -- Average the step over a uniform index.
        rw [drawUntil_cons, expectedLength_bind]
        simp only [hstep, probOutput_uniformFin_eq_div]
        rw [ENNReal.tsum_mul_left, tsum_fintype (L := .unconditional _), Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        -- The indexed sum is a sum over the pool.
        have hcancel : ((xs.length : ℝ≥0∞) + 1)⁻¹ * ((xs.length : ℝ≥0∞) + 1) = 1 :=
          ENNReal.inv_mul_cancel hne htop
        rw [show (∑ i : Fin (xs.length + 1),
              (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then
                  NegHypergeom.expectedDraws xs.length (G - 1) r
                else NegHypergeom.expectedDraws xs.length G (r + 1)))
            = ∑ i : Fin (x :: xs).length,
                (if accept ((x :: xs)[(i : ℕ)]) then
                    NegHypergeom.expectedDraws xs.length (G - 1) r
                  else NegHypergeom.expectedDraws xs.length G (r + 1)) from rfl,
          sum_fin_ite, NegHypergeom.expectedDraws_succ,
          show xs.length + 1 - G = B from by omega,
          show ((xs.length + 1 : ℕ) : ℝ≥0∞) = (xs.length : ℝ≥0∞) + 1 from by push_cast; ring]
        simp only [div_eq_mul_inv, one_mul]
        rw [mul_add, mul_add, hcancel]
        ring

/-- The closed-form bound on the loop's expected number of draws. Exhaustion is covered: when the
pool holds fewer than `r` accepting values the loop draws all of it, and the bound still holds. -/
theorem expectedLength_drawUntil_le (accept : S → Bool) (r : ℕ) (l : List S) :
    expectedLength (drawUntil accept r l)
      ≤ r * (l.length + 1) / (l.countP accept + 1) := by
  rw [expectedLength_drawUntil accept l.length r l rfl]
  exact NegHypergeom.expectedDraws_le List.countP_le_length

end ProbComp
