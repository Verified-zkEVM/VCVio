/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.NegativeHypergeometric
public import VCVio.EvalDist.Expectation
public import VCVio.OracleComp.ProbComp

/-!
# Drawing without replacement until enough successes

`drawUntil accept r pool` draws uniformly from `pool` without replacement and stops as soon as `r`
accepting values have been collected, or when the pool runs out. It returns the values drawn, in
order, so a caller can read off both how many draws it made and which of them accepted.

`expectedValue_length_drawUntil` identifies its expected number of draws with the negative
hypergeometric recursion `NegHypergeom.expectedDraws`, and `expectedValue_length_drawUntil_le`
gives the resulting closed-form bound. Exhaustion needs no separate treatment: the loop simply
returns the whole pool, and `NegHypergeom.expectedDraws_le` already covers that case.

The pool is a `List`, not a `Finset`, because a draw is an index rather than a value: that keeps
the loop in `ProbComp` with no failure branch, makes the recursion terminate on the pool's length,
and costs nothing, since positions are what the counting argument uses anyway. Duplicates in the
pool are allowed and are counted as distinct.

The draw count is read as the expected length of the returned list, through
`OracleComp.EvalDist.expectedValue`.
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

/-- `countP` as a sum of indicators, the form that matches `Finset.card_filter`. -/
theorem countP_eq_sum_map (l : List α) (p : α → Bool) :
    l.countP p = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [countP_cons, map_cons, sum_cons, ih]
      cases p x
      · simp
      · simp; omega

/-- In a duplicate-free list, deleting a position removes that value entirely. -/
theorem getElem_notMem_eraseIdx {l : List α} (hl : l.Nodup) {i : ℕ} (hi : i < l.length) :
    l[i] ∉ l.eraseIdx i := by
  have hsplit : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i l]
    rw [← List.getElem_cons_drop hi]
  rw [eraseIdx_eq_take_drop_succ, mem_append]
  rw [hsplit, nodup_append] at hl
  obtain ⟨-, htail, hdisj⟩ := hl
  refine fun hmem => hmem.elim (fun htake => ?_) (fun hdrop => ?_)
  · exact hdisj _ htake _ (mem_cons_self ..) rfl
  · exact (nodup_cons.mp htail).1 hdrop

/-- Deleting a rejecting position leaves the accepting count alone. -/
theorem countP_eraseIdx_of_neg {l : List α} {i : ℕ} (hi : i < l.length) (hp : p l[i] = false) :
    (l.eraseIdx i).countP p = l.countP p := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [eraseIdx_eq_take_drop_succ, countP_append, countP_append, ← List.getElem_cons_drop hi,
    countP_cons, hp]
  simp

end List

namespace Finset

/-- Counting a `Finset`'s elements through its list is filtering it. -/
theorem countP_toList {α : Type u} (s : Finset α) (p : α → Bool) :
    s.toList.countP p = (s.filter fun x => p x).card := by
  classical
  rw [List.countP_eq_sum_map, Finset.sum_map_toList, Finset.card_filter]

end Finset

namespace ProbComp

variable {S : Type}

/-! ## Expected length of a list-valued computation -/

open OracleComp.EvalDist in
/-- Prefixing a fixed value adds exactly one to the expected length. -/
theorem expectedValue_length_cons_map (y : S) (mc : ProbComp (List S)) :
    expectedValue ((y :: ·) <$> mc) (fun d => (d.length : ℝ≥0∞))
      = expectedValue mc (fun d => (d.length : ℝ≥0∞)) + 1 := by
  rw [expectedValue_map]
  simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
  rw [expectedValue_add, expectedValue_const (probFailure_of_liftM_PMF mc)]

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


/-! ## What the loop returns

Success is a property of the pool alone: the loop collects `r` accepting values exactly when the
pool holds that many, and otherwise stops having drained it. That is what lets the extractor read
its own success off the acceptance table. -/

theorem mem_of_mem_support_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → ∀ d ∈ support (drawUntil accept r l),
      ∀ y ∈ d, y ∈ l := by
  induction n with
  | zero =>
      intro r l hl d hd
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      simp_all
  | succ n ih =>
      intro r l hl d hd
      cases r with
      | zero => simp_all
      | succ r =>
        obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
          cases l with
          | nil => simp at hl
          | cons x xs => exact ⟨x, xs, rfl⟩
        have hxs : xs.length = n := by simpa using hl
        rw [drawUntil_cons, mem_support_bind_iff] at hd
        obtain ⟨i, -, hd⟩ := hd
        rw [support_map] at hd
        obtain ⟨rest, hrest, rfl⟩ := hd
        have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
        have hlen : ((x :: xs).eraseIdx i).length = n := by
          rw [List.length_eraseIdx_of_lt hi]; simpa using hxs
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact List.getElem_mem hi
        · exact List.mem_of_mem_eraseIdx (ih _ _ hlen rest hrest y hy)

theorem nodup_of_mem_support_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → l.Nodup → ∀ d ∈ support (drawUntil accept r l),
      d.Nodup := by
  induction n with
  | zero =>
      intro r l hl _ d hd
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      simp_all
  | succ n ih =>
      intro r l hl hnd d hd
      cases r with
      | zero => simp_all
      | succ r =>
        obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
          cases l with
          | nil => simp at hl
          | cons x xs => exact ⟨x, xs, rfl⟩
        have hxs : xs.length = n := by simpa using hl
        rw [drawUntil_cons, mem_support_bind_iff] at hd
        obtain ⟨i, -, hd⟩ := hd
        rw [support_map] at hd
        obtain ⟨rest, hrest, rfl⟩ := hd
        have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
        have hlen : ((x :: xs).eraseIdx i).length = n := by
          rw [List.length_eraseIdx_of_lt hi]; simpa using hxs
        refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih _ _ hlen (hnd.eraseIdx i) rest hrest⟩
        exact List.getElem_notMem_eraseIdx hnd hi
          (mem_of_mem_support_drawUntil accept _ _ _ hlen rest hrest _ hmem)

/-- The loop collects `min r (accepting values in the pool)` of them: it stops either because it
has enough or because the pool ran out. -/
theorem countP_of_mem_support_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → ∀ d ∈ support (drawUntil accept r l),
      d.countP accept = min r (l.countP accept) := by
  induction n with
  | zero =>
      intro r l hl d hd
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      simp_all
  | succ n ih =>
      intro r l hl d hd
      cases r with
      | zero => simp_all
      | succ r =>
        obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
          cases l with
          | nil => simp at hl
          | cons x xs => exact ⟨x, xs, rfl⟩
        have hxs : xs.length = n := by simpa using hl
        rw [drawUntil_cons, mem_support_bind_iff] at hd
        obtain ⟨i, -, hd⟩ := hd
        rw [support_map] at hd
        obtain ⟨rest, hrest, rfl⟩ := hd
        have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
        have hlen : ((x :: xs).eraseIdx i).length = n := by
          rw [List.length_eraseIdx_of_lt hi]; simpa using hxs
        cases hacc : accept ((x :: xs)[(i : ℕ)]) with
        | false =>
            rw [hacc] at hrest
            simp only [Bool.false_eq_true, if_false] at hrest
            have hcount := ih _ _ hlen rest hrest
            have hneg := List.countP_eraseIdx_of_neg hi hacc
            rw [List.countP_cons, hacc]
            simp only [Bool.false_eq_true, if_false]
            omega
        | true =>
            rw [hacc] at hrest
            simp only [if_true] at hrest
            have hcount := ih _ _ hlen rest hrest
            have hpos := List.countP_eraseIdx_of_pos hi hacc
            rw [List.countP_cons, hacc]
            simp only [if_true]
            omega

/-! ## The loop is a random ordering, truncated

Taking `accept` to be always false leaves the budget untouched at every draw, so the loop stops
only when the pool is empty: `drawAll` draws the whole pool, one uniformly chosen element at a
time. `takeUntil` is the deterministic truncation `drawUntil` performs on such an ordering, and
`evalDist_drawUntil_eq_map_drawAll` says the two accounts agree.

The point of the reformulation is that a uniformly random ordering depends on the pool only through
its underlying multiset, which the recursive loop hides. -/

/-- Draw the whole pool, one uniformly chosen element at a time. -/
noncomputable def drawAll (l : List S) : ProbComp (List S) := drawUntil (fun _ => false) 1 l

@[simp] theorem drawAll_nil : drawAll ([] : List S) = pure [] := drawUntil_nil _ _

theorem drawAll_cons (x : S) (xs : List S) :
    drawAll (x :: xs) =
      (do
        let i ← $[0..xs.length]
        let y := (x :: xs)[(i : ℕ)]'(by simpa using i.isLt)
        (y :: ·) <$> drawAll ((x :: xs).eraseIdx i)) := by
  rw [drawAll, drawUntil_cons]
  simp only [Bool.false_eq_true, if_false, drawAll]

/-- Keep an ordering's prefix up to and including its `r`-th accepting element. This is what
`drawUntil` does to the ordering `drawAll` produces. -/
def takeUntil (accept : S → Bool) : ℕ → List S → List S
  | 0, _ => []
  | _, [] => []
  | r + 1, x :: xs => x :: takeUntil accept (if accept x then r else r + 1) xs

@[simp] theorem takeUntil_zero (accept : S → Bool) (l : List S) :
    takeUntil accept 0 l = [] := by cases l <;> rfl

@[simp] theorem takeUntil_nil (accept : S → Bool) (r : ℕ) :
    takeUntil accept r ([] : List S) = [] := by cases r <;> rfl

theorem takeUntil_cons (accept : S → Bool) (r : ℕ) (x : S) (xs : List S) :
    takeUntil accept (r + 1) (x :: xs)
      = x :: takeUntil accept (if accept x then r else r + 1) xs := rfl

/-- The loop is total: it only ever samples an index of a nonempty pool. -/
theorem neverFail_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → NeverFail (drawUntil accept r l) := by
  induction n with
  | zero =>
      intro r l hl
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      rw [drawUntil_nil]
      infer_instance
  | succ n ih =>
      intro r l hl
      obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
        cases l with
        | nil => simp at hl
        | cons x xs => exact ⟨x, xs, rfl⟩
      have hxs : xs.length = n := by simpa using hl
      cases r with
      | zero => rw [drawUntil_zero]; infer_instance
      | succ r =>
          rw [drawUntil_cons]
          refine (neverFail_bind_iff _ _).mpr ⟨inferInstance, fun i _ => ?_⟩
          rw [neverFail_map_iff]
          have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
          exact ih _ _ (by rw [List.length_eraseIdx_of_lt hi]; simpa using hxs)

theorem neverFail_drawAll (l : List S) : NeverFail (drawAll l) :=
  neverFail_drawUntil _ l.length 1 l rfl

/-- **The loop is a uniformly random ordering, truncated.** -/
theorem evalDist_drawUntil_eq_map_drawAll (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n →
      evalDist (drawUntil accept r l) = evalDist (takeUntil accept r <$> drawAll l) := by
  induction n with
  | zero =>
      intro r l hl
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      simp
  | succ n ih =>
      intro r l hl
      obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
        cases l with
        | nil => simp at hl
        | cons x xs => exact ⟨x, xs, rfl⟩
      have hxs : xs.length = n := by simpa using hl
      cases r with
      | zero =>
          classical
          rw [drawUntil_zero,
            show takeUntil accept 0 = fun _ : List S => ([] : List S) from
              funext (takeUntil_zero accept)]
          refine evalDist_ext fun d => ?_
          rw [probOutput_map_const, (neverFail_drawAll (x :: xs)).probFailure_eq_zero,
            probOutput_pure]
          simp
      | succ r =>
          rw [drawUntil_cons, drawAll_cons, map_bind]
          refine evalDist_bind_congr fun i _ => ?_
          dsimp only
          have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
          have hlen : ((x :: xs).eraseIdx i).length = n := by
            rw [List.length_eraseIdx_of_lt hi]; simpa using hxs
          have hRHS : takeUntil accept (r + 1) <$> ((fun a : List S => (x :: xs)[(i : ℕ)] :: a)
                <$> drawAll ((x :: xs).eraseIdx i))
              = (fun a : List S => (x :: xs)[(i : ℕ)] :: a) <$>
                  (takeUntil accept (if accept ((x :: xs)[(i : ℕ)]) then r else r + 1)
                    <$> drawAll ((x :: xs).eraseIdx i)) := by
            rw [Functor.map_map, Functor.map_map]
            congr 1
          rw [hRHS]
          exact evalDist_map_eq_of_evalDist_eq (ih _ _ hlen) _

/-! ## The loop is uniform over its outcomes

Each draw is uniform over what is left, so any two runs that made the same number of draws are
equally likely — whatever they drew, and whatever the pool's order was. `probOutput_drawUntil`
records that: the weight of an outcome depends only on its length.

This is what makes the loop's law a function of the pool's *set* of values rather than of the list
presenting it, which the recursion on `List` otherwise hides. -/

private theorem probOutput_cons_map_self (y : S) (mx : ProbComp (List S)) (d : List S) :
    Pr[= y :: d | (y :: ·) <$> mx] = Pr[= d | mx] :=
  probOutput_map_injective mx (fun _ _ h => (List.cons_eq_cons.mp h).2) d

private theorem probOutput_cons_map_of_ne {y z : S} (hyz : y ≠ z) (mx : ProbComp (List S))
    (d : List S) : Pr[= z :: d | (y :: ·) <$> mx] = 0 := by
  refine probOutput_eq_zero_of_not_mem_support fun h => ?_
  rw [support_map] at h
  obtain ⟨d', -, hd'⟩ := h
  exact hyz (List.cons_eq_cons.mp hd').1

private theorem probOutput_cons_map_nil (y : S) (mx : ProbComp (List S)) :
    Pr[= ([] : List S) | (y :: ·) <$> mx] = 0 := by
  refine probOutput_eq_zero_of_not_mem_support fun h => ?_
  rw [support_map] at h
  obtain ⟨d, -, hd⟩ := h
  simp at hd

/-- A run against a nonempty pool draws at some index, and what follows is a run against the pool
with that index removed. -/
theorem mem_support_drawUntil_cons_iff (accept : S → Bool) (r : ℕ) (x : S) (xs : List S)
    {d : List S} :
    d ∈ support (drawUntil accept (r + 1) (x :: xs)) ↔
      ∃ i : Fin (xs.length + 1),
        d = ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) :: d.tail ∧
          d.tail ∈ support (drawUntil accept
            (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then r else r + 1)
            ((x :: xs).eraseIdx i)) := by
  rw [drawUntil_cons, mem_support_bind_iff]
  constructor
  · rintro ⟨i, -, hd⟩
    rw [support_map] at hd
    obtain ⟨rest, hrest, rfl⟩ := hd
    exact ⟨i, rfl, hrest⟩
  · rintro ⟨i, hd, hrest⟩
    refine ⟨i, by simp, ?_⟩
    rw [support_map]
    exact ⟨d.tail, hrest, hd.symm⟩

theorem ne_nil_of_mem_support_drawUntil_cons (accept : S → Bool) (r : ℕ) (x : S) (xs : List S)
    {d : List S} (hd : d ∈ support (drawUntil accept (r + 1) (x :: xs))) : d ≠ [] := by
  obtain ⟨i, hi, -⟩ := (mem_support_drawUntil_cons_iff accept r x xs).mp hd
  rw [hi]
  exact List.cons_ne_nil _ _

/-- **Every outcome of a given length is equally likely.** Against a pool of `n` distinct values, a
run that made `d.length` draws has weight the reciprocal of `n` falling `d.length` — the number of
ordered choices those draws had. The weight does not depend on *what* was drawn, nor on the order
the pool was presented in. -/
theorem probOutput_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → l.Nodup →
      ∀ d ∈ support (drawUntil accept r l),
        Pr[= d | drawUntil accept r l] = ((n.descFactorial d.length : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  induction n with
  | zero =>
      intro r l hl _ d hd
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      rw [drawUntil_nil] at hd ⊢
      obtain rfl : d = [] := by simpa using hd
      simp
  | succ n ih =>
      intro r l hl hnd d hd
      obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
        cases l with
        | nil => simp at hl
        | cons x xs => exact ⟨x, xs, rfl⟩
      have hxs : xs.length = n := by simpa using hl
      subst hxs
      cases r with
      | zero =>
          rw [drawUntil_zero] at hd ⊢
          obtain rfl : d = [] := by simpa using hd
          simp
      | succ r =>
          obtain ⟨i₀, hi₀, hrest⟩ := (mem_support_drawUntil_cons_iff accept r x xs).mp hd
          obtain ⟨z, d', rfl⟩ : ∃ z d', d = z :: d' := by
            cases d with
            | nil => exact absurd rfl (ne_nil_of_mem_support_drawUntil_cons accept r x xs hd)
            | cons z d' => exact ⟨z, d', rfl⟩
          have hz : ((x :: xs)[(i₀ : ℕ)]'(by simpa using i₀.isLt)) = z :=
            ((List.cons_eq_cons.mp hi₀).1).symm
          simp only [List.tail_cons] at hrest
          have hlenEr : ((x :: xs).eraseIdx i₀).length = xs.length := by
            have hi : (i₀ : ℕ) < (x :: xs).length := by simpa using i₀.isLt
            rw [List.length_eraseIdx_of_lt hi]; simp
          rw [hz] at hrest
          rw [drawUntil_cons, probOutput_bind_eq_tsum, tsum_fintype (L := .unconditional _)]
          simp only [probOutput_uniformFin_eq_div]
          have hvanish : ∀ i ∈ (Finset.univ : Finset (Fin (xs.length + 1))), i ≠ i₀ →
              1 / ((xs.length : ℝ≥0∞) + 1) *
                Pr[= z :: d' | (((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) :: ·) <$>
                  drawUntil accept
                    (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then r else r + 1)
                    ((x :: xs).eraseIdx i)] = 0 := by
            intro i _ hne
            refine mul_eq_zero_of_right _ (probOutput_cons_map_of_ne (fun heq => ?_) _ _)
            exact hne (Fin.ext (hnd.getElem_inj_iff.mp (heq.trans hz.symm)))
          rw [Finset.sum_eq_single i₀ hvanish (fun h => absurd (Finset.mem_univ _) h), hz,
            probOutput_cons_map_self,
            ih _ ((x :: xs).eraseIdx i₀) hlenEr (hnd.eraseIdx _) d' hrest,
            List.length_cons, Nat.succ_descFactorial_succ]
          push_cast
          rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness)), one_div]

/-! ## The law depends only on the pool's values

Every draw is uniform over what is left, so the order the pool was presented in is invisible.
`support_drawUntil_congr` says the reachable outcomes are the same for two nodup pools with the
same values, and with `probOutput_drawUntil` that upgrades to `evalDist_drawUntil_congr`: the whole
law is a function of the pool's set of values. -/

private theorem mem_eraseIdx_iff_of_nodup {l : List S} (hnd : l.Nodup) {i : ℕ}
    (hi : i < l.length) {y : S} : y ∈ l.eraseIdx i ↔ y ∈ l ∧ y ≠ l[i] := by
  rw [List.mem_eraseIdx_iff_getElem]
  constructor
  · rintro ⟨j, hj, hne, rfl⟩
    exact ⟨List.getElem_mem hj, fun h => hne (hnd.getElem_inj_iff.mp h)⟩
  · rintro ⟨hy, hne⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    exact ⟨j, hj, fun h => hne (by subst h; rfl), rfl⟩

private theorem support_drawUntil_subset (accept : S → Bool) (n : ℕ)
    (ih : ∀ (r : ℕ) (l l' : List S), l.length = n → l'.length = n → l.Nodup → l'.Nodup →
      (∀ y, y ∈ l ↔ y ∈ l') → support (drawUntil accept r l) = support (drawUntil accept r l'))
    (r : ℕ) : ∀ (u v : List S), u.length = n + 1 → v.length = n + 1 → u.Nodup → v.Nodup →
      (∀ y, y ∈ u ↔ y ∈ v) →
        support (drawUntil accept (r + 1) u) ⊆ support (drawUntil accept (r + 1) v) := by
  intro u v hu hv hndu hndv huv
  obtain ⟨p, ps, rfl⟩ : ∃ p ps, u = p :: ps := by
    cases u with
    | nil => simp at hu
    | cons p ps => exact ⟨p, ps, rfl⟩
  obtain ⟨q, qs, rfl⟩ : ∃ q qs, v = q :: qs := by
    cases v with
    | nil => simp at hv
    | cons q qs => exact ⟨q, qs, rfl⟩
  intro d hd
  obtain ⟨i, hdeq, hrest⟩ := (mem_support_drawUntil_cons_iff accept r p ps).mp hd
  have hi : (i : ℕ) < (p :: ps).length := by simpa using i.isLt
  obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem ((huv _).mp (List.getElem_mem hi))
  have hjlt : j < qs.length + 1 := by simpa using hj
  refine (mem_support_drawUntil_cons_iff accept r q qs).mpr ⟨⟨j, hjlt⟩, ?_, ?_⟩
  · rw [hdeq]; congr 1; exact hjeq.symm
  · rw [show (q :: qs)[((⟨j, hjlt⟩ : Fin (qs.length + 1)) : ℕ)] = (p :: ps)[(i : ℕ)] from hjeq]
    have hsub : support (drawUntil accept
          (if accept ((p :: ps)[(i : ℕ)]) then r else r + 1) ((p :: ps).eraseIdx i))
        = support (drawUntil accept
          (if accept ((p :: ps)[(i : ℕ)]) then r else r + 1) ((q :: qs).eraseIdx j)) := by
      refine ih _ _ _ ?_ ?_ (hndu.eraseIdx _) (hndv.eraseIdx _) fun y => ?_
      · rw [List.length_eraseIdx_of_lt hi]; simpa using hu
      · rw [List.length_eraseIdx_of_lt hj]; simpa using hv
      · rw [mem_eraseIdx_iff_of_nodup hndu hi, mem_eraseIdx_iff_of_nodup hndv hj, hjeq, huv y]
    rwa [← hsub]

/-- Two nodup pools holding the same values admit the same runs. -/
theorem support_drawUntil_congr (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l l' : List S), l.length = n → l'.length = n → l.Nodup → l'.Nodup →
      (∀ y, y ∈ l ↔ y ∈ l') →
        support (drawUntil accept r l) = support (drawUntil accept r l') := by
  induction n with
  | zero =>
      intro r l l' hl hl' _ _ _
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      obtain rfl : l' = [] := List.length_eq_zero_iff.mp hl'
      rfl
  | succ n ih =>
      intro r l l' hl hl' hnd hnd' hmem
      cases r with
      | zero => rw [drawUntil_zero, drawUntil_zero]
      | succ r =>
          exact Set.Subset.antisymm
            (support_drawUntil_subset accept n ih r l l' hl hl' hnd hnd' hmem)
            (support_drawUntil_subset accept n ih r l' l hl' hl hnd' hnd
              fun y => (hmem y).symm)

/-- **The loop's law depends only on the pool's values.** -/
theorem evalDist_drawUntil_congr (accept : S → Bool) (n : ℕ) (r : ℕ) (l l' : List S)
    (hl : l.length = n) (hl' : l'.length = n) (hnd : l.Nodup) (hnd' : l'.Nodup)
    (hmem : ∀ y, y ∈ l ↔ y ∈ l') :
    evalDist (drawUntil accept r l) = evalDist (drawUntil accept r l') := by
  classical
  have hsupp := support_drawUntil_congr accept n r l l' hl hl' hnd hnd' hmem
  refine evalDist_ext fun d => ?_
  by_cases hd : d ∈ support (drawUntil accept r l)
  · rw [probOutput_drawUntil accept n r l hl hnd d hd,
      probOutput_drawUntil accept n r l' hl' hnd' d (hsupp ▸ hd)]
  · rw [probOutput_eq_zero_of_not_mem_support hd,
      probOutput_eq_zero_of_not_mem_support (hsupp ▸ hd)]

/-! ## Relabelling, and exchangeability within accept classes

Relabelling the pool relabels the run: `drawUntil_map` is a program identity, since the index the
loop samples does not depend on what the values are. Composed with `evalDist_drawUntil_congr` it
gives `probEvent_mem_drawUntil_congr`, the fact the weighted analyses need — two values the pool
treats alike are equally likely to be drawn. -/

/-- Relabelling the pool relabels its runs. Stated between two pools because the sub-pool a run
descends into is not itself closed under the relabelling — only the correspondence is. -/
theorem map_mem_support_drawUntil (accept : S → Bool) (σ : Equiv.Perm S) (n : ℕ) :
    ∀ (r : ℕ) (l l' : List S), l.length = n → l'.length = n → l.Nodup → l'.Nodup →
      (∀ y, y ∈ l ↔ σ y ∈ l') →
        ∀ d ∈ support (drawUntil (fun y => accept (σ y)) r l),
          d.map σ ∈ support (drawUntil accept r l') := by
  induction n with
  | zero =>
      intro r l l' hl hl' _ _ _ d hd
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      obtain rfl : l' = [] := List.length_eq_zero_iff.mp hl'
      rw [drawUntil_nil] at hd ⊢
      obtain rfl : d = [] := by simpa using hd
      simp
  | succ n ih =>
      intro r l l' hl hl' hnd hnd' hcorr d hd
      cases r with
      | zero =>
          rw [drawUntil_zero] at hd ⊢
          obtain rfl : d = [] := by simpa using hd
          simp
      | succ r =>
          obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
            cases l with
            | nil => simp at hl
            | cons x xs => exact ⟨x, xs, rfl⟩
          obtain ⟨x', xs', rfl⟩ : ∃ x' xs', l' = x' :: xs' := by
            cases l' with
            | nil => simp at hl'
            | cons x' xs' => exact ⟨x', xs', rfl⟩
          obtain ⟨i, hdeq, hrest⟩ :=
            (mem_support_drawUntil_cons_iff (fun y => accept (σ y)) r x xs).mp hd
          have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
          obtain ⟨j, hj, hjeq⟩ :=
            List.getElem_of_mem ((hcorr _).mp (List.getElem_mem hi))
          have hjlt : j < xs'.length + 1 := by simpa using hj
          refine (mem_support_drawUntil_cons_iff accept r x' xs').mpr ⟨⟨j, hjlt⟩, ?_, ?_⟩
          · rw [hdeq, List.map_cons, List.tail_cons]
            congr 1
            exact hjeq.symm
          · rw [hdeq, List.map_cons, List.tail_cons,
              show (x' :: xs')[((⟨j, hjlt⟩ : Fin (xs'.length + 1)) : ℕ)]
                = σ ((x :: xs)[(i : ℕ)]) from hjeq]
            refine ih _ ((x :: xs).eraseIdx i) ((x' :: xs').eraseIdx j) ?_ ?_
              (hnd.eraseIdx _) (hnd'.eraseIdx _) (fun y => ?_) _ hrest
            · rw [List.length_eraseIdx_of_lt hi]; simpa using hl
            · rw [List.length_eraseIdx_of_lt hj]; simpa using hl'
            · rw [mem_eraseIdx_iff_of_nodup hnd hi, mem_eraseIdx_iff_of_nodup hnd' hj, hjeq,
                hcorr y]
              exact and_congr_right fun _ => not_congr σ.injective.eq_iff.symm

/-- A permutation preserving acceptance and the pool's values maps runs to runs, bijectively. -/
theorem map_mem_support_drawUntil_iff (accept : S → Bool) (σ : Equiv.Perm S)
    (hacc : ∀ y, accept (σ y) = accept y) (r : ℕ) (l : List S) (hnd : l.Nodup)
    (hmem : ∀ y, σ y ∈ l ↔ y ∈ l) {d : List S} :
    d.map σ ∈ support (drawUntil accept r l) ↔ d ∈ support (drawUntil accept r l) := by
  have hfun : (fun y => accept (σ y)) = accept := funext hacc
  have hfun' : (fun y => accept (σ.symm y)) = accept := by
    funext y; rw [← hacc (σ.symm y), Equiv.apply_symm_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := map_mem_support_drawUntil accept σ.symm l.length r l l rfl rfl hnd hnd
      (fun y => by rw [← hmem (σ.symm y), Equiv.apply_symm_apply]) _ (by rwa [hfun'])
    simpa [List.map_map, Function.comp_def] using this
  · exact map_mem_support_drawUntil accept σ l.length r l l rfl rfl hnd hnd
      (fun y => (hmem y).symm) d (by rwa [hfun])

/-- Relabelling by a permutation that preserves acceptance and the pool's values leaves the law
alone. -/
theorem evalDist_drawUntil_map_perm (accept : S → Bool) (σ : Equiv.Perm S)
    (hacc : ∀ y, accept (σ y) = accept y) (r : ℕ) (l : List S) (hnd : l.Nodup)
    (hmem : ∀ y, σ y ∈ l ↔ y ∈ l) :
    evalDist ((·.map σ) <$> drawUntil accept r l) = evalDist (drawUntil accept r l) := by
  classical
  have hinj : Function.Injective (fun d : List S => d.map σ) :=
    fun d₁ d₂ h => by simpa [List.map_map, Function.comp_def] using congrArg (·.map σ.symm) h
  refine evalDist_ext fun d => ?_
  by_cases hd : d ∈ support (drawUntil accept r l)
  · have hpre : (d.map σ.symm).map σ = d := by simp [List.map_map, Function.comp_def]
    have hmem' : (d.map σ.symm) ∈ support (drawUntil accept r l) := by
      refine (map_mem_support_drawUntil_iff accept σ hacc r l hnd hmem).mp ?_
      rw [hpre]; exact hd
    have hL := probOutput_map_injective (drawUntil accept r l) hinj (d.map σ.symm)
    rw [hpre] at hL
    rw [hL, probOutput_drawUntil accept l.length r l rfl hnd _ hmem',
      probOutput_drawUntil accept l.length r l rfl hnd d hd, List.length_map]
  · rw [probOutput_eq_zero_of_not_mem_support hd]
    refine probOutput_eq_zero_of_not_mem_support fun h => hd ?_
    rw [support_map] at h
    obtain ⟨d', hd', rfl⟩ := h
    exact (map_mem_support_drawUntil_iff accept σ hacc r l hnd hmem).mpr hd'

private theorem probEvent_congr_of_evalDist_eq {α : Type} {mx my : ProbComp α}
    (h : evalDist mx = evalDist my) (p : α → Prop) : Pr[p | mx] = Pr[p | my] := by
  rw [probEvent_def, probEvent_def, h]

/-! ## Expected number of draws -/

/-- **Exchangeability.** Two values of the pool that the acceptance test cannot tell apart are
equally likely to be drawn. -/
theorem probEvent_mem_drawUntil_congr (accept : S → Bool) (r : ℕ) (l : List S) (hnd : l.Nodup)
    {a b : S} (ha : a ∈ l) (hb : b ∈ l) (hab : accept a = accept b) :
    Pr[fun d => a ∈ d | drawUntil accept r l] = Pr[fun d => b ∈ d | drawUntil accept r l] := by
  letI : DecidableEq S := Classical.decEq S
  set σ : Equiv.Perm S := Equiv.swap a b with hσ
  have hacc : ∀ y, accept (σ y) = accept y := by
    intro y
    rcases eq_or_ne y a with rfl | hya
    · rw [hσ, Equiv.swap_apply_left, hab]
    rcases eq_or_ne y b with rfl | hyb
    · rw [hσ, Equiv.swap_apply_right, hab]
    · rw [hσ, Equiv.swap_apply_of_ne_of_ne hya hyb]
  have hmem : ∀ y, σ y ∈ l ↔ y ∈ l := by
    intro y
    rcases eq_or_ne y a with rfl | hya
    · rw [hσ, Equiv.swap_apply_left]; exact ⟨fun _ => ha, fun _ => hb⟩
    rcases eq_or_ne y b with rfl | hyb
    · rw [hσ, Equiv.swap_apply_right]; exact ⟨fun _ => hb, fun _ => ha⟩
    · rw [hσ, Equiv.swap_apply_of_ne_of_ne hya hyb]
  have hpred : (fun d : List S => b ∈ d) ∘ (·.map σ) = fun d : List S => a ∈ d := by
    funext d
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨z, hz, hzb⟩ := List.mem_map.mp h
      have hza : z = a := by
        have hzz := congrArg σ hzb
        rwa [hσ, Equiv.swap_apply_self, Equiv.swap_apply_right] at hzz
      exact hza ▸ hz
    · exact List.mem_map.mpr ⟨a, h, by rw [hσ, Equiv.swap_apply_left]⟩
  have hlaw := evalDist_drawUntil_map_perm accept σ hacc r l hnd hmem
  rw [← probEvent_congr_of_evalDist_eq hlaw (fun d => b ∈ d), probEvent_map, hpred]

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

open OracleComp.EvalDist in
/-- The loop's expected number of draws is the negative hypergeometric expectation at the pool's
size and accepting count. -/
theorem expectedValue_length_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n →
      expectedValue (drawUntil accept r l) (fun d => (d.length : ℝ≥0∞))
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
            expectedValue ((((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) :: ·) <$>
                drawUntil accept
                  (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then r else r + 1)
                  ((x :: xs).eraseIdx i)) (fun d => (d.length : ℝ≥0∞))
              = (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then
                  NegHypergeom.expectedDraws xs.length (G - 1) r
                else NegHypergeom.expectedDraws xs.length G (r + 1)) + 1 := by
          intro i
          have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
          have hlen : ((x :: xs).eraseIdx i).length = xs.length := by
            rw [List.length_eraseIdx_of_lt hi]; simp
          rw [expectedValue_length_cons_map, ih _ _ hlen]
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
        rw [drawUntil_cons, expectedValue_bind, expectedValue_def]
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

open OracleComp.EvalDist in
/-- The closed-form bound on the loop's expected number of draws. Exhaustion is covered: when the
pool holds fewer than `r` accepting values the loop draws all of it, and the bound still holds. -/
theorem expectedValue_length_drawUntil_le (accept : S → Bool) (r : ℕ) (l : List S) :
    expectedValue (drawUntil accept r l) (fun d => (d.length : ℝ≥0∞))
      ≤ r * (l.length + 1) / (l.countP accept + 1) := by
  rw [expectedValue_length_drawUntil accept l.length r l rfl]
  exact NegHypergeom.expectedDraws_le List.countP_le_length

/-! ## Per-element draw probabilities

Exchangeability pins the individual draw probabilities down completely, once the two aggregate
totals are known: over the whole pool they sum to the expected number of draws, and over the
pool's accepting values they sum to the number of accepting draws the loop makes — which is its
budget or the pool's supply, whichever is smaller. -/

open OracleComp.EvalDist in
/-- The weighted total of what a run drew, resolved into per-value draw probabilities. -/
theorem expectedValue_sum_map_drawUntil [DecidableEq S] (accept : S → Bool) (r : ℕ) (l : List S)
    (hnd : l.Nodup) (g : S → ℝ≥0∞) :
    expectedValue (drawUntil accept r l) (fun d => (d.map g).sum)
      = ∑ x ∈ l.toFinset, g x * Pr[fun d => x ∈ d | drawUntil accept r l] := by
  classical
  have hpt : ∀ d ∈ support (drawUntil accept r l),
      (d.map g).sum = ∑ x ∈ l.toFinset, (if x ∈ d then g x else 0) := by
    intro d hd
    have hsub : ∀ y ∈ d, y ∈ l := mem_of_mem_support_drawUntil accept l.length r l rfl d hd
    have hdn : d.Nodup := nodup_of_mem_support_drawUntil accept l.length r l rfl hnd d hd
    rw [← Finset.sum_filter, show l.toFinset.filter (fun x => x ∈ d) = d.toFinset from
      Finset.ext fun x => by
        simp only [Finset.mem_filter, List.mem_toFinset]
        exact ⟨fun h => h.2, fun h => ⟨hsub x h, h⟩⟩]
    exact (List.sum_toFinset g hdn).symm
  rw [expectedValue_congr_of_mem_support _ hpt, expectedValue_finsetSum]
  exact Finset.sum_congr rfl fun x _ => expectedValue_ite _ _ _

open OracleComp.EvalDist in
/-- Summed over the pool, the draw probabilities are the expected number of draws. -/
theorem sum_probEvent_mem_drawUntil [DecidableEq S] (accept : S → Bool) (r : ℕ) (l : List S)
    (hnd : l.Nodup) :
    ∑ x ∈ l.toFinset, Pr[fun d => x ∈ d | drawUntil accept r l]
      = NegHypergeom.expectedDraws l.length (l.countP accept) r := by
  classical
  have h := expectedValue_sum_map_drawUntil accept r l hnd (fun _ => (1 : ℝ≥0∞))
  simp only [one_mul] at h
  have hcong : expectedValue (drawUntil accept r l)
        (fun d => ((d.map (fun _ => (1 : ℝ≥0∞))).sum))
      = expectedValue (drawUntil accept r l) (fun d => (d.length : ℝ≥0∞)) :=
    expectedValue_congr_of_mem_support _ fun d _ => by simp
  rw [← h, hcong, expectedValue_length_drawUntil accept l.length r l rfl]

open OracleComp.EvalDist in
/-- Summed over the pool's accepting values, they are the number of accepting values the loop
collects: its budget, or the pool's supply. -/
theorem sum_probEvent_mem_drawUntil_accept [DecidableEq S] (accept : S → Bool) (r : ℕ)
    (l : List S) (hnd : l.Nodup) :
    ∑ x ∈ l.toFinset.filter (fun x => accept x), Pr[fun d => x ∈ d | drawUntil accept r l]
      = ((min r (l.countP accept) : ℕ) : ℝ≥0∞) := by
  classical
  have hg := expectedValue_sum_map_drawUntil accept r l hnd (fun x => if accept x then 1 else 0)
  rw [Finset.sum_filter]
  simp only [ite_mul, one_mul, zero_mul] at hg
  rw [← hg, expectedValue_congr_of_mem_support _ (fun d hd => ?_),
    expectedValue_const (neverFail_drawUntil accept l.length r l rfl).probFailure_eq_zero]
  rw [show ((d.map fun x => if accept x then (1 : ℝ≥0∞) else 0).sum)
      = ((d.countP accept : ℕ) : ℝ≥0∞) from ?_,
    countP_of_mem_support_drawUntil accept l.length r l rfl d hd]
  clear hd
  induction d with
  | nil => simp
  | cons y ys ihd =>
      rw [List.map_cons, List.sum_cons, ihd, List.countP_cons]
      cases hy : accept y
      · simp
      · simp
        ring

private theorem card_filter_toFinset [DecidableEq S] (l : List S) (hnd : l.Nodup) (p : S → Bool) :
    (l.toFinset.filter (fun x => p x)).card = l.countP p := by
  classical
  rw [← List.toFinset_filter, List.toFinset_card_of_nodup (hnd.filter _),
    List.countP_eq_length_filter]

open OracleComp.EvalDist in
/-- **The accepting values are drawn with equal probability**, so each is drawn as often as the
loop's accepting draws allow, divided by the pool's supply of them. -/
theorem probEvent_mem_drawUntil_mul_countP (accept : S → Bool) (r : ℕ)
    (l : List S) (hnd : l.Nodup) {x : S} (hx : x ∈ l) (hacc : accept x) :
    Pr[fun d => x ∈ d | drawUntil accept r l] * (l.countP accept : ℝ≥0∞)
      = ((min r (l.countP accept) : ℕ) : ℝ≥0∞) := by
  letI : DecidableEq S := Classical.decEq S
  have hconst : ∀ y ∈ l.toFinset.filter (fun y => accept y),
      Pr[fun d => y ∈ d | drawUntil accept r l]
        = Pr[fun d => x ∈ d | drawUntil accept r l] := by
    intro y hy
    rw [Finset.mem_filter, List.mem_toFinset] at hy
    exact probEvent_mem_drawUntil_congr accept r l hnd hy.1 hx (by rw [hy.2, hacc])
  rw [← sum_probEvent_mem_drawUntil_accept accept r l hnd, Finset.sum_congr rfl hconst,
    Finset.sum_const, card_filter_toFinset l hnd accept, nsmul_eq_mul, mul_comm]

open OracleComp.EvalDist in
/-- The rejecting values likewise, with the loop's remaining draws to share out. -/
theorem probEvent_mem_drawUntil_mul_countP_not (accept : S → Bool) (r : ℕ)
    (l : List S) (hnd : l.Nodup) {x : S} (hx : x ∈ l) (hrej : accept x = false) :
    Pr[fun d => x ∈ d | drawUntil accept r l] * (l.countP (fun y => !accept y) : ℝ≥0∞)
        + ((min r (l.countP accept) : ℕ) : ℝ≥0∞)
      = NegHypergeom.expectedDraws l.length (l.countP accept) r := by
  letI : DecidableEq S := Classical.decEq S
  have hconst : ∀ y ∈ l.toFinset.filter (fun y => ¬ (accept y = true)),
      Pr[fun d => y ∈ d | drawUntil accept r l]
        = Pr[fun d => x ∈ d | drawUntil accept r l] := by
    intro y hy
    rw [Finset.mem_filter, List.mem_toFinset] at hy
    exact probEvent_mem_drawUntil_congr accept r l hnd hy.1 hx
      (by rw [hrej, Bool.eq_false_iff]; exact fun h => hy.2 h)
  have hcard : (l.toFinset.filter (fun y => ¬ (accept y = true))).card
      = l.countP (fun y => !accept y) := by
    rw [← card_filter_toFinset l hnd (fun y => !accept y)]
    exact congrArg Finset.card (Finset.filter_congr fun y _ => by simp)
  rw [← sum_probEvent_mem_drawUntil accept r l hnd,
    ← Finset.sum_filter_add_sum_filter_not l.toFinset (fun y => accept y),
    sum_probEvent_mem_drawUntil_accept accept r l hnd, Finset.sum_congr rfl hconst,
    Finset.sum_const, nsmul_eq_mul, hcard]
  ring

/-! ## The column bound

A *column* is a coordinate's worth of values: `Fintype.card S` of them, of which `countP` accept.
A resampling loop centred on an accepting value `v` draws from the rest of the column, so across
all the accepting centres a fixed value `x` can be drawn many times over.
`sum_probEvent_mem_erase_le` says it is drawn at most `r` times in total — the same budget one loop
has.

That is the counting step of a *weighted* cost bound: charge each drawn value a weight, and the
column's total charge is at most `r` times the column's total weight, whatever the weights are. -/

section Column

variable [DecidableEq S] [Fintype S]

omit [DecidableEq S] [Fintype S] in
open OracleComp.EvalDist in
theorem probEvent_mem_drawUntil_eq_zero (a : S → Bool) (r : ℕ) (l : List S) {x : S}
    (hx : x ∉ l) : Pr[fun d => x ∈ d | drawUntil a r l] = 0 :=
  probEvent_eq_zero fun d hd hxd =>
    hx (mem_of_mem_support_drawUntil a l.length r l rfl d hd x hxd)

theorem countP_toList_erase (a : S → Bool) {v : S} (hv : a v) :
    ((Finset.univ.erase v).toList).countP a = (Finset.univ.filter fun y => a y).card - 1 := by
  classical
  have hmem : v ∈ Finset.univ.filter (fun y => a y) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
  rw [Finset.countP_toList,
    show (Finset.univ.erase v).filter (fun y => a y)
      = (Finset.univ.filter fun y => a y).erase v from by
        refine Finset.ext fun y => ?_
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
        tauto,
    Finset.card_erase_of_mem hmem]

theorem length_toList_erase (v : S) :
    ((Finset.univ.erase v).toList).length = Fintype.card S - 1 := by
  rw [Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

theorem countP_not_toList_erase (a : S → Bool) {v : S} (hv : a v) :
    ((Finset.univ.erase v).toList).countP (fun y => !a y)
      = Fintype.card S - (Finset.univ.filter fun y => a y).card := by
  have hlen := List.length_eq_countP_add_countP_not ((Finset.univ.erase v).toList) a
  rw [length_toList_erase, countP_toList_erase a hv] at hlen
  have hHpos : 0 < (Finset.univ.filter fun y => a y).card :=
    Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  have hHle : (Finset.univ.filter fun y => a y).card ≤ Fintype.card S := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.filter_subset _ _)
  have hNpos : 0 < Fintype.card S := lt_of_lt_of_le hHpos hHle
  omega

open OracleComp.EvalDist in
/-- **The column bound.** Summed over the accepting centres of a column, the chance that a
resampling loop starting there draws a fixed value `x` is at most the loop's own budget. -/
theorem sum_probEvent_mem_erase_le (a : S → Bool) (r : ℕ) (x : S) :
    ∑ v ∈ Finset.univ.filter (fun v => a v),
        Pr[fun d => x ∈ d | drawUntil a r ((Finset.univ.erase v).toList)]
      ≤ (r : ℝ≥0∞) := by
  classical
  set A : Finset S := Finset.univ.filter (fun v => a v) with hA
  set H : ℕ := A.card with hH
  set N : ℕ := Fintype.card S with hN
  have hHle : H ≤ N := by
    have hc : A.card ≤ (Finset.univ : Finset S).card :=
      Finset.card_le_card (by rw [hA]; exact Finset.filter_subset _ _)
    simpa [hH, hN] using hc
  set P : ℝ≥0∞ :=
    ∑ v ∈ A, Pr[fun d => x ∈ d | drawUntil a r ((Finset.univ.erase v).toList)] with hP
  by_cases hax : a x
  · -- `x` accepts: only the other `H - 1` accepting centres can draw it, and they share out the
    -- loop's accepting draws.
    have hxA : x ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax⟩
    rcases Nat.lt_or_ge H 2 with hH1 | hH2
    · have hAx : A = {x} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hxA, fun y hy => Finset.card_le_one.mp (by omega) y hy x hxA⟩
      rw [hP, hAx, Finset.sum_singleton, probEvent_mem_drawUntil_eq_zero a r _ (by simp)]
      exact zero_le
    · have hterm : ∀ v ∈ A,
          Pr[fun d => x ∈ d | drawUntil a r ((Finset.univ.erase v).toList)]
              * ((H - 1 : ℕ) : ℝ≥0∞)
            = if v = x then 0 else ((min r (H - 1) : ℕ) : ℝ≥0∞) := by
        intro v hv
        have hav : a v := (Finset.mem_filter.mp hv).2
        by_cases hvx : v = x
        · rw [if_pos hvx, hvx, probEvent_mem_drawUntil_eq_zero a r _ (by simp), zero_mul]
        · rw [if_neg hvx, ← countP_toList_erase a hav]
          exact probEvent_mem_drawUntil_mul_countP a r _ (Finset.nodup_toList _)
            (by simp [Ne.symm hvx]) hax
      have hsum : P * ((H - 1 : ℕ) : ℝ≥0∞)
          = ((H - 1 : ℕ) : ℝ≥0∞) * ((min r (H - 1) : ℕ) : ℝ≥0∞) := by
        rw [hP, Finset.sum_mul, Finset.sum_congr rfl hterm, ← Finset.sum_erase_add A _ hxA,
          if_pos rfl, add_zero,
          Finset.sum_congr rfl (fun v hv => if_neg (Finset.ne_of_mem_erase hv)),
          Finset.sum_const, Finset.card_erase_of_mem hxA, nsmul_eq_mul]
      refine (ENNReal.mul_le_mul_iff_left
        (show ((H - 1 : ℕ) : ℝ≥0∞) ≠ 0 by exact_mod_cast (by omega : (H - 1 : ℕ) ≠ 0))
        (by finiteness)).mp ?_
      rw [hsum, mul_comm]
      exact mul_le_mul' (by exact_mod_cast Nat.min_le_left r (H - 1)) le_rfl
  · -- `x` rejects: every accepting centre can draw it.
    have hxA : x ∉ A := fun h => hax (Finset.mem_filter.mp h).2
    have hHlt : H < N := by
      refine lt_of_le_of_ne hHle fun h => hxA ?_
      have hAu : A = Finset.univ := Finset.eq_univ_of_card A (by rw [← hH, h, hN])
      rw [hAu]
      exact Finset.mem_univ _
    rcases Nat.lt_or_ge r H with hrH | hHr
    · have hterm : ∀ v ∈ A,
          Pr[fun d => x ∈ d | drawUntil a r ((Finset.univ.erase v).toList)]
              * ((N - H : ℕ) : ℝ≥0∞) + (r : ℝ≥0∞)
            = NegHypergeom.expectedDraws (N - 1) (H - 1) r := by
        intro v hv
        have hav : a v := (Finset.mem_filter.mp hv).2
        have h := probEvent_mem_drawUntil_mul_countP_not a r ((Finset.univ.erase v).toList)
          (Finset.nodup_toList _) (x := x)
          (by
            have hne : x ≠ v := fun h => hax (by rw [h]; exact hav)
            simp [hne])
          (by simpa using hax)
        rwa [countP_not_toList_erase a hav, countP_toList_erase a hav, length_toList_erase,
          show min r (H - 1) = r from Nat.min_eq_left (by omega)] at h
      have hED : (H : ℝ≥0∞) * NegHypergeom.expectedDraws (N - 1) (H - 1) r
          = (r : ℝ≥0∞) * N := by
        have h := NegHypergeom.mul_expectedDraws (N - 1) (H - 1) r (by omega) (by omega)
        have hc1 : ((H - 1 : ℕ) : ℝ≥0∞) + 1 = (H : ℝ≥0∞) := by
          have hh : (H - 1 : ℕ) + 1 = H := by omega
          exact_mod_cast congrArg (fun n : ℕ => (n : ℝ≥0∞)) hh
        have hc2 : ((N - 1 : ℕ) : ℝ≥0∞) + 1 = (N : ℝ≥0∞) := by
          have hh : (N - 1 : ℕ) + 1 = N := by omega
          exact_mod_cast congrArg (fun n : ℕ => (n : ℝ≥0∞)) hh
        rwa [hc1, hc2] at h
      have hstep : P * ((N - H : ℕ) : ℝ≥0∞) + (H : ℝ≥0∞) * (r : ℝ≥0∞) = (r : ℝ≥0∞) * N := by
        have h1 := Finset.sum_congr rfl hterm
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.sum_const,
          nsmul_eq_mul, nsmul_eq_mul, ← hP, ← hH, hED] at h1
        exact h1
      have hrN : (r : ℝ≥0∞) * N
          = (r : ℝ≥0∞) * ((N - H : ℕ) : ℝ≥0∞) + (H : ℝ≥0∞) * (r : ℝ≥0∞) := by
        have hc : (N : ℝ≥0∞) = ((N - H : ℕ) : ℝ≥0∞) + (H : ℝ≥0∞) := by
          have hh : N = (N - H : ℕ) + H := by omega
          exact_mod_cast congrArg (fun n : ℕ => (n : ℝ≥0∞)) hh
        rw [hc, mul_add, mul_comm (r : ℝ≥0∞) (H : ℝ≥0∞)]
      rw [hrN] at hstep
      have hP' : P * ((N - H : ℕ) : ℝ≥0∞) = (r : ℝ≥0∞) * ((N - H : ℕ) : ℝ≥0∞) :=
        (ENNReal.add_left_inj (by finiteness)).mp hstep
      refine (ENNReal.mul_le_mul_iff_left
        (show ((N - H : ℕ) : ℝ≥0∞) ≠ 0 by exact_mod_cast (by omega : (N - H : ℕ) ≠ 0))
        (by finiteness)).mp (le_of_eq hP')
    · calc P ≤ ∑ _v ∈ A, (1 : ℝ≥0∞) := Finset.sum_le_sum fun v _ => probEvent_le_one
        _ = (H : ℝ≥0∞) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hH]
        _ ≤ (r : ℝ≥0∞) := by exact_mod_cast hHr

open OracleComp.EvalDist in
/-- **The weighted column bound.** Charge every drawn value a weight; summed over the accepting
centres, a column's expected charge is at most `r` times the column's total weight, whatever the
weights are.

This is the form a weighted cost bound consumes: `sum_probEvent_mem_erase_le` says no value is
drawn more than `r` times across the centres, and weights are then just linear. -/
theorem sum_expectedValue_sum_map_erase_le (a : S → Bool) (r : ℕ) (g : S → ℝ≥0∞) :
    ∑ v ∈ Finset.univ.filter (fun v => a v),
        expectedValue (drawUntil a r ((Finset.univ.erase v).toList))
          (fun d => (d.map g).sum)
      ≤ (r : ℝ≥0∞) * ∑ x : S, g x := by
  classical
  have hterm : ∀ v : S,
      expectedValue (drawUntil a r ((Finset.univ.erase v).toList)) (fun d => (d.map g).sum)
        = ∑ x : S, g x * Pr[fun d => x ∈ d | drawUntil a r ((Finset.univ.erase v).toList)] := by
    intro v
    rw [expectedValue_sum_map_drawUntil a r _ (Finset.nodup_toList _) g,
      Finset.toList_toFinset]
    refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
    have hxv : x = v := by
      by_contra hne
      exact hx (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
    rw [hxv, probEvent_mem_drawUntil_eq_zero a r _ (by simp), mul_zero]
  calc ∑ v ∈ Finset.univ.filter (fun v => a v),
        expectedValue (drawUntil a r ((Finset.univ.erase v).toList)) (fun d => (d.map g).sum)
      = ∑ v ∈ Finset.univ.filter (fun v => a v), ∑ x : S,
          g x * Pr[fun d => x ∈ d | drawUntil a r ((Finset.univ.erase v).toList)] :=
        Finset.sum_congr rfl fun v _ => hterm v
    _ = ∑ x : S, g x * ∑ v ∈ Finset.univ.filter (fun v => a v),
          Pr[fun d => x ∈ d | drawUntil a r ((Finset.univ.erase v).toList)] := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum ..).symm
    _ ≤ ∑ x : S, g x * (r : ℝ≥0∞) :=
        Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (sum_probEvent_mem_erase_le a r x)
    _ = (r : ℝ≥0∞) * ∑ x : S, g x := by rw [← Finset.sum_mul, mul_comm]

end Column

end ProbComp
