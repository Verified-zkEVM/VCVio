/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Norm bounds for commutators in a normed ring

The commutator `⁅a, b⁆ = a * b - b * a` of a ring is a derivation in each argument. In a
seminormed ring this gives the Leibniz bounds `norm_lie_mul_le` and `norm_mul_lie_le`, and by
induction the bound `norm_lie_list_prod_le` on the commutator with a product of elements of norm
at most one by the sum of the norms of the individual commutators.
-/

public section

section Ring

variable {R : Type*} [Ring R]

/-- The commutator with a fixed element is a derivation: `⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆`. -/
theorem Ring.lie_mul_eq (a b c : R) : ⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆ := by
  simp only [Ring.lie_def, mul_sub, sub_mul, mul_assoc]
  abel

/-- The commutator is a derivation in its first argument:
`⁅a * b, c⁆ = a * ⁅b, c⁆ + ⁅a, c⁆ * b`. -/
theorem Ring.mul_lie_eq (a b c : R) : ⁅a * b, c⁆ = a * ⁅b, c⁆ + ⁅a, c⁆ * b := by
  simp only [Ring.lie_def, mul_sub, sub_mul, mul_assoc]
  abel

/-- Every element commutes with one. -/
theorem Ring.lie_one (a : R) : ⁅a, (1 : R)⁆ = 0 := by
  simp [Ring.lie_def]

end Ring

section SeminormedRing

variable {R : Type*} [SeminormedRing R]

/-- Leibniz bound for the commutator with a product. -/
theorem norm_lie_mul_le (a b c : R) : ‖⁅a, b * c⁆‖ ≤ ‖⁅a, b⁆‖ * ‖c‖ + ‖b‖ * ‖⁅a, c⁆‖ := by
  rw [Ring.lie_mul_eq]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

/-- Leibniz bound for the commutator of a product. -/
theorem norm_mul_lie_le (a b c : R) : ‖⁅a * b, c⁆‖ ≤ ‖a‖ * ‖⁅b, c⁆‖ + ‖⁅a, c⁆‖ * ‖b‖ := by
  rw [Ring.mul_lie_eq]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

/-- A product of elements of norm at most one has norm at most one, provided the unit does. -/
theorem List.norm_prod_le_one (h1 : ‖(1 : R)‖ ≤ 1) (l : List R) (hl : ∀ b ∈ l, ‖b‖ ≤ 1) :
    ‖l.prod‖ ≤ 1 := by
  induction l with
  | nil => simpa using h1
  | cons b l ih =>
    rw [List.prod_cons]
    exact (norm_mul_le _ _).trans <| (mul_le_mul (hl b List.mem_cons_self)
      (ih fun c hc ↦ hl c (List.mem_cons_of_mem b hc)) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)

/-- Telescoped Leibniz bound: the commutator of `a` with a product of elements of norm at most
one is bounded by the sum of the norms of the commutators of `a` with the factors. -/
theorem norm_lie_list_prod_le (a : R) (l : List R)
    (hl : ∀ b ∈ l, ‖b‖ ≤ 1) : ‖⁅a, l.prod⁆‖ ≤ (l.map fun b ↦ ‖⁅a, b⁆‖).sum := by
  induction l with
  | nil => simp [Ring.lie_one]
  | cons b l ih =>
    have hl' : ∀ c ∈ l, ‖c‖ ≤ 1 := fun c hc ↦ hl c (List.mem_cons_of_mem b hc)
    cases l with
    | nil => simp
    | cons c l =>
      have hprod : ‖(c :: l).prod‖ ≤ 1 :=
        (List.norm_prod_le' (List.cons_ne_nil c l)).trans <|
          (le_abs_self _).trans <| List.norm_prod_le_one (R := ℝ) (by norm_num)
            ((c :: l).map norm) (by
            simpa using hl')
      rw [List.prod_cons, List.map_cons, List.sum_cons]
      refine (norm_lie_mul_le a b (c :: l).prod).trans (add_le_add ?_ ?_)
      · exact mul_le_of_le_one_right (norm_nonneg _) hprod
      · exact (mul_le_of_le_one_left (norm_nonneg _) (hl b List.mem_cons_self)).trans (ih hl')

end SeminormedRing
