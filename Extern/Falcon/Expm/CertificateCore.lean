/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Chebyshev certificates checked by kernel evaluation

A bound `|f x| ≤ B` on an interval, for a function `f` whose scaled form `D * f` is an integer
polynomial, reduces to finite integer arithmetic. Parameterise the interval as
`x = (p + q * y) / s` with `y ∈ [-1, 1]`, and expand `D * s ^ n * f ((p + q * y) / s)` in the
Chebyshev basis as `∑ j, N j * T j y`. Then `|T j y| ≤ 1` gives
`D * s ^ n * |f x| ≤ ∑ j, |N j|`, and all the cancellation that makes the bound tight lives in the
integer coefficients `N`.

This module proves that reduction once, over integer polynomials represented as coefficient
lists (`IntPoly`):

* `IntPoly.homog` computes the affine substitution `s ^ n * P ((p + q * y) / s)` as an integer
  polynomial in `y`, and `IntPoly.chebComb` computes `∑ j, N j * T j` in the monomial basis;
* `ChebCert.check` is a `Bool`-valued test comparing the two and bounding `∑ j, |N j|`;
* `ChebCert.abs_le_of_check` turns a successful check into the real-valued bound, and
  `ChebCert.exists_mem_of_coverChain` covers an interval by a chain of certificates.

A certificate is then data plus one `decide +kernel` proof that the check succeeds, which the
kernel discharges with GMP-accelerated integer arithmetic instead of normalising a degree-`n`
real polynomial identity with `ring`.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Polynomial

/-- An integer polynomial as its coefficient list, lowest degree first. -/
abbrev IntPoly := List ℤ

namespace IntPoly

/-- Coefficient-wise sum, padding the shorter list with zeros. -/
@[expose] def add : IntPoly → IntPoly → IntPoly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

/-- Scalar multiple. -/
@[expose] def smul (c : ℤ) (p : IntPoly) : IntPoly := p.map (c * ·)

/-- Product. The two-element base case keeps products free of trailing zeros. -/
@[expose] def mul : IntPoly → IntPoly → IntPoly
  | [], _ => []
  | [a], q => smul a q
  | a :: b :: p, q => add (smul a q) (0 :: mul (b :: p) q)

/-- Evaluation at a real point, by Horner's rule. -/
@[expose] noncomputable def eval (y : ℝ) : IntPoly → ℝ
  | [] => 0
  | a :: p => a + y * eval y p

@[simp] theorem eval_nil (y : ℝ) : eval y [] = 0 := rfl

@[simp] theorem eval_cons (y : ℝ) (a : ℤ) (p : IntPoly) :
    eval y (a :: p) = a + y * eval y p := rfl

theorem eval_add (y : ℝ) : ∀ p q : IntPoly, eval y (add p q) = eval y p + eval y q
  | [], q => by simp [add]
  | a :: p, [] => by simp [add]
  | a :: p, b :: q => by
    simp only [add, eval_cons, eval_add y p q]
    push_cast
    ring

theorem eval_smul (y : ℝ) (c : ℤ) : ∀ p : IntPoly, eval y (smul c p) = c * eval y p
  | [] => by simp [smul]
  | a :: p => by
    have ih := eval_smul y c p
    simp only [smul, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    push_cast
    ring

theorem eval_mul (y : ℝ) : ∀ p q : IntPoly, eval y (mul p q) = eval y p * eval y q
  | [], q => by simp [mul]
  | [a], q => by simp [mul, eval_smul]
  | a :: b :: p, q => by
    have ih := eval_mul y (b :: p) q
    rw [mul, eval_add, eval_smul, eval_cons, ih, eval_cons (p := b :: p)]
    push_cast
    ring

/-- The affine substitution `x = (p + q * y) / s`, with the denominator cleared:
`homog p q s P` is the integer polynomial in `y` equal to `s ^ (P.length - 1) * P x`
(see `eval_homog`). -/
@[expose] def homog (p q s : ℤ) : IntPoly → IntPoly
  | [] => []
  | a :: c => add [a * s ^ c.length] (mul [p, q] (homog p q s c))

theorem eval_homog (p q s : ℤ) (hs : (s : ℝ) ≠ 0) (y : ℝ) :
    ∀ c : IntPoly, (s : ℝ) * eval y (homog p q s c)
      = (s : ℝ) ^ c.length * eval (((p : ℝ) + q * y) / s) c
  | [] => by simp [homog]
  | a :: c => by
    have ih := eval_homog p q s hs y c
    set x := ((p : ℝ) + q * y) / s
    have hx : (s : ℝ) * x = p + q * y := by simp only [x]; field_simp
    simp only [homog, eval_add, eval_mul, eval_cons, eval_nil, List.length_cons, pow_succ]
    push_cast
    linear_combination ((p : ℝ) + y * q) * ih - (s : ℝ) ^ c.length * eval x c * hx

/-- The Chebyshev recurrence `T (k + 2) = 2 * X * T (k + 1) - T k` on coefficient lists. -/
@[expose] def chebNext (t₀ t₁ : IntPoly) : IntPoly := add (0 :: smul 2 t₁) (smul (-1) t₀)

/-- `chebComb N t₀ t₁` is `∑ j, N j * T (k + j)` in the monomial basis, given the monomial
forms `t₀ = T k` and `t₁ = T (k + 1)`. -/
@[expose] def chebComb : IntPoly → IntPoly → IntPoly → IntPoly
  | [], _, _ => []
  | a :: N, t₀, t₁ => add (smul a t₀) (chebComb N t₁ (chebNext t₀ t₁))

/-- `∑ j, N j * T (k + j) y`, read off the coefficient list `N`. -/
noncomputable def chebSum (y : ℝ) : IntPoly → ℕ → ℝ
  | [], _ => 0
  | a :: N, k => a * (Chebyshev.T ℝ (k : ℤ)).eval y + chebSum y N (k + 1)

theorem eval_chebNext (y : ℝ) (k : ℕ) {t₀ t₁ : IntPoly}
    (h₀ : eval y t₀ = (Chebyshev.T ℝ (k : ℤ)).eval y)
    (h₁ : eval y t₁ = (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y) :
    eval y (chebNext t₀ t₁) = (Chebyshev.T ℝ ((k + 2 : ℕ) : ℤ)).eval y := by
  rw [chebNext, eval_add, eval_cons, eval_smul, eval_smul, h₀, h₁,
    show ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 by push_cast; ring, Chebyshev.T_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  push_cast
  ring

theorem eval_chebComb (y : ℝ) :
    ∀ (N : IntPoly) (k : ℕ) (t₀ t₁ : IntPoly),
      eval y t₀ = (Chebyshev.T ℝ (k : ℤ)).eval y →
      eval y t₁ = (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y →
      eval y (chebComb N t₀ t₁) = chebSum y N k
  | [], _, _, _, _, _ => by simp [chebComb, chebSum]
  | a :: N, k, t₀, t₁, h₀, h₁ => by
    rw [chebComb, eval_add, eval_smul, h₀, chebSum,
      eval_chebComb y N (k + 1) t₁ _ h₁ (eval_chebNext y k h₀ h₁)]

/-- `∑ j, |N j|`. -/
@[expose] def l1 (N : IntPoly) : ℤ := (N.map fun a => (a.natAbs : ℤ)).sum

theorem abs_chebSum_le {y : ℝ} (hy : |y| ≤ 1) :
    ∀ (N : IntPoly) (k : ℕ), |chebSum y N k| ≤ l1 N
  | [], _ => by simp [chebSum, l1]
  | a :: N, k => by
    have ih := abs_chebSum_le hy N (k + 1)
    have hT := Chebyshev.abs_eval_T_real_le_one (k : ℤ) hy
    simp only [chebSum, l1, List.map_cons, List.sum_cons] at ih ⊢
    push_cast at ih ⊢
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hT) ih

end IntPoly

open IntPoly

/-- A Chebyshev certificate for the interval `[(p - q) / s, (p + q) / s]`: coefficients `N` of
the scaled target in the Chebyshev basis, and the claimed bound. -/
structure ChebCert where
  /-- Numerator of the interval midpoint. -/
  p : ℤ
  /-- Numerator of the interval radius. -/
  q : ℤ
  /-- Common denominator of the midpoint and radius. -/
  s : ℤ
  /-- Chebyshev coefficients of `D * s ^ (P.length - 1) * f ((p + q * y) / s)`. -/
  N : IntPoly
  /-- The claimed bound on `|f|` over the interval. -/
  bound : ℤ

namespace ChebCert

/-- The left endpoint `(p - q) / s`. -/
@[expose] noncomputable def lo (c : ChebCert) : ℝ := ((c.p : ℝ) - c.q) / c.s

/-- The right endpoint `(p + q) / s`. -/
@[expose] noncomputable def hi (c : ChebCert) : ℝ := ((c.p : ℝ) + c.q) / c.s

/-- The finite check behind a certificate for the polynomial `P` with scale `D`: the affine
substitution of `P` equals the Chebyshev combination `N` coefficient for coefficient, and
`s * ∑ |N j| ≤ D * s ^ P.length * bound`. -/
@[expose] def check (P : IntPoly) (D : ℤ) (c : ChebCert) : Bool :=
  decide (0 < c.q) && decide (0 < c.s) &&
    homog c.p c.q c.s P == chebComb c.N [1] [0, 1] &&
    decide (c.s * l1 c.N ≤ D * c.s ^ P.length * c.bound)

/-- **Chebyshev certificate.** If `D * f` is the polynomial `P` and a certificate passes
`check`, then `|f| ≤ bound` on the certificate's interval. -/
theorem abs_le_of_check {f : ℝ → ℝ} {P : IntPoly} {D : ℤ} (hD : 0 < D)
    (hP : ∀ x, (D : ℝ) * f x = eval x P) {c : ChebCert} (hc : c.check P D = true)
    {x : ℝ} (hx₀ : c.lo ≤ x) (hx₁ : x ≤ c.hi) : |f x| ≤ c.bound := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨hq, hs⟩, hid⟩, hl1⟩ := hc
  have hqR : (0 : ℝ) < c.q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < c.s := by exact_mod_cast hs
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  set y := ((c.s : ℝ) * x - c.p) / c.q with hy_def
  have hxy : ((c.p : ℝ) + c.q * y) / c.s = x := by
    rw [hy_def]; field_simp; ring
  have hy : |y| ≤ 1 := by
    rw [lo, div_le_iff₀ hsR] at hx₀
    rw [hi, le_div_iff₀ hsR] at hx₁
    rw [hy_def, abs_div, abs_of_pos hqR, div_le_one hqR, abs_le]
    constructor <;> linarith
  have hev := eval_homog c.p c.q c.s hsR.ne' y P
  rw [hid, hxy, ← hP,
    eval_chebComb y c.N 0 [1] [0, 1] (by simp) (by simp)] at hev
  have hsum := abs_chebSum_le hy c.N 0
  have hl1R : (c.s : ℝ) * l1 c.N ≤ D * (c.s : ℝ) ^ P.length * c.bound := by
    exact_mod_cast hl1
  have hpow : (0 : ℝ) < (c.s : ℝ) ^ P.length := pow_pos hsR _
  have key : (D : ℝ) * (c.s : ℝ) ^ P.length * |f x|
      ≤ (D : ℝ) * (c.s : ℝ) ^ P.length * c.bound := by
    calc (D : ℝ) * (c.s : ℝ) ^ P.length * |f x|
        = |(c.s : ℝ) * chebSum y c.N 0| := by
          rw [hev, abs_mul, abs_mul, abs_of_pos hpow, abs_of_pos hDR]; ring
      _ = (c.s : ℝ) * |chebSum y c.N 0| := by rw [abs_mul, abs_of_pos hsR]
      _ ≤ (c.s : ℝ) * l1 c.N := by gcongr
      _ ≤ _ := hl1R
  exact le_of_mul_le_mul_left key (by positivity)

/-- Consecutive certificates overlap: each one's left endpoint is at most the previous one's
right endpoint, compared by cross-multiplication. -/
@[expose] def coverChain (c : ChebCert) : List ChebCert → Bool
  | [] => true
  | d :: rest => decide ((d.p - d.q) * c.s ≤ (c.p + c.q) * d.s) && coverChain d rest

/-- The last certificate of a chain. -/
@[expose] def last (c : ChebCert) : List ChebCert → ChebCert
  | [] => c
  | d :: rest => last d rest

/-- A chain of overlapping certificates covers the interval from its first left endpoint to its
last right endpoint. -/
theorem exists_mem_of_coverChain :
    ∀ (c : ChebCert) (rest : List ChebCert), coverChain c rest = true →
      (∀ d ∈ c :: rest, 0 < d.s) → ∀ x : ℝ, c.lo ≤ x → x ≤ (last c rest).hi →
      ∃ d ∈ c :: rest, d.lo ≤ x ∧ x ≤ d.hi
  | c, [], _, _, x, h₀, h₁ => ⟨c, List.mem_singleton_self c, h₀, h₁⟩
  | c, d :: rest, hch, hs, x, h₀, h₁ => by
    simp only [coverChain, Bool.and_eq_true, decide_eq_true_eq] at hch
    rcases le_or_gt x c.hi with hx | hx
    · exact ⟨c, List.mem_cons_self .., h₀, hx⟩
    · have hcs : (0 : ℝ) < c.s := by exact_mod_cast hs c List.mem_cons_self
      have hds : (0 : ℝ) < d.s := by
        exact_mod_cast hs d (List.mem_cons_of_mem _ List.mem_cons_self)
      have hdlo : d.lo ≤ c.hi := by
        rw [lo, hi, div_le_div_iff₀ hds hcs]
        exact_mod_cast hch.1
      obtain ⟨e, he, hlo, hhi⟩ := exists_mem_of_coverChain d rest hch.2
        (fun e he => hs e (List.mem_cons_of_mem _ he)) x (by linarith) h₁
      exact ⟨e, List.mem_cons_of_mem _ he, hlo, hhi⟩

/-- Everything a chain of certificates must satisfy to bound `|f|` by `B` on the interval it
covers: each certificate checks against `P` and `D`, each bound is at most `B`, and consecutive
certificates overlap. -/
@[expose] def checkCover (P : IntPoly) (D B : ℤ) (c : ChebCert) (rest : List ChebCert) : Bool :=
  (c :: rest).all (fun d => d.check P D && decide (d.bound ≤ B)) && coverChain c rest

/-- A chain that passes `checkCover` bounds `|f|` by `B` from its first left endpoint to its last
right endpoint. -/
theorem abs_le_of_checkCover {f : ℝ → ℝ} {P : IntPoly} {D B : ℤ} (hD : 0 < D)
    (hP : ∀ x, (D : ℝ) * f x = eval x P) {c : ChebCert} {rest : List ChebCert}
    (h : checkCover P D B c rest = true) {x : ℝ} (hx₀ : c.lo ≤ x) (hx₁ : x ≤ (last c rest).hi) :
    |f x| ≤ B := by
  simp only [checkCover, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hall, hchain⟩ := h
  have hs : ∀ d ∈ c :: rest, 0 < d.s := fun d hd => by
    have := (hall d hd).1
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.2
  obtain ⟨d, hd, hlo, hhi⟩ := exists_mem_of_coverChain c rest hchain hs x hx₀ hx₁
  exact (abs_le_of_check hD hP (hall d hd).1 hlo hhi).trans (by exact_mod_cast (hall d hd).2)

end ChebCert

end Falcon.Concrete.FPRBridge
