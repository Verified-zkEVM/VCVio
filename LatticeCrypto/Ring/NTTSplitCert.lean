/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import LatticeCrypto.Ring.NTTCert
public import LatticeCrypto.Ring.SchoolbookCert

/-!
# Cooley–Tukey Residue Certificates For Blocked NTT Stages

This module relates the blocked butterfly stages of `LatticeCrypto.Ring.NTTCert` to polynomial
reduction. A block of `len` coefficients starting at `base` is read as the polynomial
`∑_{r < len} a[base + r] X^r` (`blockPoly`). One forward layer on the layout `ctLayout` takes
a block congruent to `F` modulo `X^(2·len) − z²` to two half blocks (`forwardStage_ctLayout_dvd`).
They are congruent to `F` modulo `X^len − z` and `X^len + z`. Iterating over `k` layers gives
the Cooley–Tukey residue theorem `forwardStages_ofFn_dvd`: after the last layer, block `g` is
congruent to the input polynomial modulo `X^(N / 2^k) − c k g`. The coefficient formulas
`coeffAt_forwardStage_ctLayout_left` / `_right` and `coeffAt_inverseStage_ctLayout_left` /
`_right` give the output of one forward or inverse layer at each coefficient.

The statement is a divisibility over an arbitrary commutative ring. So it covers both full splits
into linear factors (block size `1`, where it is evaluation at a root) and partial splits into
quadratic factors (block size `2`). The bridge lemmas `X_pow_sub_C_dvd_X_pow_mul_add_one` and
`negacyclicModulus_dvd_toPolynomial_negacyclicMulPure` connect the residues to negacyclic
multiplication.

## References

- NIST FIPS 204, Section 7.5 (NTT and NTT⁻¹)
-/

public section

namespace LatticeCrypto.NTTCert

open Polynomial

variable {R : Type*} [CommRing R]

/-! ## Block polynomials -/

/-- Coefficient `n` of `a`, or `0` past the end. -/
def coeffAt {N : ℕ} (a : Fin N → R) (n : ℕ) : R := if h : n < N then a ⟨n, h⟩ else 0

/-- The polynomial `∑_{r < len} a[base + r] X^r` stored in one block of a coefficient vector. -/
noncomputable def blockPoly {N : ℕ} (a : Fin N → R) (base len : ℕ) : R[X] :=
  ∑ r ∈ Finset.range len, C (coeffAt a (base + r)) * X ^ r

/-- `coeffAt` agrees with `a` inside the range. -/
theorem coeffAt_fin {N : ℕ} (a : Fin N → R) (i : Fin N) : coeffAt a i = a i := by
  simp [coeffAt]

/-- `coeffAt a n` is entry `n` of `a` for `n < N`. -/
theorem coeffAt_of_lt {N : ℕ} (a : Fin N → R) {n : ℕ} (h : n < N) : coeffAt a n = a ⟨n, h⟩ :=
  dite_eq_left h

/-- `coeffAt a n` is `0` for `N ≤ n`. -/
theorem coeffAt_of_le {N : ℕ} (a : Fin N → R) {n : ℕ} (h : N ≤ n) : coeffAt a n = 0 :=
  dite_eq_right (Nat.not_lt.mpr h)

/-- `coeffAt` commutes with pointwise scalar multiplication. -/
theorem coeffAt_scaleCoeffs {N : ℕ} (c : R) (a : Fin N → R) (n : ℕ) :
    coeffAt (scaleCoeffs c a) n = c * coeffAt a n := by
  unfold coeffAt scaleCoeffs
  split_ifs <;> simp

/-- A block of length `m + n` splits into its first `m` and its last `n` coefficients. -/
theorem blockPoly_add_len {N : ℕ} (a : Fin N → R) (base m n : ℕ) :
    blockPoly a base (m + n) = blockPoly a base m + X ^ m * blockPoly a (base + m) n := by
  simp only [blockPoly, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [add_assoc, pow_add]
  ring

/-- A block of length `1` is a constant polynomial. -/
theorem blockPoly_one {N : ℕ} (a : Fin N → R) (i : Fin N) : blockPoly a i 1 = C (a i) := by
  simp [blockPoly, coeffAt_fin]

/-- The full block starting at `0` is the polynomial represented by the backend. -/
theorem blockPoly_zero_eq_toPolynomial (backend : PolyBackend R) (p : backend.Poly) :
    blockPoly (backend.coeff p) 0 backend.degree = backend.toPolynomial p := by
  rw [PolyBackend.toPolynomial, blockPoly,
    ← Fin.sum_univ_eq_sum_range (fun r => C (coeffAt (backend.coeff p) (0 + r)) * X ^ r)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [C_mul_X_pow_eq_monomial, coeffAt_fin]

/-! ## One Cooley–Tukey layer -/

/-- Layer layout: `groups` blocks of `2 * len` coefficients inside `Fin N`. -/
def ctLayout (groups len : ℕ) {N : ℕ} (h : groups * (2 * len) = N) :
    ButterflyLayout (Fin groups × Fin len) (Fin N) where
  equiv := (blockLayout groups len).equiv.trans (finCongr h)

private theorem coeffAt_of_val_eq {N : ℕ} (a : Fin N → R) (j : Fin N) {n : ℕ}
    (hn : j.val = n) : coeffAt a n = a j := by
  subst hn
  exact coeffAt_fin a j

private theorem ctLayout_left_val {groups len N : ℕ} (h : groups * (2 * len) = N)
    (g : Fin groups) (r : Fin len) :
    ((ctLayout groups len h).equiv ((g, r), false)).val = g * (2 * len) + r := by
  simp [ctLayout]

private theorem ctLayout_right_val {groups len N : ℕ} (h : groups * (2 * len) = N)
    (g : Fin groups) (r : Fin len) :
    ((ctLayout groups len h).equiv ((g, r), true)).val = g * (2 * len) + len + r := by
  simp [ctLayout]

/-- Left butterfly output at block coordinates: `u + z·v`. -/
theorem coeffAt_forwardStage_ctLayout_left {groups len N : ℕ} (h : groups * (2 * len) = N)
    (z : Fin groups → R) (a : Fin N → R) (g : Fin groups) {r : ℕ} (hr : r < len) :
    coeffAt (forwardStage (ctLayout groups len h) (fun p => z p.1) a) (g * (2 * len) + r) =
      coeffAt a (g * (2 * len) + r) + z g * coeffAt a (g * (2 * len) + len + r) := by
  have hl := ctLayout_left_val h g ⟨r, hr⟩
  have hrt := ctLayout_right_val h g ⟨r, hr⟩
  rw [coeffAt_of_val_eq _ _ hl, coeffAt_of_val_eq _ _ hl, coeffAt_of_val_eq _ _ hrt]
  simp [forwardStage, forwardButterfly]

/-- Right butterfly output at block coordinates: `u − z·v`. -/
theorem coeffAt_forwardStage_ctLayout_right {groups len N : ℕ} (h : groups * (2 * len) = N)
    (z : Fin groups → R) (a : Fin N → R) (g : Fin groups) {r : ℕ} (hr : r < len) :
    coeffAt (forwardStage (ctLayout groups len h) (fun p => z p.1) a) (g * (2 * len) + len + r) =
      coeffAt a (g * (2 * len) + r) - z g * coeffAt a (g * (2 * len) + len + r) := by
  have hl := ctLayout_left_val h g ⟨r, hr⟩
  have hrt := ctLayout_right_val h g ⟨r, hr⟩
  rw [coeffAt_of_val_eq _ _ hrt, coeffAt_of_val_eq _ _ hl, coeffAt_of_val_eq _ _ hrt]
  simp [forwardStage, forwardButterfly]

/-- Left inverse butterfly output at block coordinates: `u + v`. -/
theorem coeffAt_inverseStage_ctLayout_left {groups len N : ℕ} (h : groups * (2 * len) = N)
    (zInv : Fin groups → R) (a : Fin N → R) (g : Fin groups) {r : ℕ} (hr : r < len) :
    coeffAt (inverseStage (ctLayout groups len h) (fun p => zInv p.1) a) (g * (2 * len) + r) =
      coeffAt a (g * (2 * len) + r) + coeffAt a (g * (2 * len) + len + r) := by
  have hl := ctLayout_left_val h g ⟨r, hr⟩
  have hrt := ctLayout_right_val h g ⟨r, hr⟩
  rw [coeffAt_of_val_eq _ _ hl, coeffAt_of_val_eq _ _ hl, coeffAt_of_val_eq _ _ hrt]
  simp [inverseStage, inverseButterfly]

/-- Right inverse butterfly output at block coordinates: `zInv·(u − v)`. -/
theorem coeffAt_inverseStage_ctLayout_right {groups len N : ℕ} (h : groups * (2 * len) = N)
    (zInv : Fin groups → R) (a : Fin N → R) (g : Fin groups) {r : ℕ} (hr : r < len) :
    coeffAt (inverseStage (ctLayout groups len h) (fun p => zInv p.1) a)
        (g * (2 * len) + len + r) =
      zInv g * (coeffAt a (g * (2 * len) + r) - coeffAt a (g * (2 * len) + len + r)) := by
  have hl := ctLayout_left_val h g ⟨r, hr⟩
  have hrt := ctLayout_right_val h g ⟨r, hr⟩
  rw [coeffAt_of_val_eq _ _ hrt, coeffAt_of_val_eq _ _ hl, coeffAt_of_val_eq _ _ hrt]
  simp [inverseStage, inverseButterfly]

/-- `X^m − z` divides `X^(2m) − z²`. -/
private theorem X_pow_sub_C_dvd_X_pow_two_mul_sub_C_sq (m : ℕ) (z : R) :
    X ^ m - C z ∣ X ^ (2 * m) - C (z ^ 2) := by
  refine ⟨X ^ m + C z, ?_⟩
  rw [show (X : R[X]) ^ (2 * m) = (X ^ m) ^ 2 by rw [← pow_mul, mul_comm], C_pow]
  ring

/-- One Cooley–Tukey layer splits a residue modulo `X^(2·len) − z²` into residues modulo
`X^len − z` (left half) and `X^len + z` (right half). -/
theorem forwardStage_ctLayout_dvd {groups len N : ℕ} (h : groups * (2 * len) = N)
    (z : Fin groups → R) (a : Fin N → R) (F : R[X]) (g : Fin groups)
    (hdvd : X ^ (2 * len) - C (z g ^ 2) ∣ blockPoly a (g * (2 * len)) (2 * len) - F) :
    (X ^ len - C (z g) ∣
        blockPoly (forwardStage (ctLayout groups len h) (fun p => z p.1) a) (g * (2 * len)) len -
          F) ∧
    (X ^ len - C (-z g) ∣
        blockPoly (forwardStage (ctLayout groups len h) (fun p => z p.1) a)
          (g * (2 * len) + len) len - F) := by
  have hP := blockPoly_add_len a (g * (2 * len)) len len
  rw [← two_mul] at hP
  have hL : blockPoly (forwardStage (ctLayout groups len h) (fun p => z p.1) a)
      (g * (2 * len)) len =
        blockPoly a (g * (2 * len)) len + C (z g) * blockPoly a (g * (2 * len) + len) len := by
    simp only [blockPoly, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [coeffAt_forwardStage_ctLayout_left h z a g (Finset.mem_range.mp hr)]
    simp only [C_add, C_mul]
    ring
  have hR : blockPoly (forwardStage (ctLayout groups len h) (fun p => z p.1) a)
      (g * (2 * len) + len) len =
        blockPoly a (g * (2 * len)) len - C (z g) * blockPoly a (g * (2 * len) + len) len := by
    simp only [blockPoly, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [coeffAt_forwardStage_ctLayout_right h z a g (Finset.mem_range.mp hr)]
    simp only [C_sub, C_mul]
    ring
  rw [hP] at hdvd
  constructor
  · rw [hL, show ∀ U V : R[X], U + C (z g) * V - F =
        (U + X ^ len * V - F) - (X ^ len - C (z g)) * V from fun U V => by ring]
    exact dvd_sub ((X_pow_sub_C_dvd_X_pow_two_mul_sub_C_sq len (z g)).trans hdvd)
      (dvd_mul_right _ _)
  · rw [hR, show ∀ U V : R[X], U - C (z g) * V - F =
        (U + X ^ len * V - F) - (X ^ len - C (-z g)) * V from fun U V => by rw [C_neg]; ring]
    have h6 := X_pow_sub_C_dvd_X_pow_two_mul_sub_C_sq len (-z g)
    rw [neg_sq] at h6
    exact dvd_sub (h6.trans hdvd) (dvd_mul_right _ _)

/-! ## Iterated layers -/

/-- Appending a stage applies it after the earlier stages. -/
theorem forwardStages_append {Coord : Type*} (l : List (ScaledStage R Coord))
    (t : ScaledStage R Coord) (a : Coord → R) :
    forwardStages (l ++ [t]) a = t.forward (forwardStages l a) := by
  induction l generalizing a with
  | nil => rfl
  | cons s l ih => simp only [List.cons_append, forwardStages]; exact ih _

/-- `forwardStages` over `List.ofFn` peels off the last stage. -/
theorem forwardStages_ofFn_succ {Coord : Type*} {k : ℕ}
    (stage : Fin (k + 1) → ScaledStage R Coord) (a : Coord → R) :
    forwardStages (List.ofFn stage) a =
      (stage (Fin.last k)).forward
        (forwardStages (List.ofFn fun s : Fin k => stage s.castSucc) a) := by
  rw [List.ofFn_succ', List.concat_eq_append, forwardStages_append]

/-- `k` stages with scale factor `c` accumulate the factor `c ^ k`. -/
theorem stageScalar_ofFn {Coord : Type*} {k : ℕ} (stage : Fin k → ScaledStage R Coord) {c : R}
    (h : ∀ s, (stage s).scalar = c) : stageScalar (List.ofFn stage) = c ^ k := by
  induction k with
  | zero => exact (pow_zero c).symm
  | succ k ih => rw [List.ofFn_succ, stageScalar, ih _ fun s => h s.succ, h, pow_succ]

/-- After `k` radix-2 layers on blocked layouts, block `g` of size `N / 2^k` is congruent to the
input polynomial modulo `X^(N/2^k) − c k g`. Here the twiddles satisfy `z s g ^ 2 = c s g`,
`c (s+1) (2g) = z s g` and `c (s+1) (2g+1) = −z s g`. -/
theorem forwardStages_ofFn_dvd {N k : ℕ} (len : Fin k → ℕ)
    (hshape : ∀ s : Fin k, 2 ^ s.val * (2 * len s) = N)
    (z : (s : Fin k) → Fin (2 ^ s.val) → R) (c : ℕ → ℕ → R)
    (hsq : ∀ s g, z s g ^ 2 = c s.val g.val)
    (hleft : ∀ s g, c (s.val + 1) (2 * g.val) = z s g)
    (hright : ∀ s g, c (s.val + 1) (2 * g.val + 1) = -z s g)
    (stage : Fin k → ScaledStage R (Fin N))
    (hstage : ∀ s, (stage s).forward =
      forwardStage (ctLayout (2 ^ s.val) (len s) (hshape s)) (fun p => z s p.1))
    (a : Fin N → R) (g : ℕ) (hg : g < 2 ^ k) :
    X ^ (N / 2 ^ k) - C (c k g) ∣
      blockPoly (forwardStages (List.ofFn stage) a) (g * (N / 2 ^ k)) (N / 2 ^ k) -
        blockPoly a 0 N := by
  induction k generalizing g with
  | zero =>
    obtain rfl : g = 0 := by simpa using hg
    simp [forwardStages]
  | succ k ih =>
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hsh : 2 ^ k * (2 * len (Fin.last k)) = N := hshape (Fin.last k)
    have hN1 : N / 2 ^ k = 2 * len (Fin.last k) := by
      rw [← hsh, Nat.mul_div_cancel_left _ hpos]
    have hN2 : N / 2 ^ (k + 1) = len (Fin.last k) := by
      rw [← hsh, pow_succ, ← mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
    have hg' : g / 2 < 2 ^ k := by rw [pow_succ] at hg; omega
    have ih' := ih (fun s => len s.castSucc) (fun s => hshape s.castSucc)
      (fun s => z s.castSucc) (fun s g => hsq s.castSucc g) (fun s g => hleft s.castSucc g)
      (fun s g => hright s.castSucc g) (fun s => stage s.castSucc) (fun s => hstage s.castSucc)
      (g / 2) hg'
    have hsq' : z (Fin.last k) ⟨g / 2, hg'⟩ ^ 2 = c k (g / 2) := hsq _ _
    rw [hN1, ← hsq'] at ih'
    have h7 := forwardStage_ctLayout_dvd (hshape (Fin.last k)) (z (Fin.last k))
      (forwardStages (List.ofFn fun s : Fin k => stage s.castSucc) a) (blockPoly a 0 N)
      ⟨g / 2, hg'⟩ ih'
    rw [forwardStages_ofFn_succ, hstage (Fin.last k), hN2]
    rcases Nat.even_or_odd' g with ⟨g', rfl | rfl⟩
    · have hl : c (k + 1) (2 * g') = z (Fin.last k) ⟨2 * g' / 2, hg'⟩ := by
        have h := hleft (Fin.last k) ⟨2 * g' / 2, hg'⟩
        simp only [Fin.val_last] at h
        rwa [show 2 * (2 * g' / 2) = 2 * g' by omega] at h
      rw [hl, show 2 * g' * len (Fin.last k) = 2 * g' / 2 * (2 * len (Fin.last k)) by
        rw [Nat.mul_div_cancel_left _ (by norm_num)]; ring]
      exact h7.1
    · have hr : c (k + 1) (2 * g' + 1) = -z (Fin.last k) ⟨(2 * g' + 1) / 2, hg'⟩ := by
        have h := hright (Fin.last k) ⟨(2 * g' + 1) / 2, hg'⟩
        simp only [Fin.val_last] at h
        rwa [show 2 * ((2 * g' + 1) / 2) + 1 = 2 * g' + 1 by omega] at h
      rw [hr, show (2 * g' + 1) * len (Fin.last k) =
          (2 * g' + 1) / 2 * (2 * len (Fin.last k)) + len (Fin.last k) by
        rw [show (2 * g' + 1) / 2 = g' by omega]; ring]
      exact h7.2

/-! ## Negacyclic bridges -/

/-- If `γ^m = −1`, then `X^B − γ` divides `X^(B·m) + 1`. -/
theorem X_pow_sub_C_dvd_X_pow_mul_add_one {B m : ℕ} {γ : R} (hγ : γ ^ m = -1) :
    X ^ B - C γ ∣ X ^ (B * m) + 1 := by
  have h := sub_dvd_pow_sub_pow (X ^ B) (C γ) m
  rwa [← pow_mul, ← C_pow, hγ, C_neg, C_1, sub_neg_eq_add] at h

/-- `negacyclicMulPure` agrees with the polynomial product modulo `X^n + 1`. -/
theorem negacyclicModulus_dvd_toPolynomial_negacyclicMulPure (backend : PolyBackend R)
    (kernel : PolyKernel R backend) (f g : backend.Poly) :
    X ^ backend.degree + 1 ∣
      backend.toPolynomial (negacyclicMulPure kernel f g) -
        backend.toPolynomial f * backend.toPolynomial g := by
  have h := negacyclicMulPure_sound backend kernel f g
  simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial, ← map_mul] at h
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  simpa [negacyclicModulus] using h

end LatticeCrypto.NTTCert
