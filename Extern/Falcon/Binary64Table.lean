/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all LatticeCrypto.Falcon.Concrete.GMTable
import all LatticeCrypto.Falcon.Concrete.FPR
import all LatticeCrypto.Falcon.Concrete.FloatLike
import all Extern.Falcon.FPR.Decode
public import Extern.Falcon.Binary64Ops

/-!
# The twiddle table and the integer conversion in binary64

`fpolyFFT` and `fpolyIFFT` read their twiddles from c-fn-dsa's table `GMTable.gmRaw`, and
`fpolySetSmall` converts integers with `FPR.ofInt`. This file proves what the error analysis needs
from both, by kernel evaluation (`decide +kernel`) of checks on the bit patterns, with no
transcendental evaluation:

- `twiddle_chain`, `gmPair_twiddle`: the table entries used at the first eight stages are normal
  binary64 values of magnitude in `[2^(-9), 1]`, and entry `2^(s+1) + c` is within
  `(s + 1) · 2^(-51)` of the exact twiddle `Falcon.FFTStages.twiddle s c`, which is
  `exp(i · rootAngle s c / 2)`. The check is a square-root chain: entry `2m` squares to entry `m`
  within `2^(-51)` and lies in the open first quadrant, entry `2m + 1` is `i` times entry `2m`
  exactly, and entry `2` squares to `i`. A first-quadrant square root of a value within `d` of a
  unit's square is within `d` of the unit (`norm_sub_le_norm_sq_sub`), so the distance grows by
  at most `2^(-51)` per level;
- `ofInt32_exact`: `FPR.ofInt` is exact on the integers of magnitude at most `127`;
- `toReal_ifftScale`: the final scale of `fpolyIFFT` is exactly `2^(1 - logn)` for `2 ≤ logn ≤ 9`.
-/

public section

namespace Falcon.Concrete.Binary64

open Falcon.Concrete.FPRBridge Falcon.Concrete.FPR Falcon.FFTStages Complex

/-! ## Values of table words -/

/-- The value of a table word in units of `2^(-62)`, for biased exponents at least `1013`. -/
def gmVal (w : UInt64) : ℤ :=
  (if (FPR.decode w).sign then -1 else 1) *
    (((2 ^ 52 + (FPR.decode w).mantissa) * 2 ^ ((FPR.decode w).exponent - 1013) : ℕ) : ℤ)

/-- The biased exponent of `w` is in `[1014, 1022]`: a normal value in `[2^(-9), 1)`. -/
def gmInRange (w : UInt64) : Bool :=
  1014 ≤ (FPR.decode w).exponent && (FPR.decode w).exponent ≤ 1022

private theorem toReal_of_gmInRange {w : UInt64} (h : gmInRange w = true) :
    toReal w = gmVal w / 2 ^ 62 ∧ FPR.IsNormal w ∧ |toReal w| ≤ 1 ∧
      (2 : ℝ) ^ (-(9 : ℤ)) ≤ |toReal w| := by
  simp only [gmInRange, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  set b := FPR.decode w with hb
  have hne : b.exponent ≠ 2047 := by omega
  have hm : b.mantissa < 2 ^ 52 := FPR.decode_mantissa_lt w
  have hval : toReal w = (if b.sign then -1 else 1) * ((2 ^ 52 + b.mantissa : ℕ) : ℝ) *
      (2 : ℝ) ^ ((b.exponent : ℤ) - 1075) := by
    change b.toReal = _
    rw [FPR.Bits.toReal_eq_of_exponent_ne_2047 b hne]
    have hsig : b.significand = 2 ^ 52 + b.mantissa := by
      unfold FPR.Bits.significand
      split_ifs with h0
      · omega
      · ring
    have hwe : b.workExp = b.exponent := by
      unfold FPR.Bits.workExp; exact Nat.max_eq_left (by omega)
    rw [hsig, hwe]; congr 2; ring
  have habs :
      |toReal w| = ((2 ^ 52 + b.mantissa : ℕ) : ℝ) * (2 : ℝ) ^ ((b.exponent : ℤ) - 1075) := by
    rw [hval, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ ((b.exponent : ℤ) - 1075)),
      Nat.abs_cast]
    split_ifs <;> simp
  have hn0 : b.exponent ≠ 0 := by omega
  refine ⟨?_, ⟨hn0, hne⟩, ?_, ?_⟩
  · rw [hval, gmVal, ← hb]
    have : ((2 : ℝ) ^ ((b.exponent : ℤ) - 1075)) =
        ((2 ^ (b.exponent - 1013) : ℕ) : ℝ) / 2 ^ 62 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Nat.cast_sub (by omega),
        div_eq_mul_inv, ← zpow_natCast (n := 62), ← zpow_neg, ← zpow_add₀ (by norm_num)]
      congr 1; push_cast; ring
    rw [this]; split_ifs <;> push_cast <;> ring
  · rw [habs]
    have hsig : ((2 ^ 52 + b.mantissa : ℕ) : ℝ) ≤ 2 ^ 53 := by
      exact_mod_cast (by omega : 2 ^ 52 + b.mantissa ≤ 2 ^ 53)
    have hexp : (2 : ℝ) ^ ((b.exponent : ℤ) - 1075) ≤ 2 ^ (-(53 : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    calc ((2 ^ 52 + b.mantissa : ℕ) : ℝ) * (2 : ℝ) ^ ((b.exponent : ℤ) - 1075) ≤
          2 ^ 53 * 2 ^ (-(53 : ℤ)) := mul_le_mul hsig hexp (by positivity) (by positivity)
      _ = 1 := by norm_num
  · rw [habs]
    have hsig : (2 : ℝ) ^ 52 ≤ ((2 ^ 52 + b.mantissa : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ^ 52 ≤ 2 ^ 52 + b.mantissa)
    have hexp : (2 : ℝ) ^ (-(61 : ℤ)) ≤ 2 ^ ((b.exponent : ℤ) - 1075) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    calc (2 : ℝ) ^ (-(9 : ℤ)) = 2 ^ 52 * 2 ^ (-(61 : ℤ)) := by norm_num
      _ ≤ _ := mul_le_mul hsig hexp (by positivity) (by positivity)

/-! ## The square-root chain -/

/-- Words `2k` and `2k + 1` of a list, as pairs. -/
def pairsOf : List UInt64 → List (UInt64 × UInt64)
  | a :: b :: t => (a, b) :: pairsOf t
  | _ => []

/-- The check for parent pair `p` and children `c` (at `2m`) and `d` (at `2m + 1`); at the
first parent the parent value is taken to be `i`. -/
def family (p c d : UInt64 × UInt64) (first : Bool) : Bool :=
  let pr : ℤ := if first then 0 else gmVal p.1
  let pi : ℤ := if first then 2 ^ 62 else gmVal p.2
  (first || (gmInRange p.1 && gmInRange p.2)) &&
  gmInRange c.1 && gmInRange c.2 && !(FPR.decode c.1).sign && !(FPR.decode c.2).sign &&
    d.1 == (c.2 ^^^ 0x8000000000000000) && d.2 == c.1 &&
    decide ((gmVal c.1 * gmVal c.1 - gmVal c.2 * gmVal c.2 - pr * 2 ^ 62).natAbs ≤ 2 ^ 72) &&
    decide ((2 * gmVal c.1 * gmVal c.2 - pi * 2 ^ 62).natAbs ≤ 2 ^ 72)

/-- Walk the parents and their children in step. -/
def walk : ℕ → Bool → List (UInt64 × UInt64) → List (UInt64 × UInt64) → Bool
  | 0, _, _, _ => true
  | n + 1, first, p :: ps, c :: d :: cs => family p c d first && walk n false ps cs
  | _ + 1, _, _, _ => false

/-- The kernel check of the square-root chain over the 255 parents of the table. -/
theorem walk_gmRaw : walk 255 true ((pairsOf GMTable.gmRaw.toList).drop 1)
    ((pairsOf GMTable.gmRaw.toList).drop 2) = true := by
  decide +kernel

private theorem walk_spec : ∀ (n : ℕ) (first : Bool) (P : List (UInt64 × UInt64)) (a : ℕ),
    walk n first (P.drop a) (P.drop (2 * a)) = true → ∀ j < n,
      ∃ p c d, P[a + j]? = some p ∧ P[2 * (a + j)]? = some c ∧ P[2 * (a + j) + 1]? = some d ∧
        family p c d (first && j == 0) = true := by
  intro n
  induction n with
  | zero => intro _ _ _ _ j hj; omega
  | succ n ih =>
    intro first P a h j hj
    match hpa : P.drop a, hpc : P.drop (2 * a) with
    | p :: ps, c :: d :: cs =>
      rw [hpa, hpc] at h
      simp only [walk, Bool.and_eq_true] at h
      obtain ⟨hf, hw⟩ := h
      have h0 : P[a]? = some p := by
        have := congrArg (fun l => l[0]?) hpa; simpa [List.getElem?_drop] using this
      have hc0 : P[2 * a]? = some c := by
        have := congrArg (fun l => l[0]?) hpc; simpa [List.getElem?_drop] using this
      have hd0 : P[2 * a + 1]? = some d := by
        have := congrArg (fun l => l[1]?) hpc; simpa [List.getElem?_drop] using this
      have hps : P.drop (a + 1) = ps := by
        have := congrArg List.tail hpa; simpa [List.tail_drop] using this
      have hcs : P.drop (2 * (a + 1)) = cs := by
        have := congrArg (fun l => l.tail.tail) hpc
        simpa [List.tail_drop, show 2 * (a + 1) = 2 * a + 1 + 1 by ring] using this
      rcases j with _ | j
      · exact ⟨p, c, d, by simpa using h0, by simpa using hc0, by simpa using hd0,
          by simpa using hf⟩
      · rw [← hps, ← hcs] at hw
        obtain ⟨p', c', d', h1, h2, h3, h4⟩ := ih false P (a + 1) hw j (by omega)
        refine ⟨p', c', d', ?_, ?_, ?_, by simpa using h4⟩
        · rw [show a + (j + 1) = a + 1 + j by ring]; exact h1
        · rw [show a + (j + 1) = a + 1 + j by ring]; exact h2
        · rw [show a + (j + 1) = a + 1 + j by ring]; exact h3
    | [], _ => rw [hpa] at h; simp [walk] at h
    | _ :: _, [] => rw [hpa, hpc] at h; simp [walk] at h
    | _ :: _, [_] => rw [hpa, hpc] at h; simp [walk] at h

private theorem pairsOf_getElem? : ∀ (L : List UInt64) (j : ℕ) (x : UInt64 × UInt64),
    (pairsOf L)[j]? = some x → L[2 * j]? = some x.1 ∧ L[2 * j + 1]? = some x.2
  | a :: b :: t, 0, x, h => by
    simp only [pairsOf, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp
  | a :: b :: t, j + 1, x, h => by
    simp only [pairsOf, List.getElem?_cons_succ] at h
    obtain ⟨h1, h2⟩ := pairsOf_getElem? t j x h
    refine ⟨?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]; simpa using h1
    · rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring]; simpa using h2
  | [], _, _, h => by simp [pairsOf] at h
  | [_], _, _, h => by simp [pairsOf] at h

private theorem ofRawFPR_fpr (w : UInt64) : (FloatLike.ofRawFPR w : FPR) = w := rfl

/-- Table pair `m` in `FPR`: the words at `2m` and `2m + 1`. -/
theorem gmPair_fpr (m : ℕ) : (FFTOps.gmPair m : FPR × FPR) =
    (GMTable.gmRaw.getD (2 * m) 0, GMTable.gmRaw.getD (2 * m + 1) 0) := by
  simp only [FFTOps.gmPair, ofRawFPR_fpr]

private theorem gmPair_of_pairs {m : ℕ} {x : UInt64 × UInt64}
    (h : (pairsOf GMTable.gmRaw.toList)[m]? = some x) : (FFTOps.gmPair m : FPR × FPR) = x := by
  obtain ⟨h1, h2⟩ := pairsOf_getElem? _ m x h
  rw [gmPair_fpr]
  simp only [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h1, h2, Option.getD_some]

/-- The facts the walk gives about parent `m ∈ [1, 256)`. -/
theorem family_of_walk {m : ℕ} (h1 : 1 ≤ m) (h2 : m < 256) :
    ∃ p c d, (pairsOf GMTable.gmRaw.toList)[m]? = some p ∧
      (pairsOf GMTable.gmRaw.toList)[2 * m]? = some c ∧
      (pairsOf GMTable.gmRaw.toList)[2 * m + 1]? = some d ∧
      family p c d (m == 1) = true := by
  obtain ⟨p, c, d, hp, hc, hd, hf⟩ := walk_spec 255 true _ 1 walk_gmRaw (m - 1) (by omega)
  refine ⟨p, c, d, ?_, ?_, ?_, ?_⟩
  · rwa [show 1 + (m - 1) = m by omega] at hp
  · rwa [show 2 * (1 + (m - 1)) = 2 * m by omega] at hc
  · rwa [show 2 * (1 + (m - 1)) + 1 = 2 * m + 1 by omega] at hd
  · have : (m - 1 == 0) = (m == 1) := by
      by_cases hm : m = 1
      · subst hm; rfl
      · rw [beq_false_of_ne hm, beq_false_of_ne (by omega : m - 1 ≠ 0)]
    simpa [this] using hf

private theorem toReal_neg_word (w : UInt64) : toReal (w ^^^ 0x8000000000000000) = -toReal w := by
  have : w ^^^ 0x8000000000000000 = FPR.neg w := rfl
  rw [this, toReal_neg]

/-- A first-quadrant square root of a value near a unit square is near the unit root. -/
theorem norm_sub_le_norm_sq_sub {w z : ℂ} (hz : ‖z‖ = 1) (hw1 : 0 ≤ w.re) (hw2 : 0 ≤ w.im)
    (hz1 : 0 ≤ z.re) (hz2 : 0 ≤ z.im) : ‖w - z‖ ≤ ‖w ^ 2 - z ^ 2‖ := by
  have hsum : 1 ≤ ‖w + z‖ := by
    have hz' : z.re ^ 2 + z.im ^ 2 = 1 := by
      have := Complex.normSq_eq_norm_sq z
      rw [hz, Complex.normSq_apply] at this; nlinarith
    have : 1 ≤ ‖w + z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im]; nlinarith
    nlinarith [norm_nonneg (w + z)]
  rw [show w ^ 2 - z ^ 2 = (w - z) * (w + z) by ring, norm_mul]
  nlinarith [norm_nonneg (w - z)]

private theorem rootAngle_mem : ∀ (s c : ℕ), 0 < rootAngle s c ∧ rootAngle s c < 2 * Real.pi
  | 0, c => by rw [rootAngle_zero]; constructor <;> linarith [Real.pi_pos]
  | s + 1, c => by
    obtain ⟨h1, h2⟩ := rootAngle_mem s (c / 2)
    simp only [rootAngle]
    have hb : ((c % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : c % 2 ≤ 1)
    have hb0 : (0 : ℝ) ≤ ((c % 2 : ℕ) : ℝ) := by positivity
    constructor <;> nlinarith [Real.pi_pos]

private theorem twiddle_sq (s c : ℕ) : twiddle (s + 1) (2 * c) ^ 2 = twiddle s c := by
  rw [twiddle, twiddle, rootAngle_two_mul, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

private theorem twiddle_odd (s c : ℕ) :
    twiddle (s + 1) (2 * c + 1) = I * twiddle (s + 1) (2 * c) := by
  rw [twiddle, twiddle, rootAngle_two_mul_add_one, rootAngle_two_mul]
  rw [show (((rootAngle s c / 2 + Real.pi) / 2 : ℝ) : ℂ) * I =
      ((rootAngle s c / 2 / 2 : ℝ) : ℂ) * I + ((Real.pi / 2 : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_add, Complex.exp_mul_I (((Real.pi / 2 : ℝ) : ℂ)), ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp; ring

private theorem twiddle_even_quadrant (s c : ℕ) :
    0 ≤ (twiddle (s + 1) (2 * c)).re ∧ 0 ≤ (twiddle (s + 1) (2 * c)).im := by
  obtain ⟨h1, h2⟩ := rootAngle_mem s c
  rw [twiddle, rootAngle_two_mul, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  constructor
  · exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩).le
  · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le

private theorem twiddle_zero : twiddle 0 0 ^ 2 = I := by
  rw [twiddle, ← Complex.exp_nat_mul, rootAngle_zero]
  rw [show ((2 : ℕ) : ℂ) * ((((Real.pi / 2) / 2 : ℝ) : ℂ) * I) = ((Real.pi / 2 : ℝ) : ℂ) * I by
    push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

private theorem twiddle_zero_quadrant : 0 ≤ (twiddle 0 0).re ∧ 0 ≤ (twiddle 0 0).im := by
  rw [twiddle, rootAngle_zero, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  constructor
  · exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).le
  · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])).le

private theorem abs_cast_le {X : ℤ} {k : ℕ} (h : X.natAbs ≤ 2 ^ k) : |(X : ℝ)| ≤ 2 ^ k := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]; exact_mod_cast h

/-- What a successful family check says about the children of parent `p` in `ℂ`. -/
theorem family_spec {p c d : UInt64 × UInt64} {first : Bool} (h : family p c d first = true) :
    GoodP (2 ^ (-(9 : ℤ))) 1 c ∧ GoodP (2 ^ (-(9 : ℤ))) 1 d ∧
      0 < toReal c.1 ∧ 0 < toReal c.2 ∧ cplx d = I * cplx c ∧
      ‖cplx c ^ 2 - (if first then I else cplx p)‖ ≤ 2 * 2 ^ (-(52 : ℤ)) := by
  simp only [family, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hpar, hc1⟩, hc2⟩, hs1⟩, hs2⟩, hd1⟩, hd2⟩, hre⟩, him⟩ := h
  obtain ⟨vc1, nc1, ub1, lb1⟩ := toReal_of_gmInRange hc1
  obtain ⟨vc2, nc2, ub2, lb2⟩ := toReal_of_gmInRange hc2
  have gpos : ∀ w : UInt64, (FPR.decode w).sign = false → 0 < (gmVal w : ℝ) / 2 ^ 62 := by
    intro w hw
    have : (0 : ℤ) < gmVal w := by
      unfold gmVal; rw [hw]; simp only [Bool.false_eq_true, ite_false, one_mul]
      exact_mod_cast Nat.mul_pos (by positivity) (by positivity)
    have : (0 : ℝ) < gmVal w := by exact_mod_cast this
    positivity
  have pos1 : 0 < toReal c.1 := by rw [vc1]; exact gpos _ hs1
  have pos2 : 0 < toReal c.2 := by rw [vc2]; exact gpos _ hs2
  have hgc1 : Good (2 ^ (-(9 : ℤ))) 1 c.1 := ⟨Or.inl nc1, Or.inr lb1, ub1⟩
  have hgc2 : Good (2 ^ (-(9 : ℤ))) 1 c.2 := ⟨Or.inl nc2, Or.inr lb2, ub2⟩
  have hdc : cplx d = I * cplx c := by
    apply Complex.ext <;> simp [cplx, hd1, hd2, toReal_neg_word]
  refine ⟨⟨hgc1, hgc2⟩, ⟨?_, ?_⟩, pos1, pos2, hdc, ?_⟩
  · rw [hd1]
    refine ⟨Or.inl (FPR.isNormal_neg nc2), ?_, ?_⟩ <;>
      rw [show c.2 ^^^ 0x8000000000000000 = FPR.neg c.2 from rfl, toReal_neg, abs_neg]
    · exact Or.inr lb2
    · exact ub2
  · rw [hd2]; exact hgc1
  · have key : ∀ pr pi : ℤ,
        (gmVal c.1 * gmVal c.1 - gmVal c.2 * gmVal c.2 - pr * 2 ^ 62).natAbs ≤ 2 ^ 72 →
        (2 * gmVal c.1 * gmVal c.2 - pi * 2 ^ 62).natAbs ≤ 2 ^ 72 → ∀ q : ℂ,
        q.re = (pr : ℝ) / 2 ^ 62 → q.im = (pi : ℝ) / 2 ^ 62 →
        ‖cplx c ^ 2 - q‖ ≤ 2 * 2 ^ (-(52 : ℤ)) := by
      intro pr pi hre him q hqr hqi
      apply norm_le_of_parts
      · simp only [Complex.sub_re, sq, Complex.mul_re, cplx_re, cplx_im, hqr, vc1, vc2]
        have e : (gmVal c.1 : ℝ) / 2 ^ 62 * (gmVal c.1 / 2 ^ 62) -
            gmVal c.2 / 2 ^ 62 * (gmVal c.2 / 2 ^ 62) - pr / 2 ^ 62 =
            ((gmVal c.1 * gmVal c.1 - gmVal c.2 * gmVal c.2 - pr * 2 ^ 62 : ℤ) : ℝ) / 2 ^ 124 := by
          push_cast; ring
        rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 124)]
        calc _ ≤ (2 : ℝ) ^ 72 / 2 ^ 124 := by gcongr; exact abs_cast_le hre
          _ = 2 ^ (-(52 : ℤ)) := by norm_num
      · simp only [Complex.sub_im, sq, Complex.mul_im, cplx_re, cplx_im, hqi, vc1, vc2]
        have e : (gmVal c.1 : ℝ) / 2 ^ 62 * (gmVal c.2 / 2 ^ 62) +
            gmVal c.2 / 2 ^ 62 * (gmVal c.1 / 2 ^ 62) - pi / 2 ^ 62 =
            ((2 * gmVal c.1 * gmVal c.2 - pi * 2 ^ 62 : ℤ) : ℝ) / 2 ^ 124 := by
          push_cast; ring
        rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 124)]
        calc _ ≤ (2 : ℝ) ^ 72 / 2 ^ 124 := by gcongr; exact abs_cast_le him
          _ = 2 ^ (-(52 : ℤ)) := by norm_num
    cases first
    · simp only [Bool.false_eq_true, ite_false, false_or] at hre him hpar ⊢
      exact key _ _ hre him (cplx p) (toReal_of_gmInRange hpar.1).1
        (toReal_of_gmInRange hpar.2).1
    · simp only [ite_true] at hre him ⊢
      exact key _ _ hre him I (by simp) (by norm_num)

/-! ## The table against the exact twiddles -/

/-- `2^(-51)`, the per-level distance of the square-root chain. -/
theorem twiddle_chain : ∀ s ≤ 7, ∀ c < 2 ^ s,
    GoodP (2 ^ (-(9 : ℤ))) 1 (FFTOps.gmPair (2 ^ (s + 1) + c) : FPR × FPR) ∧
      ‖cplx (FFTOps.gmPair (2 ^ (s + 1) + c)) - twiddle s c‖ ≤ (s + 1) * (2 * 2 ^ (-(52 : ℤ))) := by
  intro s
  induction s with
  | zero =>
    intro _ c hc
    obtain rfl : c = 0 := by simpa using hc
    obtain ⟨p, cc, d, -, hc', -, hf⟩ := family_of_walk (m := 1) le_rfl (by norm_num)
    obtain ⟨hg, -, pos1, pos2, -, hsq⟩ := family_spec hf
    have hm : (FFTOps.gmPair (2 ^ (0 + 1) + 0) : FPR × FPR) = cc := gmPair_of_pairs hc'
    rw [hm]
    refine ⟨hg, ?_⟩
    have := norm_sub_le_norm_sq_sub (w := cplx cc) (z := twiddle 0 0) (norm_twiddle 0 0)
      (by simpa using pos1.le) (by simpa using pos2.le) twiddle_zero_quadrant.1
      twiddle_zero_quadrant.2
    rw [twiddle_zero] at this
    simp only [beq_self_eq_true, ↓reduceIte] at hsq
    push_cast
    linarith
  | succ s ih =>
    intro hs c' hc'
    set c := c' / 2
    set b := c' % 2
    have hcb : c' = 2 * c + b := by have := Nat.mod_add_div c' 2; omega
    have hc : c < 2 ^ s := by
      have : c' < 2 * 2 ^ s := by rw [← pow_succ']; exact hc'
      omega
    obtain ⟨hgp, hp⟩ := ih (by omega) c hc
    set m := 2 ^ (s + 1) + c with hmdef
    have hm1 : 2 ≤ m := by
      have : 2 ≤ 2 ^ (s + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hm2 : m < 256 := by
      have : 2 ^ (s + 1) + 2 ^ s ≤ 2 ^ 7 + 2 ^ 6 := by
        gcongr
        omega
      omega
    obtain ⟨p, cc, d, hpm, hcc, hdd, hf⟩ := family_of_walk (m := m) (by omega) hm2
    have hne : (m == 1) = false := beq_false_of_ne (by omega)
    rw [hne] at hf
    obtain ⟨hgc, hgd, pos1, pos2, hdc, hsq⟩ := family_spec hf
    simp only [Bool.false_eq_true, ite_false] at hsq
    have hpp : (FFTOps.gmPair m : FPR × FPR) = p := gmPair_of_pairs hpm
    rw [hpp] at hp
    have heven : ‖cplx cc - twiddle (s + 1) (2 * c)‖ ≤ (s + 2) * (2 * 2 ^ (-(52 : ℤ))) := by
      have h1 := norm_sub_le_norm_sq_sub (w := cplx cc) (z := twiddle (s + 1) (2 * c))
        (norm_twiddle _ _) (by simpa using pos1.le) (by simpa using pos2.le)
        (twiddle_even_quadrant s c).1 (twiddle_even_quadrant s c).2
      rw [twiddle_sq] at h1
      have h2 : ‖cplx cc ^ 2 - twiddle s c‖ ≤ ‖cplx cc ^ 2 - cplx p‖ + ‖cplx p - twiddle s c‖ := by
        calc _ = ‖(cplx cc ^ 2 - cplx p) + (cplx p - twiddle s c)‖ := by rw [sub_add_sub_cancel]
          _ ≤ _ := norm_add_le _ _
      exact h1.trans (h2.trans (add_le_add hsq hp)) |>.trans (le_of_eq (by ring))
    have hidx : 2 ^ (s + 1 + 1) + c' = 2 * m + b := by rw [hcb, hmdef, pow_succ]; ring
    rw [hidx]
    rcases (by omega : b = 0 ∨ b = 1) with h0 | h0
    · rw [h0, add_zero, gmPair_of_pairs hcc]
      refine ⟨hgc, ?_⟩
      rw [hcb, h0, add_zero]
      exact heven.trans (le_of_eq (by push_cast; ring))
    · rw [h0, gmPair_of_pairs hdd]
      refine ⟨hgd, ?_⟩
      rw [hcb, h0, twiddle_odd, hdc, ← mul_sub, norm_mul, Complex.norm_I, one_mul]
      exact heven.trans (le_of_eq (by push_cast; ring))

/-- The table twiddle of stage `s ≤ 7`, block `c`, is a `Good` pair within `2^(-48)` of the exact
twiddle `exp(i · rootAngle s c / 2)`. -/
theorem gmPair_twiddle {s c : ℕ} (hs : s ≤ 7) (hc : c < 2 ^ s) :
    GoodP (2 ^ (-(9 : ℤ))) 1 (FFTOps.gmPair (2 ^ (s + 1) + c) : FPR × FPR) ∧
      ‖cplx (FFTOps.gmPair (2 ^ (s + 1) + c)) - twiddle s c‖ ≤ 2 ^ (-(48 : ℤ)) := by
  obtain ⟨hg, he⟩ := twiddle_chain s hs c hc
  refine ⟨hg, he.trans ?_⟩
  have : (s : ℝ) + 1 ≤ 8 := by exact_mod_cast (by omega : s + 1 ≤ 8)
  calc ((s : ℝ) + 1) * (2 * 2 ^ (-(52 : ℤ))) ≤ 8 * (2 * 2 ^ (-(52 : ℤ))) := by gcongr
    _ = 2 ^ (-(48 : ℤ)) := by norm_num

/-! ## Integer conversion and the final scale -/

/-- The bit-level check that `FPR.ofInt v` is exactly `v`. -/
def ofIntOK (v : ℤ) : Bool :=
  let b := FPR.decode (FPR.ofInt (Int32.ofInt v).toInt64)
  if v = 0 then b.exponent == 0 && b.mantissa == 0
  else b.exponent != 0 && decide (b.exponent ≤ 1075) &&
    (2 ^ 52 + b.mantissa == v.natAbs * 2 ^ (1075 - b.exponent)) && (b.sign == decide (v < 0))

private theorem ofIntOK_all : (List.range 255).all (fun i => ofIntOK ((i : ℤ) - 127)) = true := by
  decide +kernel

/-- `FPR.ofInt` is exact on `[-127, 127]`, with a normal or zero result. -/
theorem ofInt32_exact {v : ℤ} (hv : |v| ≤ 127) :
    toReal (FloatLike.ofInt32 (Int32.ofInt v) : FPR) = v ∧
      FPR.IsNormalOrZero (FloatLike.ofInt32 (Int32.ofInt v) : FPR) := by
  have hok : ofIntOK v = true := by
    have h := List.all_eq_true.mp ofIntOK_all (v + 127).toNat
      (List.mem_range.mpr (by rw [abs_le] at hv; omega))
    rwa [show (((v + 127).toNat : ℕ) : ℤ) - 127 = v by rw [abs_le] at hv; omega] at h
  have hdef : (FloatLike.ofInt32 (Int32.ofInt v) : FPR) = FPR.ofInt (Int32.ofInt v).toInt64 := rfl
  rw [hdef]
  set b := FPR.decode (FPR.ofInt (Int32.ofInt v).toInt64) with hb
  have hm : b.mantissa < 2 ^ 52 := FPR.decode_mantissa_lt _
  unfold ofIntOK at hok
  rw [← hb] at hok
  by_cases h0 : v = 0
  · simp only [h0, ite_true, Bool.and_eq_true, beq_iff_eq] at hok
    have hz : FPR.IsZero (FPR.ofInt (Int32.ofInt v).toInt64) := ⟨hok.1, hok.2⟩
    refine ⟨?_, Or.inr hz⟩
    change b.toReal = _
    rw [h0]; unfold FPR.Bits.toReal; simp [hok.1, hok.2]
  · simp only [h0, ite_false, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
      beq_iff_eq] at hok
    obtain ⟨⟨⟨he0, hle⟩, hsig⟩, hsgn⟩ := hok
    have hne : b.exponent ≠ 2047 := by omega
    refine ⟨?_, Or.inl ⟨he0, hne⟩⟩
    change b.toReal = _
    rw [FPR.Bits.toReal_eq_of_exponent_ne_2047 b hne]
    have hs : b.significand = v.natAbs * 2 ^ (1075 - b.exponent) := by
      unfold FPR.Bits.significand; simp only [he0, ite_false]; rw [← hsig, Nat.add_comm]
    have hw : b.workExp = b.exponent := by
      unfold FPR.Bits.workExp; exact Nat.max_eq_left (by omega)
    rw [hs, hw, hsgn]
    have hpow : (2 : ℝ) ^ (1075 - b.exponent) * (2 : ℝ) ^ ((b.exponent : ℤ) - 1023 - 52) = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      have : (((1075 - b.exponent : ℕ) : ℤ) + ((b.exponent : ℤ) - 1023 - 52)) = 0 := by omega
      rw [this, zpow_zero]
    push_cast
    simp only [mul_assoc, hpow, mul_one]
    by_cases hneg : v < 0
    · simp only [hneg, decide_true, ite_true]
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]; ring
    · simp only [hneg, decide_false, Bool.false_eq_true, ite_false]
      rw [Nat.cast_natAbs, Int.cast_abs,
        abs_of_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ v by omega))]
      ring

/-- The bit-level check of the final scale of `fpolyIFFT`. -/
def scaleOK (logn : ℕ) : Bool :=
  let b := FPR.decode (FPR.scaled 4503599627370496 (0 - 51 - logn.toUInt32.toInt32))
  b.sign == false && b.exponent == 1024 - logn && b.mantissa == 0

private theorem scaleOK_all : (List.range' 2 8).all scaleOK = true := by decide +kernel

/-- **The final scale of `fpolyIFFT` is exactly `2^(1 - logn)`** for `2 ≤ logn ≤ 9`. -/
theorem toReal_ifftScale {logn : ℕ} (h1 : 2 ≤ logn) (h2 : logn ≤ 9) :
    toReal (FloatLike.scaled 4503599627370496 (0 - 51 - logn.toUInt32.toInt32) : FPR) =
        2 ^ (1 - (logn : ℤ)) ∧
      FPR.IsNormalOrZero
        (FloatLike.scaled 4503599627370496 (0 - 51 - logn.toUInt32.toInt32) : FPR) := by
  have hok : scaleOK logn = true :=
    List.all_eq_true.mp scaleOK_all logn (List.mem_range'_1.mpr ⟨h1, by omega⟩)
  have hdef : (FloatLike.scaled 4503599627370496 (0 - 51 - logn.toUInt32.toInt32) : FPR) =
      FPR.scaled 4503599627370496 (0 - 51 - logn.toUInt32.toInt32) := rfl
  rw [hdef]
  set b := FPR.decode (FPR.scaled 4503599627370496 (0 - 51 - logn.toUInt32.toInt32)) with hb
  unfold scaleOK at hok
  rw [← hb] at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hs, he⟩, hm⟩ := hok
  have hn0 : b.exponent ≠ 0 := by rw [he]; omega
  have hn2 : b.exponent ≠ 2047 := by rw [he]; omega
  refine ⟨?_, Or.inl ⟨hn0, hn2⟩⟩
  change b.toReal = _
  have hval : b.toReal = (2 : ℝ) ^ (((1024 - logn : ℕ) : ℤ) - 1023) := by
    unfold FPR.Bits.toReal
    simp only [he, show 1024 - logn ≠ 0 by omega, show 1024 - logn ≠ 2047 by omega, ite_false,
      hs, hm, Bool.false_eq_true, CharP.cast_eq_zero, zero_div, add_zero, one_mul]
  rw [hval, show ((1024 - logn : ℕ) : ℤ) - 1023 = 1 - (logn : ℤ) by omega]

end Falcon.Concrete.Binary64

end
