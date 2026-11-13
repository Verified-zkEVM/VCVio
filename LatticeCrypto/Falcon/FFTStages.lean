/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all LatticeCrypto.Falcon.PackedFFT
public import LatticeCrypto.Falcon.PackedFFT

/-!
# The packed FFT as in-place butterfly stages

The reference FFT (`fpoly_FFT` of c-fn-dsa) does not run the merge recursion of
`RealFFTPoly.ofCoeffs`: it reads the `2 · 2^k` real coefficients `f` of a polynomial as the
`2^k` complex numbers `fᵣ + i · f_{r + 2^k}` and runs `k` in-place butterfly stages over them.
Stage `s` splits each block of `2^(k - s)` slots in two halves `x, y` and replaces them by
`x + σ · y` and `x - σ · y`, where `σ = exp(i · rootAngle s c / 2)` for block `c`. The inverse
transform (`fpoly_iFFT`) runs the stages in the opposite order with
`(a, b) ↦ (a + b, (a - b) · σ̄)`.

This file describes these stages over `ℂ` and proves what the floating-point analysis needs from
them:

- `bfStage`: one stage, for any pair map, on functions `ℕ → α`; `bfStage_bfStage` composes two
  stages with the same blocks;
- `fwdStages_apply` and `coord_ofCoeffs_eq_fwdStages`: the exact stages compute the packed FFT of
  the specification, slot `j` being the value at `exp(i · rootAngle k j)`;
- `invStages_fwdStages`: the exact inverse stages undo the forward stages up to the factor `2^k`;
- `stages_error`: the error recursion. A computed transform whose stage `s` is within
  `η · (2 + η)^s · A` of the exact stage applied to its own input, in the largest modulus of any
  slot, ends within `((2 + η)^k - 2^k) · A` of the exact transform of inputs bounded by `A`. The
  statement is generic in what the computed values are; an invariant `P s` of the computation is
  carried through the stages, so a floating-point instance can thread its domain conditions.

`LatticeCrypto.NTTCert.forwardStages_ofFn_dvd` proves the same residue statement for blocked
stages over a commutative ring on `Fin N`. The stages here are on functions `ℕ → α` for any `α`
because the floating-point stages of `Extern.Falcon.FFTLoops` are the same `bfStage`
over pairs of `FloatLike` values, which form no ring, and the error recursion compares the
computed and the exact stage slot by slot through that shared definition. The residue
statement over `ℂ` (`fwdStages_eval`) is proved on `bfStage` directly rather than through a
`ScaledStage` bridge to `NTTCert`.
-/

public section

open Complex

namespace Falcon

namespace FFTStages

/-! ## Butterfly stages -/

variable {α : Type*}

/-- One in-place butterfly stage with half-block `H`: slots `q` and `q + H` of the block
`q / (2 * H)` are replaced by the two components of `g c` applied to them. -/
@[expose] def bfStage (H : ℕ) (g : ℕ → α × α → α × α) (x : ℕ → α) : ℕ → α := fun q =>
  if q % (2 * H) < H then (g (q / (2 * H)) (x q, x (q + H))).1
  else (g (q / (2 * H)) (x (q - H), x q)).2

private theorem mod_div_add_half {q H : ℕ} (hH : 0 < H) (hr : q % (2 * H) < H) :
    (q + H) % (2 * H) = q % (2 * H) + H ∧ (q + H) / (2 * H) = q / (2 * H) := by
  have h2 : 0 < 2 * H := by omega
  have hq : q + H = (q % (2 * H) + H) + 2 * H * (q / (2 * H)) := by
    have := Nat.mod_add_div q (2 * H); omega
  rw [hq, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ h2,
    Nat.mod_eq_of_lt (by omega : q % (2 * H) + H < 2 * H),
    Nat.div_eq_of_lt (by omega : q % (2 * H) + H < 2 * H)]
  simp

private theorem mod_div_sub_half {q H : ℕ} (hH : 0 < H) (hr : ¬q % (2 * H) < H) :
    H ≤ q ∧ (q - H) % (2 * H) = q % (2 * H) - H ∧ (q - H) / (2 * H) = q / (2 * H) := by
  have h2 : 0 < 2 * H := by omega
  have hlt := Nat.mod_lt q h2
  have hdm := Nat.mod_add_div q (2 * H)
  have hq : q - H = (q % (2 * H) - H) + 2 * H * (q / (2 * H)) := by omega
  refine ⟨by omega, ?_⟩
  rw [hq, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ h2,
    Nat.mod_eq_of_lt (by omega : q % (2 * H) - H < 2 * H),
    Nat.div_eq_of_lt (by omega : q % (2 * H) - H < 2 * H)]
  simp

/-- Two stages with the same blocks compose pairwise. -/
theorem bfStage_bfStage (H : ℕ) (hH : 0 < H) (g g' : ℕ → α × α → α × α) (x : ℕ → α) :
    bfStage H g' (bfStage H g x) = bfStage H (fun c p => g' c (g c p)) x := by
  funext q
  by_cases hr : q % (2 * H) < H
  · obtain ⟨h1, h2⟩ := mod_div_add_half hH hr
    have hn : ¬(q % (2 * H) + H < H) := by omega
    simp only [bfStage, hr, ite_true, h1, h2, hn, ite_false, Nat.add_sub_cancel]
  · obtain ⟨h0, h1, h2⟩ := mod_div_sub_half hH hr
    have hy : q % (2 * H) - H < H := by have := Nat.mod_lt q (by omega : 0 < 2 * H); omega
    simp only [bfStage, hr, ite_false, h1, h2, hy, ite_true, Nat.sub_add_cancel h0]

/-- A slot in the first half of a block inside `[0, 2^k)` has its partner inside too. -/
private theorem add_half_lt {k H q : ℕ} (hH : 2 * H ∣ 2 ^ k) (hHpos : 0 < H) (hq : q < 2 ^ k)
    (hr : q % (2 * H) < H) : q + H < 2 ^ k := by
  obtain ⟨d, hd⟩ := hH
  have hdm := Nat.mod_add_div q (2 * H)
  have hc : q / (2 * H) < d := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    calc q < 2 ^ k := hq
      _ = d * (2 * H) := by rw [hd, mul_comm]
  have : 2 * H * (q / (2 * H) + 1) ≤ 2 * H * d := Nat.mul_le_mul_left _ hc
  rw [← hd] at this
  nlinarith

/-- A pair map is non-expansive when each output moves by at most the sum of the input moves. -/
def NonExpansive (g : ℕ → ℂ × ℂ → ℂ × ℂ) : Prop :=
  ∀ c a b a' b', ‖(g c (a, b)).1 - (g c (a', b')).1‖ ≤ ‖a - a'‖ + ‖b - b'‖ ∧
    ‖(g c (a, b)).2 - (g c (a', b')).2‖ ≤ ‖a - a'‖ + ‖b - b'‖

/-- A non-expansive stage at most doubles the largest slot difference. -/
theorem bfStage_sub_le {k H : ℕ} (hH : 2 * H ∣ 2 ^ k) (hHpos : 0 < H)
    {g : ℕ → ℂ × ℂ → ℂ × ℂ} (hg : NonExpansive g) (x y : ℕ → ℂ) (D : ℝ)
    (hxy : ∀ q < 2 ^ k, ‖x q - y q‖ ≤ D) :
    ∀ q < 2 ^ k, ‖bfStage H g x q - bfStage H g y q‖ ≤ 2 * D := by
  intro q hq
  by_cases hr : q % (2 * H) < H
  · have hq' := add_half_lt hH hHpos hq hr
    simp only [bfStage, hr, ite_true]
    linarith [(hg (q / (2 * H)) (x q) (x (q + H)) (y q) (y (q + H))).1, hxy q hq, hxy _ hq']
  · have h0 := (mod_div_sub_half hHpos hr).1
    simp only [bfStage, hr, ite_false]
    linarith [(hg (q / (2 * H)) (x (q - H)) (x q) (y (q - H)) (y q)).2, hxy q hq,
      hxy (q - H) (by omega)]

/-- A non-expansive stage fixing `0` at most doubles the largest slot. -/
theorem bfStage_norm_le {k H : ℕ} (hH : 2 * H ∣ 2 ^ k) (hHpos : 0 < H)
    {g : ℕ → ℂ × ℂ → ℂ × ℂ} (hg : NonExpansive g) (hg0 : ∀ c, g c (0, 0) = (0, 0))
    (x : ℕ → ℂ) (B : ℝ) (hx : ∀ q < 2 ^ k, ‖x q‖ ≤ B) :
    ∀ q < 2 ^ k, ‖bfStage H g x q‖ ≤ 2 * B := by
  have h := bfStage_sub_le hH hHpos hg x (fun _ => 0) B (by simpa using hx)
  intro q hq
  have hz : bfStage H g (fun _ => (0 : ℂ)) q = 0 := by
    unfold bfStage; split_ifs <;> simp [hg0]
  simpa [hz] using h q hq

/-- A stage reads only inside its block, so it respects agreement on `[0, hn)`. -/
theorem bfStage_congr (hn H : ℕ) (hH : 0 < H) (hdvd : 2 * H ∣ hn)
    (g : ℕ → α × α → α × α) (x y : ℕ → α) (hxy : ∀ q < hn, x q = y q) :
    ∀ q < hn, bfStage H g x q = bfStage H g y q := by
  intro q hq
  obtain ⟨d, hd⟩ := hdvd
  unfold bfStage
  split_ifs with hr
  · have hlt : q + H < hn := by
      have hdm := Nat.mod_add_div q (2 * H)
      have hc : q / (2 * H) < d := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; calc q < hn := hq
          _ = d * (2 * H) := by rw [hd, mul_comm]
      have : 2 * H * (q / (2 * H) + 1) ≤ 2 * H * d := Nat.mul_le_mul_left _ hc
      nlinarith
    rw [hxy q hq, hxy (q + H) hlt]
  · rw [hxy q hq, hxy (q - H) (by omega)]

/-! ## The exact stages -/

/-- The twiddle of block `c` at stage `s`: `exp(i · rootAngle s c / 2)`, the square root of the
block's root `exp(i · rootAngle s c)` that the reference table stores. -/
@[expose] noncomputable def twiddle (s c : ℕ) : ℂ := exp (((rootAngle s c / 2 : ℝ) : ℂ) * I)

/-- The twiddles lie on the unit circle. -/
theorem norm_twiddle (s c : ℕ) : ‖twiddle s c‖ = 1 := by
  rw [twiddle, Complex.norm_exp_ofReal_mul_I]

private theorem conj_twiddle_mul (s c : ℕ) :
    (starRingEnd ℂ) (twiddle s c) * twiddle s c = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_twiddle]; simp

/-- The forward butterfly `(a, b) ↦ (a + σ · b, a - σ · b)`. -/
@[expose] def fwdBF (σ : ℂ) (p : ℂ × ℂ) : ℂ × ℂ := (p.1 + σ * p.2, p.1 - σ * p.2)

/-- The inverse butterfly `(a, b) ↦ (a + b, (a - b) · σ̄)`. -/
@[expose] def invBF (σ : ℂ) (p : ℂ × ℂ) : ℂ × ℂ := (p.1 + p.2, (p.1 - p.2) * (starRingEnd ℂ) σ)

/-- Stage `s` of the forward transform on `2^k` slots: half-blocks of `2^(k - 1 - s)`. -/
@[expose] noncomputable def fwdStage (k s : ℕ) : (ℕ → ℂ) → ℕ → ℂ :=
  bfStage (2 ^ (k - 1 - s)) fun c => fwdBF (twiddle s c)

/-- Stage `s` of the inverse transform on `2^k` slots. -/
@[expose] noncomputable def invStage (k s : ℕ) : (ℕ → ℂ) → ℕ → ℂ :=
  bfStage (2 ^ (k - 1 - s)) fun c => invBF (twiddle s c)

/-- The first `s` forward stages. -/
@[expose] noncomputable def fwdStages (k : ℕ) : ℕ → (ℕ → ℂ) → ℕ → ℂ
  | 0, x => x
  | s + 1, x => fwdStage k s (fwdStages k s x)

/-- The first `j` inverse stages, which are the forward stages `k - 1, …, k - j` inverted. -/
@[expose] noncomputable def invStages (k : ℕ) : ℕ → (ℕ → ℂ) → ℕ → ℂ
  | 0, x => x
  | j + 1, x => invStage k (k - 1 - j) (invStages k j x)

private theorem fwdBF_nonExpansive (σ : ℕ → ℂ) (hσ : ∀ c, ‖σ c‖ = 1) :
    NonExpansive fun c => fwdBF (σ c) := by
  intro c a b a' b'
  simp only [fwdBF]
  constructor
  · calc ‖a + σ c * b - (a' + σ c * b')‖ = ‖(a - a') + σ c * (b - b')‖ := by congr 1; ring
      _ ≤ ‖a - a'‖ + ‖σ c * (b - b')‖ := norm_add_le _ _
      _ = ‖a - a'‖ + ‖b - b'‖ := by rw [norm_mul, hσ, one_mul]
  · calc ‖a - σ c * b - (a' - σ c * b')‖ = ‖(a - a') - σ c * (b - b')‖ := by congr 1; ring
      _ ≤ ‖a - a'‖ + ‖σ c * (b - b')‖ := norm_sub_le _ _
      _ = ‖a - a'‖ + ‖b - b'‖ := by rw [norm_mul, hσ, one_mul]

private theorem invBF_nonExpansive (σ : ℕ → ℂ) (hσ : ∀ c, ‖σ c‖ = 1) :
    NonExpansive fun c => invBF (σ c) := by
  intro c a b a' b'
  simp only [invBF]
  constructor
  · calc ‖a + b - (a' + b')‖ = ‖(a - a') + (b - b')‖ := by congr 1; ring
      _ ≤ ‖a - a'‖ + ‖b - b'‖ := norm_add_le _ _
  · calc ‖(a - b) * (starRingEnd ℂ) (σ c) - (a' - b') * (starRingEnd ℂ) (σ c)‖ =
          ‖(a - a') - (b - b')‖ * ‖(starRingEnd ℂ) (σ c)‖ := by
            rw [← norm_mul]; congr 1; ring
      _ = ‖(a - a') - (b - b')‖ := by rw [Complex.norm_conj, hσ, mul_one]
      _ ≤ ‖a - a'‖ + ‖b - b'‖ := norm_sub_le _ _

private theorem two_mul_two_pow_dvd {k s : ℕ} (hs : s < k) : 2 * 2 ^ (k - 1 - s) ∣ 2 ^ k :=
  ⟨2 ^ s, by rw [← pow_succ', ← pow_add]; congr 1; omega⟩

/-- A forward stage at most doubles the largest slot difference. -/
theorem fwdStage_sub_le {k s : ℕ} (hs : s < k) (x y : ℕ → ℂ) (D : ℝ)
    (hxy : ∀ q < 2 ^ k, ‖x q - y q‖ ≤ D) :
    ∀ q < 2 ^ k, ‖fwdStage k s x q - fwdStage k s y q‖ ≤ 2 * D :=
  bfStage_sub_le (two_mul_two_pow_dvd hs) (by positivity)
    (fwdBF_nonExpansive _ fun c => norm_twiddle s c) x y D hxy

/-- An inverse stage at most doubles the largest slot difference. -/
theorem invStage_sub_le {k s : ℕ} (hs : s < k) (x y : ℕ → ℂ) (D : ℝ)
    (hxy : ∀ q < 2 ^ k, ‖x q - y q‖ ≤ D) :
    ∀ q < 2 ^ k, ‖invStage k s x q - invStage k s y q‖ ≤ 2 * D :=
  bfStage_sub_le (two_mul_two_pow_dvd hs) (by positivity)
    (invBF_nonExpansive _ fun c => norm_twiddle s c) x y D hxy

/-- A forward stage at most doubles the largest slot. -/
theorem fwdStage_norm_le {k s : ℕ} (hs : s < k) (x : ℕ → ℂ) (B : ℝ)
    (hx : ∀ q < 2 ^ k, ‖x q‖ ≤ B) : ∀ q < 2 ^ k, ‖fwdStage k s x q‖ ≤ 2 * B :=
  bfStage_norm_le (two_mul_two_pow_dvd hs) (by positivity)
    (fwdBF_nonExpansive _ fun c => norm_twiddle s c) (fun _ => by simp [fwdBF]) x B hx

/-- An inverse stage at most doubles the largest slot. -/
theorem invStage_norm_le {k s : ℕ} (hs : s < k) (x : ℕ → ℂ) (B : ℝ)
    (hx : ∀ q < 2 ^ k, ‖x q‖ ≤ B) : ∀ q < 2 ^ k, ‖invStage k s x q‖ ≤ 2 * B :=
  bfStage_norm_le (two_mul_two_pow_dvd hs) (by positivity)
    (invBF_nonExpansive _ fun c => norm_twiddle s c) (fun _ => by simp [invBF]) x B hx

/-- The forward stages read only the slots in `[0, 2^k)`. -/
theorem fwdStages_congr (k : ℕ) : ∀ s ≤ k, ∀ x y : ℕ → ℂ, (∀ q < 2 ^ k, x q = y q) →
    ∀ q < 2 ^ k, fwdStages k s x q = fwdStages k s y q := by
  intro s
  induction s with
  | zero => intro _ x y h; exact h
  | succ s ih =>
    intro hs x y h
    exact bfStage_congr (2 ^ k) _ (by positivity) (two_mul_two_pow_dvd (s := s) (by omega))
      (fun c => fwdBF (twiddle s c)) _ _ (ih (by omega) x y h)

/-- The inverse stages read only the slots in `[0, 2^k)`. -/
theorem invStages_congr (k : ℕ) : ∀ j ≤ k, ∀ x y : ℕ → ℂ, (∀ q < 2 ^ k, x q = y q) →
    ∀ q < 2 ^ k, invStages k j x q = invStages k j y q := by
  intro j
  induction j with
  | zero => intro _ x y h; exact h
  | succ j ih =>
    intro hj x y h
    exact bfStage_congr (2 ^ k) _ (by positivity) (two_mul_two_pow_dvd (s := k - 1 - j) (by omega))
      (fun c => invBF (twiddle (k - 1 - j) c)) _ _ (ih (by omega) x y h)

/-! ## The exact stages evaluate -/

private theorem mul_add_mod_div {T c j : ℕ} (hj : j < T) :
    (c * T + j) % T = j ∧ (c * T + j) / T = c := by
  have hT : 0 < T := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hT, Nat.div_eq_of_lt hj, zero_add]

private theorem exp_rootAngle_succ (s c b : ℕ) (hb : b < 2) :
    exp (((rootAngle (s + 1) (2 * c + b) : ℝ) : ℂ) * I) =
      (if b = 0 then 1 else -1) * twiddle s c := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · simp [rootAngle_two_mul, twiddle]
  · rw [rootAngle_two_mul_add_one, twiddle]
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    simp

/-- **The residue invariant.** After `s` stages, block `c`, read as a polynomial, takes the value
of the input polynomial at every root `ζ` of `X^(2^(k - s)) - exp(i · rootAngle s c)`. -/
theorem fwdStages_eval (k : ℕ) (x : ℕ → ℂ) : ∀ s ≤ k, ∀ c < 2 ^ s, ∀ ζ : ℂ,
    ζ ^ 2 ^ (k - s) = exp (((rootAngle s c : ℝ) : ℂ) * I) →
    ∑ r ∈ Finset.range (2 ^ (k - s)), fwdStages k s x (c * 2 ^ (k - s) + r) * ζ ^ r =
      ∑ r ∈ Finset.range (2 ^ k), x r * ζ ^ r := by
  intro s
  induction s with
  | zero =>
    intro _ c hc ζ _
    have hc0 : c = 0 := by simpa using hc
    subst hc0
    simp [fwdStages]
  | succ s ih =>
    intro hs c' hc' ζ hζ
    set H := 2 ^ (k - (s + 1)) with hHdef
    have hTH : 2 ^ (k - s) = H + H := by
      rw [hHdef, ← two_mul, ← pow_succ']; congr 1; omega
    have hHpos : 0 < H := by positivity
    have hk1 : k - 1 - s = k - (s + 1) := by omega
    set c := c' / 2 with hcdef
    set b := c' % 2 with hbdef
    have hb : b < 2 := Nat.mod_lt _ (by norm_num)
    have hc'cb : c' = 2 * c + b := by have := Nat.mod_add_div c' 2; omega
    have hc : c < 2 ^ s := by
      have : c' < 2 * 2 ^ s := by rw [← pow_succ']; exact hc'
      omega
    have hζH : ζ ^ H = (if b = 0 then 1 else -1) * twiddle s c := by
      rw [hζ, hc'cb, exp_rootAngle_succ s c b hb]
    have hsq : (if b = 0 then (1 : ℂ) else -1) * (if b = 0 then 1 else -1) = 1 := by
      split_ifs <;> norm_num
    have hζT : ζ ^ 2 ^ (k - s) = exp (((rootAngle s c : ℝ) : ℂ) * I) := by
      rw [hTH, pow_add, hζH]
      calc (if b = 0 then (1 : ℂ) else -1) * twiddle s c * ((if b = 0 then 1 else -1) * twiddle s c)
          = ((if b = 0 then (1 : ℂ) else -1) * (if b = 0 then 1 else -1)) *
              (twiddle s c * twiddle s c) := by ring
        _ = twiddle s c * twiddle s c := by rw [hsq, one_mul]
        _ = exp (((rootAngle s c : ℝ) : ℂ) * I) := by
            rw [twiddle, ← Complex.exp_add]; congr 1; push_cast; ring
    set y := fwdStages k s x with hy
    have hstep : fwdStages k (s + 1) x = bfStage H (fun c => fwdBF (twiddle s c)) y := by
      change fwdStage k s y = _
      rw [fwdStage, hk1, hHdef]
    have hslot : ∀ r < H, fwdStages k (s + 1) x (c' * H + r) =
        y (c * (H + H) + r) +
          (if b = 0 then 1 else -1) * twiddle s c * y (c * (H + H) + (H + r)) := by
      intro r hr
      rw [← two_mul]
      have hidx : c' * H + r = c * (2 * H) + (b * H + r) := by rw [hc'cb]; ring
      have hlt : b * H + r < 2 * H := by
        rcases (by omega : b = 0 ∨ b = 1) with h | h <;> rw [h] <;> omega
      obtain ⟨hm, hd⟩ := mul_add_mod_div (c := c) hlt
      rw [hstep, hidx]
      unfold bfStage
      rw [hm, hd]
      rcases (by omega : b = 0 ∨ b = 1) with h | h
      · simp only [h, fwdBF, zero_mul, zero_add, hr, ↓reduceIte, one_mul]
        rw [show c * (2 * H) + r + H = c * (2 * H) + (H + r) by ring]
      · have hcnd : ¬(H + r < H) := by omega
        simp only [h, fwdBF, one_mul, hcnd, ite_false, one_ne_zero]
        rw [show c * (2 * H) + (H + r) - H = c * (2 * H) + r by omega]
        ring
    rw [← ih (by omega) c hc ζ hζT, hTH, Finset.sum_range_add]
    calc ∑ r ∈ Finset.range H, fwdStages k (s + 1) x (c' * H + r) * ζ ^ r
        = ∑ r ∈ Finset.range H, (y (c * (H + H) + r) * ζ ^ r +
            y (c * (H + H) + (H + r)) * ζ ^ (H + r)) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [hslot r (Finset.mem_range.mp hr), pow_add, hζH]
          ring
      _ = _ := Finset.sum_add_distrib

/-- **The exact stages compute the packed FFT.** Slot `c` of the `k` stages is the input,
read as a polynomial, at `exp(i · rootAngle k c)`. -/
theorem fwdStages_apply (k : ℕ) (x : ℕ → ℂ) (c : ℕ) (hc : c < 2 ^ k) :
    fwdStages k k x c =
      ∑ r ∈ Finset.range (2 ^ k), x r * exp (((rootAngle k c : ℝ) : ℂ) * I) ^ r := by
  have h := fwdStages_eval k x k le_rfl c hc (exp (((rootAngle k c : ℝ) : ℂ) * I)) (by simp)
  simpa using h

private theorem exp_two_pow_mul_rootAngle : ∀ (k c : ℕ),
    exp ((((2 ^ k : ℕ) : ℝ) * rootAngle k c : ℝ) * I) = I
  | 0, c => by
    have h : ((((2 ^ 0 : ℕ) : ℝ) * rootAngle 0 c : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by simp
    rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    simp
  | k + 1, c => by
    have h : (((2 ^ (k + 1) : ℕ) : ℝ) * rootAngle (k + 1) c : ℝ) =
        (((2 ^ k : ℕ) : ℝ) * rootAngle k (c / 2) : ℝ) +
          (((2 ^ k * (c % 2) : ℕ) : ℝ) * (2 * Real.pi)) := by
      simp only [rootAngle]; push_cast; ring
    rw [h, Complex.ofReal_add, add_mul, Complex.exp_add, exp_two_pow_mul_rootAngle k (c / 2)]
    rw [show (((((2 ^ k * (c % 2) : ℕ) : ℝ) * (2 * Real.pi) : ℝ)) : ℂ) * I =
        ((2 ^ k * (c % 2) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * I) by push_cast; ring,
      Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- A coefficient function on `Fin (2 * 2^k)`, extended by `0`. -/
@[expose] noncomputable def extend {k : ℕ} (f : Fin (2 * 2 ^ k) → ℝ) : ℕ → ℝ := fun m =>
  if h : m < 2 * 2 ^ k then f ⟨m, h⟩ else 0

/-- The `2^k` complex slots of `2 · 2^k` real coefficients: `fᵣ + i · f_{r + 2^k}`. -/
@[expose] noncomputable def complexify {k : ℕ} (f : Fin (2 * 2 ^ k) → ℝ) : ℕ → ℂ := fun r =>
  (extend f r : ℂ) + I * (extend f (r + 2 ^ k) : ℂ)

/-- **The packed FFT of the specification is the stage transform of the complex slots.** -/
theorem coord_ofCoeffs_eq_fwdStages (k : ℕ) (f : Fin (2 * 2 ^ k) → ℝ) (j : Fin (2 ^ k)) :
    RealFFTPoly.coord (RealFFTPoly.ofCoeffs k f) j = fwdStages k k (complexify f) j := by
  rw [RealFFTPoly.coord_ofCoeffs, fwdStages_apply k _ j j.2, evalAngle]
  set θ := rootAngle k j.1
  set ω := exp ((θ : ℂ) * I) with hω
  have hpow : ∀ m : ℕ, exp ((((m : ℝ) * θ : ℝ) : ℂ) * I) = ω ^ m := by
    intro m; rw [hω, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hI : ω ^ 2 ^ k = I := by
    rw [← hpow (2 ^ k)]; exact exp_two_pow_mul_rootAngle k j.1
  have hsum : ∑ m : Fin (2 * 2 ^ k), (f m : ℂ) * exp ((((m : ℕ) : ℝ) * θ : ℝ) * I) =
      ∑ m ∈ Finset.range (2 * 2 ^ k), (extend f m : ℂ) * ω ^ m := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => (extend f m : ℂ) * ω ^ m)]
    apply Finset.sum_congr rfl
    intro m _
    rw [hpow]
    simp [extend, m.2]
  rw [hsum, two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [complexify, pow_add, hI, Nat.add_comm (2 ^ k) r]
  ring

/-! ## The inverse stages -/

private theorem invStage_fwdStage {k s : ℕ} (x : ℕ → ℂ) :
    invStage k s (fwdStage k s x) = fun q => 2 * x q := by
  rw [invStage, fwdStage, bfStage_bfStage _ (by positivity)]
  funext q
  have hc : ∀ c, ∀ p : ℂ × ℂ, invBF (twiddle s c) (fwdBF (twiddle s c) p) = (2 * p.1, 2 * p.2) := by
    intro c p
    have h := conj_twiddle_mul s c
    simp only [invBF, fwdBF, Prod.mk.injEq]
    constructor
    · ring
    · linear_combination (2 * p.2) * h
  unfold bfStage
  split_ifs <;> simp [hc]

private theorem invStage_smul {k s : ℕ} (a : ℂ) (x : ℕ → ℂ) :
    invStage k s (fun q => a * x q) = fun q => a * invStage k s x q := by
  funext q
  unfold invStage bfStage
  split_ifs <;> simp only [invBF] <;> ring

/-- **The inverse stages undo the forward stages**, up to the factor `2^k` that the reference
removes by its final scaling. -/
theorem invStages_fwdStages (k : ℕ) (x : ℕ → ℂ) :
    invStages k k (fwdStages k k x) = fun q => 2 ^ k * x q := by
  have key : ∀ j ≤ k,
      invStages k j (fwdStages k k x) = fun q => 2 ^ j * fwdStages k (k - j) x q := by
    intro j
    induction j with
    | zero => intro _; funext q; simp [invStages]
    | succ j ih =>
      intro hj
      rw [invStages, ih (by omega), invStage_smul]
      have hkj : k - j = (k - 1 - j) + 1 := by omega
      rw [hkj, show fwdStages k (k - 1 - j + 1) x =
          fwdStage k (k - 1 - j) (fwdStages k (k - 1 - j) x) from rfl, invStage_fwdStage,
        show k - (j + 1) = k - 1 - j by omega]
      funext q; simp only; ring
  rw [key k le_rfl]
  funext q; simp [fwdStages]

/-! ## Error recursion -/

/-- **The stage error recursion.** Let `u s` be the slots of a computed transform after `s`
stages and `v s` those of an exact one, `v (s + 1) = S s (v s)`, from the same inputs bounded by
`A`. If each exact stage at most doubles slot differences and slot moduli, and computed stage `s`
lands within `η · (2 + η)^s · A` of the exact stage applied to the computed input whenever the
invariant `P s` holds and the input is bounded by `(2 + η)^s · A`, re-establishing `P (s + 1)`,
then after `K` stages every slot is within `((2 + η)^K - 2^K) · A` of the exact transform. -/
theorem stages_error (N K : ℕ) (u v : ℕ → ℕ → ℂ) (S : ℕ → (ℕ → ℂ) → ℕ → ℂ) (P : ℕ → Prop)
    (η A : ℝ) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hS : ∀ s < K, ∀ x y : ℕ → ℂ, ∀ D : ℝ, (∀ q < N, ‖x q - y q‖ ≤ D) →
      ∀ q < N, ‖S s x q - S s y q‖ ≤ 2 * D)
    (hSb : ∀ s < K, ∀ x : ℕ → ℂ, ∀ B : ℝ, (∀ q < N, ‖x q‖ ≤ B) → ∀ q < N, ‖S s x q‖ ≤ 2 * B)
    (hv : ∀ s, v (s + 1) = S s (v s)) (h0 : ∀ q < N, u 0 q = v 0 q)
    (hA0 : ∀ q < N, ‖u 0 q‖ ≤ A) (hP0 : P 0)
    (hloc : ∀ s < K, P s → (∀ q < N, ‖u s q‖ ≤ (2 + η) ^ s * A) →
      P (s + 1) ∧ ∀ q < N, ‖u (s + 1) q - S s (u s) q‖ ≤ η * ((2 + η) ^ s * A)) :
    ∀ s ≤ K, P s ∧ (∀ q < N, ‖u s q‖ ≤ (2 + η) ^ s * A) ∧
      ∀ q < N, ‖u s q - v s q‖ ≤ ((2 + η) ^ s - 2 ^ s) * A := by
  intro s
  induction s with
  | zero =>
    intro _
    refine ⟨hP0, by simpa using hA0, fun q hq => ?_⟩
    simp [h0 q hq]
  | succ s ih =>
    intro hs
    obtain ⟨hPs, hus, hes⟩ := ih (by omega)
    obtain ⟨hPs', hloc'⟩ := hloc s (by omega) hPs hus
    have hpow : 0 ≤ (2 + η) ^ s * A := by positivity
    have hSu := hSb s (by omega) (u s) _ hus
    have hSuv := hS s (by omega) (u s) (v s) _ hes
    refine ⟨hPs', fun q hq => ?_, fun q hq => ?_⟩
    · calc ‖u (s + 1) q‖ = ‖(u (s + 1) q - S s (u s) q) + S s (u s) q‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖u (s + 1) q - S s (u s) q‖ + ‖S s (u s) q‖ := norm_add_le _ _
        _ ≤ η * ((2 + η) ^ s * A) + 2 * ((2 + η) ^ s * A) := add_le_add (hloc' q hq) (hSu q hq)
        _ = (2 + η) ^ (s + 1) * A := by ring
    · rw [hv s]
      calc ‖u (s + 1) q - S s (v s) q‖ =
            ‖(u (s + 1) q - S s (u s) q) + (S s (u s) q - S s (v s) q)‖ := by
              rw [sub_add_sub_cancel]
        _ ≤ ‖u (s + 1) q - S s (u s) q‖ + ‖S s (u s) q - S s (v s) q‖ := norm_add_le _ _
        _ ≤ η * ((2 + η) ^ s * A) + 2 * (((2 + η) ^ s - 2 ^ s) * A) :=
            add_le_add (hloc' q hq) (hSuv q hq)
        _ = ((2 + η) ^ (s + 1) - 2 ^ (s + 1)) * A := by ring

/-- `s` exact forward stages at most multiply the largest slot by `2^s`. -/
theorem fwdStages_norm_le (k : ℕ) : ∀ s ≤ k, ∀ (x : ℕ → ℂ) (B : ℝ),
    (∀ q < 2 ^ k, ‖x q‖ ≤ B) → ∀ q < 2 ^ k, ‖fwdStages k s x q‖ ≤ 2 ^ s * B := by
  intro s
  induction s with
  | zero => intro _ x B h q hq; simpa [fwdStages] using h q hq
  | succ s ih =>
    intro hs x B h q hq
    have := fwdStage_norm_le (by omega : s < k) _ _ (ih (by omega) x B h) q hq
    simpa [fwdStages, pow_succ, mul_comm, mul_left_comm, mul_assoc] using this

/-- `j` exact inverse stages at most multiply the largest slot difference by `2^j`. -/
theorem invStages_sub_le (k : ℕ) : ∀ j ≤ k, ∀ (x y : ℕ → ℂ) (D : ℝ),
    (∀ q < 2 ^ k, ‖x q - y q‖ ≤ D) →
      ∀ q < 2 ^ k, ‖invStages k j x q - invStages k j y q‖ ≤ 2 ^ j * D := by
  intro j
  induction j with
  | zero => intro _ x y D h q hq; simpa [invStages] using h q hq
  | succ j ih =>
    intro hj x y D h q hq
    have := invStage_sub_le (by omega : k - 1 - j < k) _ _ _ (ih (by omega) x y D h) q hq
    simpa [invStages, pow_succ, mul_comm, mul_left_comm, mul_assoc] using this

/-- `j` exact inverse stages at most multiply the largest slot by `2^j`. -/
theorem invStages_norm_le (k : ℕ) : ∀ j ≤ k, ∀ (x : ℕ → ℂ) (B : ℝ),
    (∀ q < 2 ^ k, ‖x q‖ ≤ B) → ∀ q < 2 ^ k, ‖invStages k j x q‖ ≤ 2 ^ j * B := by
  intro j
  induction j with
  | zero => intro _ x B h q hq; simpa [invStages] using h q hq
  | succ j ih =>
    intro hj x B h q hq
    have := invStage_norm_le (by omega : k - 1 - j < k) _ _ (ih (by omega) x B h) q hq
    simpa [invStages, pow_succ, mul_comm, mul_left_comm, mul_assoc] using this

end FFTStages

end Falcon

end
