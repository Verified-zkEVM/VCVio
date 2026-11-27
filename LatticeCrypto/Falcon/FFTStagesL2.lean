/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all LatticeCrypto.Falcon.FFTStages
public import LatticeCrypto.Falcon.FFTStages

/-!
# The packed FFT stages in `ℓ²`

`Falcon.FFTStages` bounds computed butterfly stages slot by slot. This file gives the `ℓ²`
counterparts over the first `N` slots (`rangeL2`), for any computed transform:

- `sum_sq_fwdStage_sub`: an exact forward stage multiplies the squared `ℓ²` distance of two
  inputs by exactly `2`;
- `sum_norm_coord_ofCoeffs_sq` (Parseval): the squared slots of the packed FFT of `2 · 2^k` real
  coefficients sum to `2^k` times the squared coefficients;
- `stages_error_l2`: the `ℓ²` error recursion. A computed transform whose stage `s` lands within
  `η · ‖u s‖ + b` of the exact stage applied to its own input, in `ℓ²`, ends within
  `K · η · (√2 + η)^(K-1) · X + b · ∑_{j < K} (√2 + η)^j` of the exact transform of an input of
  `ℓ²` norm at most `X`. An invariant `P s` is threaded through the stages, as in
  `Falcon.FFTStages.stages_error`;
- `rangeL2_le_of_pairMax`, `rangeL2_bfStage_sub_le`: a stage whose slots are within
  `c₀ + δ · max ‖a‖ ‖b‖` of the exact stage, `(a, b)` the pair holding the slot, is within
  `√2 · δ · ‖x‖ + c₀ · √N` of it in `ℓ²`;
- `sum_sq_mul_sub_le`: the squared `ℓ²` error of a slotwise product, from an `ℓ²` bound on one
  factor's error and slotwise bounds on the other's.
-/

public section

open Complex

namespace Falcon

namespace FFTStages

/-! ## The `ℓ²` norm of the first `N` slots -/

/-- The `ℓ²` norm of the slots `0, …, N - 1`. -/
@[expose] noncomputable def rangeL2 (N : ℕ) (x : ℕ → ℂ) : ℝ :=
  √(∑ q ∈ Finset.range N, ‖x q‖ ^ 2)

theorem rangeL2_nonneg (N : ℕ) (x : ℕ → ℂ) : 0 ≤ rangeL2 N x := Real.sqrt_nonneg _

theorem rangeL2_sq (N : ℕ) (x : ℕ → ℂ) :
    rangeL2 N x ^ 2 = ∑ q ∈ Finset.range N, ‖x q‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem rangeL2_eq_norm (N : ℕ) (x : ℕ → ℂ) :
    rangeL2 N x = ‖(WithLp.toLp 2 (fun i : Fin N => x i) : PiLp 2 fun _ : Fin N => ℂ)‖ := by
  rw [PiLp.norm_eq_of_L2, rangeL2, ← Fin.sum_univ_eq_sum_range (fun q => ‖x q‖ ^ 2)]

/-- The triangle inequality for `rangeL2`. -/
theorem rangeL2_add_le (N : ℕ) (x y : ℕ → ℂ) :
    rangeL2 N (fun q => x q + y q) ≤ rangeL2 N x + rangeL2 N y := by
  rw [rangeL2_eq_norm, rangeL2_eq_norm N x, rangeL2_eq_norm N y]
  calc _ = ‖(WithLp.toLp 2 (fun i : Fin N => x i) : PiLp 2 fun _ : Fin N => ℂ) +
        WithLp.toLp 2 (fun i : Fin N => y i)‖ := by rw [← WithLp.toLp_add]; rfl
    _ ≤ _ := norm_add_le _ _

theorem rangeL2_sub_le (N : ℕ) (a b c : ℕ → ℂ) :
    rangeL2 N (fun q => a q - c q) ≤
      rangeL2 N (fun q => a q - b q) + rangeL2 N (fun q => b q - c q) := by
  have h := rangeL2_add_le N (fun q => a q - b q) (fun q => b q - c q)
  have e : (fun q => a q - b q + (b q - c q)) = fun q => a q - c q := by funext q; ring
  rw [e] at h
  exact h

theorem rangeL2_le_add_sub (N : ℕ) (x y : ℕ → ℂ) :
    rangeL2 N x ≤ rangeL2 N y + rangeL2 N (fun q => x q - y q) := by
  have h := rangeL2_add_le N y (fun q => x q - y q)
  have e : (fun q => y q + (x q - y q)) = x := by funext q; ring
  rw [e] at h
  exact h

theorem rangeL2_le_of_norm_le (N : ℕ) (x y : ℕ → ℂ) (h : ∀ q < N, ‖x q‖ ≤ ‖y q‖) :
    rangeL2 N x ≤ rangeL2 N y :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun q hq =>
    pow_le_pow_left₀ (norm_nonneg _) (h q (Finset.mem_range.mp hq)) 2)

private theorem rangeL2_const (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    rangeL2 N (fun _ => (c : ℂ)) = c * √(N : ℝ) := by
  unfold rangeL2
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc, Real.sqrt_mul (by positivity), Real.sqrt_sq hc, mul_comm]

private theorem rangeL2_ofReal_mul_norm (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (w : ℕ → ℂ) :
    rangeL2 N (fun q => ((δ * ‖w q‖ : ℝ) : ℂ)) = δ * rangeL2 N w := by
  unfold rangeL2
  have e : ∀ q, ‖((δ * ‖w q‖ : ℝ) : ℂ)‖ ^ 2 = δ ^ 2 * ‖w q‖ ^ 2 := by
    intro q
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hδ (norm_nonneg _)),
      mul_pow]
  simp only [e, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hδ]

/-! ## Stages pair by pair -/

/-- A sum over `M` blocks of `2H` slots, pair by pair. -/
theorem sum_range_pairs (M H : ℕ) (φ : ℕ → ℝ) :
    ∑ q ∈ Finset.range (M * (2 * H)), φ q =
      ∑ c ∈ Finset.range M, ∑ r ∈ Finset.range H,
        (φ (c * (2 * H) + r) + φ (c * (2 * H) + (H + r))) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show (M + 1) * (2 * H) = M * (2 * H) + (H + H) by ring, Finset.sum_range_add,
      Finset.sum_range_add, ih, Finset.sum_range_succ, Finset.sum_add_distrib]

/-- The first slot of a pair. -/
theorem bfStage_pair_fst {α : Type*} (H : ℕ) (g : ℕ → α × α → α × α) (x : ℕ → α) (c r : ℕ)
    (hr : r < H) :
    bfStage H g x (c * (2 * H) + r) =
      (g c (x (c * (2 * H) + r), x (c * (2 * H) + (H + r)))).1 := by
  obtain ⟨hm, hd⟩ := mul_add_mod_div (c := c) (show r < 2 * H by omega)
  unfold bfStage
  rw [hm, hd]
  simp only [hr, ↓reduceIte]
  rw [show c * (2 * H) + r + H = c * (2 * H) + (H + r) by omega]

/-- The second slot of a pair. -/
theorem bfStage_pair_snd {α : Type*} (H : ℕ) (g : ℕ → α × α → α × α) (x : ℕ → α) (c r : ℕ)
    (hr : r < H) :
    bfStage H g x (c * (2 * H) + (H + r)) =
      (g c (x (c * (2 * H) + r), x (c * (2 * H) + (H + r)))).2 := by
  obtain ⟨hm, hd⟩ := mul_add_mod_div (c := c) (show H + r < 2 * H by omega)
  unfold bfStage
  have hn : ¬(H + r < H) := by omega
  rw [hm, hd]
  simp only [hn, ↓reduceIte]
  rw [show c * (2 * H) + (H + r) - H = c * (2 * H) + r by omega]

/-- The squared distance of two stages, pair by pair. -/
theorem sum_sq_bfStage_sub (M H : ℕ) (g g' : ℕ → ℂ × ℂ → ℂ × ℂ) (x y : ℕ → ℂ) :
    ∑ q ∈ Finset.range (M * (2 * H)), ‖bfStage H g x q - bfStage H g' y q‖ ^ 2 =
      ∑ c ∈ Finset.range M, ∑ r ∈ Finset.range H,
        (‖(g c (x (c * (2 * H) + r), x (c * (2 * H) + (H + r)))).1 -
            (g' c (y (c * (2 * H) + r), y (c * (2 * H) + (H + r)))).1‖ ^ 2 +
          ‖(g c (x (c * (2 * H) + r), x (c * (2 * H) + (H + r)))).2 -
            (g' c (y (c * (2 * H) + r), y (c * (2 * H) + (H + r)))).2‖ ^ 2) := by
  rw [sum_range_pairs]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.mp hr
  rw [bfStage_pair_fst H g x c r hr', bfStage_pair_fst H g' y c r hr',
    bfStage_pair_snd H g x c r hr', bfStage_pair_snd H g' y c r hr']

/-- `2^k` is `2^s` blocks of `2 · 2^(k - 1 - s)` slots. -/
theorem two_pow_eq_blocks {k s : ℕ} (hs : s < k) :
    2 ^ k = 2 ^ s * (2 * 2 ^ (k - 1 - s)) := by
  rw [← pow_succ', ← pow_add]; congr 1; omega

private theorem pair_fwd (σ a b a' b' : ℂ) (hσ : ‖σ‖ = 1) :
    ‖a + σ * b - (a' + σ * b')‖ ^ 2 + ‖a - σ * b - (a' - σ * b')‖ ^ 2 =
      2 * (‖a - a'‖ ^ 2 + ‖b - b'‖ ^ 2) := by
  have h := parallelogram_law_with_norm ℝ (a - a') (σ * (b - b'))
  have e1 : a + σ * b - (a' + σ * b') = (a - a') + σ * (b - b') := by ring
  have e2 : a - σ * b - (a' - σ * b') = (a - a') - σ * (b - b') := by ring
  have hn : ‖σ * (b - b')‖ = ‖b - b'‖ := by rw [norm_mul, hσ, one_mul]
  rw [hn] at h
  rw [e1, e2]
  simp only [sq]
  linarith

/-- An exact forward stage doubles the squared `ℓ²` distance of two inputs. -/
theorem sum_sq_fwdStage_sub {k s : ℕ} (hs : s < k) (x y : ℕ → ℂ) :
    ∑ q ∈ Finset.range (2 ^ k), ‖fwdStage k s x q - fwdStage k s y q‖ ^ 2 =
      2 * ∑ q ∈ Finset.range (2 ^ k), ‖x q - y q‖ ^ 2 := by
  rw [two_pow_eq_blocks hs, fwdStage, sum_sq_bfStage_sub, sum_range_pairs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [fwdBF]
  exact pair_fwd _ _ _ _ _ (norm_twiddle s c)

theorem fwdStage_zero (k s : ℕ) : fwdStage k s (fun _ => 0) = fun _ => 0 := by
  funext q; unfold fwdStage bfStage; split_ifs <;> simp [fwdBF]

/-- An exact forward stage multiplies the `ℓ²` distance of two inputs by `√2`. -/
theorem rangeL2_fwdStage_sub {k s : ℕ} (hs : s < k) (x y : ℕ → ℂ) :
    rangeL2 (2 ^ k) (fun q => fwdStage k s x q - fwdStage k s y q) =
      √2 * rangeL2 (2 ^ k) (fun q => x q - y q) := by
  unfold rangeL2
  rw [sum_sq_fwdStage_sub hs, Real.sqrt_mul (by norm_num)]

/-- An exact forward stage multiplies the `ℓ²` norm by `√2`. -/
theorem rangeL2_fwdStage {k s : ℕ} (hs : s < k) (x : ℕ → ℂ) :
    rangeL2 (2 ^ k) (fwdStage k s x) = √2 * rangeL2 (2 ^ k) x := by
  have h := rangeL2_fwdStage_sub hs x (fun _ => 0)
  simp only [fwdStage_zero, sub_zero] at h
  exact h

/-! ## Parseval for the packed FFT -/

/-- `s` exact forward stages multiply the squared `ℓ²` norm by `2^s`. -/
theorem sum_sq_fwdStages (k : ℕ) : ∀ s ≤ k, ∀ x : ℕ → ℂ,
    ∑ q ∈ Finset.range (2 ^ k), ‖fwdStages k s x q‖ ^ 2 =
      2 ^ s * ∑ q ∈ Finset.range (2 ^ k), ‖x q‖ ^ 2 := by
  intro s
  induction s with
  | zero => intro _ x; simp [fwdStages]
  | succ s ih =>
    intro hs x
    have h := sum_sq_fwdStage_sub (by omega : s < k) (fwdStages k s x) (fun _ => 0)
    simp only [fwdStage_zero, sub_zero] at h
    rw [show fwdStages k (s + 1) x = fwdStage k s (fwdStages k s x) from rfl, h,
      ih (by omega), pow_succ]
    ring

/-- The squared norm of `a + i · b` for real `a`, `b`. -/
theorem norm_ofReal_add_I_mul_sq (a b : ℝ) : ‖(a : ℂ) + I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- The complex slots `fᵣ + i · f_{r + 2^k}` carry the squared coefficients. -/
theorem sum_norm_complexify_sq (k : ℕ) (f : Fin (2 * 2 ^ k) → ℝ) :
    ∑ q ∈ Finset.range (2 ^ k), ‖complexify f q‖ ^ 2 = ∑ i, f i ^ 2 := by
  have he : ∑ i, f i ^ 2 = ∑ m ∈ Finset.range (2 * 2 ^ k), extend f m ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => extend f m ^ 2)]
    exact Finset.sum_congr rfl fun m _ => by simp [extend, m.2]
  rw [he, two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [complexify, norm_ofReal_add_I_mul_sq, Nat.add_comm (2 ^ k) q]

/-- **Parseval for the packed FFT.** The squared slots of the packed FFT of `2 · 2^k` real
coefficients sum to `2^k` times the squared coefficients. -/
theorem sum_norm_coord_ofCoeffs_sq (k : ℕ) (f : Fin (2 * 2 ^ k) → ℝ) :
    ∑ j, ‖RealFFTPoly.coord (RealFFTPoly.ofCoeffs k f) j‖ ^ 2 = 2 ^ k * ∑ i, f i ^ 2 := by
  simp only [coord_ofCoeffs_eq_fwdStages]
  rw [Fin.sum_univ_eq_sum_range (fun q => ‖fwdStages k k (complexify f) q‖ ^ 2) (2 ^ k),
    sum_sq_fwdStages k k le_rfl, sum_norm_complexify_sq]

/-- A complex slot of coefficients bounded by `Z` has squared norm at most `2 · Z²`. -/
theorem norm_complexify_sq_le {k : ℕ} (f : Fin (2 * 2 ^ k) → ℝ) (Z : ℝ) (hf : ∀ i, |f i| ≤ Z)
    (q : ℕ) : ‖complexify f q‖ ^ 2 ≤ 2 * Z ^ 2 := by
  have hZ : 0 ≤ Z := (abs_nonneg _).trans (hf ⟨0, by positivity⟩)
  have he : ∀ m, extend f m ^ 2 ≤ Z ^ 2 := by
    intro m
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    unfold extend
    split_ifs
    · exact hf _
    · simpa using hZ
  rw [complexify, norm_ofReal_add_I_mul_sq]
  linarith [he q, he (q + 2 ^ k)]

/-! ## The `ℓ²` error recursion -/

private theorem step_identity (s : ℕ) (η X a : ℝ) :
    a * ((s : ℝ) * η * a ^ (s - 1) * X) + η * a ^ s * X =
      ((s + 1 : ℕ) : ℝ) * η * a ^ (s + 1 - 1) * X := by
  cases s with
  | zero => simp
  | succ t => simp only [Nat.add_sub_cancel]; push_cast; ring

private theorem geom_step (s : ℕ) (a : ℝ) :
    a * ∑ j ∈ Finset.range s, a ^ j + 1 = ∑ j ∈ Finset.range (s + 1), a ^ j := by
  rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The `ℓ²` stage error recursion.** Let `u s` be the slots of a computed transform after `s`
stages and `v s` those of an exact one, `v (s + 1) = S s (v s)`, from the same input of `ℓ²` norm
at most `X`. If each exact stage multiplies `ℓ²` distances and norms by at most `√2`, and computed
stage `s` lands within `η · ‖u s‖ + b` of the exact stage applied to the computed input in `ℓ²`
whenever the invariant `P s` holds, re-establishing `P (s + 1)`, then after `s ≤ K` stages the
computed transform is within `s · η · (√2 + η)^(s-1) · X + b · ∑_{j < s} (√2 + η)^j` of the exact
one in `ℓ²`. -/
theorem stages_error_l2 (N K : ℕ) (u v : ℕ → ℕ → ℂ) (S : ℕ → (ℕ → ℂ) → ℕ → ℂ)
    (P : ℕ → Prop) (η b X : ℝ) (hη : 0 ≤ η)
    (hS : ∀ s < K, ∀ x y : ℕ → ℂ,
      rangeL2 N (fun q => S s x q - S s y q) ≤ √2 * rangeL2 N (fun q => x q - y q))
    (hSn : ∀ s < K, ∀ x : ℕ → ℂ, rangeL2 N (S s x) ≤ √2 * rangeL2 N x)
    (hv : ∀ s, v (s + 1) = S s (v s)) (h0 : ∀ q < N, u 0 q = v 0 q)
    (hX : rangeL2 N (v 0) ≤ X) (hP0 : P 0)
    (hloc : ∀ s < K, P s → P (s + 1) ∧
      rangeL2 N (fun q => u (s + 1) q - S s (u s) q) ≤ η * rangeL2 N (u s) + b) :
    ∀ s ≤ K, P s ∧ rangeL2 N (v s) ≤ √2 ^ s * X ∧
      rangeL2 N (fun q => u s q - v s q) ≤
        (s : ℝ) * η * (√2 + η) ^ (s - 1) * X + b * ∑ j ∈ Finset.range s, (√2 + η) ^ j := by
  have hX0 : 0 ≤ X := (rangeL2_nonneg _ _).trans hX
  have hs2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  intro s
  induction s with
  | zero =>
    intro _
    refine ⟨hP0, by simpa using hX, ?_⟩
    have hz : rangeL2 N (fun q => u 0 q - v 0 q) = 0 := by
      unfold rangeL2
      rw [Finset.sum_eq_zero fun q hq => by simp [h0 q (Finset.mem_range.mp hq)]]
      simp
    rw [hz]
    simp
  | succ s ih =>
    intro hs
    obtain ⟨hPs, hvs, hes⟩ := ih (by omega)
    obtain ⟨hPs', hloc'⟩ := hloc s (by omega) hPs
    refine ⟨hPs', ?_, ?_⟩
    · rw [hv s]
      calc rangeL2 N (S s (v s)) ≤ √2 * rangeL2 N (v s) := hSn s (by omega) _
        _ ≤ √2 * (√2 ^ s * X) := mul_le_mul_of_nonneg_left hvs hs2
        _ = √2 ^ (s + 1) * X := by ring
    · have hu : rangeL2 N (u s) ≤ √2 ^ s * X +
          ((s : ℝ) * η * (√2 + η) ^ (s - 1) * X + b * ∑ j ∈ Finset.range s, (√2 + η) ^ j) := by
        have h1 := rangeL2_le_add_sub N (u s) (v s)
        linarith
      have hstep : rangeL2 N (fun q => u (s + 1) q - v (s + 1) q) ≤
          η * rangeL2 N (u s) + b + √2 *
            ((s : ℝ) * η * (√2 + η) ^ (s - 1) * X + b * ∑ j ∈ Finset.range s, (√2 + η) ^ j) := by
        rw [hv s]
        calc _ ≤ rangeL2 N (fun q => u (s + 1) q - S s (u s) q) +
              rangeL2 N (fun q => S s (u s) q - S s (v s) q) := rangeL2_sub_le N _ _ _
          _ ≤ _ := add_le_add hloc' ((hS s (by omega) _ _).trans
              (mul_le_mul_of_nonneg_left hes hs2))
      have hpow : √2 ^ s ≤ (√2 + η) ^ s := pow_le_pow_left₀ hs2 (by linarith) s
      have hprod := mul_le_mul_of_nonneg_left hpow (mul_nonneg hη hX0)
      have hu' := mul_le_mul_of_nonneg_left hu hη
      rw [← step_identity, ← geom_step]
      nlinarith [hstep, hprod, hu']

/-- The bound of `stages_error_l2` at stage factor `√2 · δ` and input norm `√2^k · X`. -/
theorem stages_error_l2_bound_eq (k : ℕ) (δ X : ℝ) :
    (k : ℝ) * (√2 * δ) * (√2 + √2 * δ) ^ (k - 1) * (√2 ^ k * X) =
      k * δ * 2 ^ k * (1 + δ) ^ (k - 1) * X := by
  rcases k with _ | t
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [show √2 + √2 * δ = √2 * (1 + δ) by ring, mul_pow]
    have h : √2 ^ (t + 1) * √2 ^ (t + 1) = (2 : ℝ) ^ (t + 1) := by
      rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
    push_cast
    linear_combination ((t + 1 : ℝ) * δ * (1 + δ) ^ t * X) * h

/-! ## The local `ℓ²` error of a computed stage -/

/-- The stage that puts the larger modulus of each pair on both of its slots. -/
@[expose] noncomputable def pairMax (H : ℕ) (x : ℕ → ℂ) : ℕ → ℂ :=
  bfStage H (fun _ p => (((max ‖p.1‖ ‖p.2‖ : ℝ) : ℂ), ((max ‖p.1‖ ‖p.2‖ : ℝ) : ℂ))) x

private theorem sum_sq_pairMax_le (M H : ℕ) (x : ℕ → ℂ) :
    ∑ q ∈ Finset.range (M * (2 * H)), ‖pairMax H x q‖ ^ 2 ≤
      2 * ∑ q ∈ Finset.range (M * (2 * H)), ‖x q‖ ^ 2 := by
  rw [sum_range_pairs, sum_range_pairs, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hr' := Finset.mem_range.mp hr
  rw [pairMax, bfStage_pair_fst _ _ _ c r hr', bfStage_pair_snd _ _ _ c r hr']
  dsimp only
  rw [Complex.norm_real, Real.norm_of_nonneg (le_max_of_le_left (norm_nonneg _))]
  rcases le_total ‖x (c * (2 * H) + r)‖ ‖x (c * (2 * H) + (H + r))‖ with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg ‖x (c * (2 * H) + r)‖]
  · rw [max_eq_left h]; nlinarith [sq_nonneg ‖x (c * (2 * H) + (H + r))‖]

/-- **`ℓ²` from slotwise errors in pairs.** If every slot `q < N = M · 2H` of `w` is at most
`c₀ + δ · m q`, `m q` the larger modulus of the pair of `x` holding slot `q` (`pairMax`), then `w`
has `ℓ²` norm at most `√2 · δ · ‖x‖ + c₀ · √N`. -/
theorem rangeL2_le_of_pairMax (N M H : ℕ) (hN : N = M * (2 * H)) (w x : ℕ → ℂ) (c₀ δ : ℝ)
    (hc₀ : 0 ≤ c₀) (hδ : 0 ≤ δ) (hw : ∀ q < N, ‖w q‖ ≤ c₀ + δ * ‖pairMax H x q‖) :
    rangeL2 N w ≤ √2 * δ * rangeL2 N x + c₀ * √(N : ℝ) := by
  set m := pairMax H x with hm
  have h1 : rangeL2 N w ≤ rangeL2 N (fun q => ((c₀ + δ * ‖m q‖ : ℝ) : ℂ)) := by
    refine rangeL2_le_of_norm_le N _ _ fun q hq => ?_
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg hc₀ (mul_nonneg hδ (norm_nonneg _)))]
    exact hw q hq
  have h2 : rangeL2 N (fun q => ((c₀ + δ * ‖m q‖ : ℝ) : ℂ)) ≤
      c₀ * √(N : ℝ) + δ * rangeL2 N m := by
    have h := rangeL2_add_le N (fun _ => (c₀ : ℂ)) (fun q => ((δ * ‖m q‖ : ℝ) : ℂ))
    rw [rangeL2_const N c₀ hc₀, rangeL2_ofReal_mul_norm N δ hδ] at h
    convert h using 2
    funext q
    push_cast
    ring
  have hm2 : rangeL2 N m ≤ √2 * rangeL2 N x := by
    unfold rangeL2
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    rw [hN]
    exact sum_sq_pairMax_le M H x
  have h3 := mul_le_mul_of_nonneg_left hm2 hδ
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ √2 * δ * rangeL2 N x + c₀ * √(N : ℝ) := by nlinarith

/-- **Local `ℓ²` error of a stage.** If two pair maps differ by at most `c₀ + δ · max ‖a‖ ‖b‖` on
every pair `(a, b)`, in both components, the two stages differ by at most `√2 · δ · ‖x‖ + c₀ · √N`
in `ℓ²` over `N = M · 2H` slots. -/
theorem rangeL2_bfStage_sub_le (N M H : ℕ) (hN : N = M * (2 * H))
    (g g' : ℕ → ℂ × ℂ → ℂ × ℂ) (x : ℕ → ℂ) (c₀ δ : ℝ) (hc₀ : 0 ≤ c₀) (hδ : 0 ≤ δ)
    (hg : ∀ c p, ‖(g c p).1 - (g' c p).1‖ ≤ c₀ + δ * max ‖p.1‖ ‖p.2‖ ∧
      ‖(g c p).2 - (g' c p).2‖ ≤ c₀ + δ * max ‖p.1‖ ‖p.2‖) :
    rangeL2 N (fun q => bfStage H g x q - bfStage H g' x q) ≤
      √2 * δ * rangeL2 N x + c₀ * √(N : ℝ) := by
  refine rangeL2_le_of_pairMax N M H hN _ x c₀ δ hc₀ hδ fun q _ => ?_
  unfold pairMax bfStage
  split_ifs
  · dsimp only
    rw [Complex.norm_real, Real.norm_of_nonneg (le_max_of_le_left (norm_nonneg _))]
    exact (hg _ _).1
  · dsimp only
    rw [Complex.norm_real, Real.norm_of_nonneg (le_max_of_le_left (norm_nonneg _))]
    exact (hg _ _).2

/-- **Slotwise bound on a stage difference.** If two pair maps differ by at most `E` on pairs of
inputs bounded by `B`, two stages on inputs bounded by `B` differ by at most `E` on every slot. -/
theorem bfStage_sub_le_of_pair {k H : ℕ} (hH : 2 * H ∣ 2 ^ k) (hHpos : 0 < H)
    (g g' : ℕ → ℂ × ℂ → ℂ × ℂ) (y : ℕ → ℂ) (B E : ℝ) (hy : ∀ q < 2 ^ k, ‖y q‖ ≤ B)
    (hg : ∀ c a b, ‖a‖ ≤ B → ‖b‖ ≤ B →
      ‖(g c (a, b)).1 - (g' c (a, b)).1‖ ≤ E ∧ ‖(g c (a, b)).2 - (g' c (a, b)).2‖ ≤ E) :
    ∀ q < 2 ^ k, ‖bfStage H g y q - bfStage H g' y q‖ ≤ E := by
  intro q hq
  unfold bfStage
  split_ifs with hr
  · exact (hg _ _ _ (hy q hq) (hy _ (add_half_lt hH hHpos hq hr))).1
  · exact (hg _ _ _ (hy _ (by omega)) (hy q hq)).2

/-! ## Products -/

/-- **`ℓ²` error of a slotwise product.** If `T̂` is within `L` of `T` in `ℓ²`, `T` has `ℓ²`
norm at most `R`, and `F̂` is slotwise bounded by `MF` and within `eF` of `F`, then `T̂ · F̂` is
within `L · MF + R · eF` of `T · F` in `ℓ²`. -/
theorem sum_sq_mul_sub_le {n : ℕ} (T₁ T F₁ F : Fin n → ℂ) (L R MF eF : ℝ) (hL : 0 ≤ L)
    (hR : 0 ≤ R) (hMF : 0 ≤ MF) (heF : 0 ≤ eF)
    (hT : ∑ j, ‖T₁ j - T j‖ ^ 2 ≤ L ^ 2) (hTn : ∑ j, ‖T j‖ ^ 2 ≤ R ^ 2)
    (hF : ∀ j, ‖F₁ j‖ ≤ MF) (hFe : ∀ j, ‖F₁ j - F j‖ ≤ eF) :
    ∑ j, ‖T₁ j * F₁ j - T j * F j‖ ^ 2 ≤ (L * MF + R * eF) ^ 2 := by
  have hpt : ∀ j, ‖T₁ j * F₁ j - T j * F j‖ ^ 2 ≤ (MF * ‖T₁ j - T j‖ + eF * ‖T j‖) ^ 2 := by
    intro j
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have e : T₁ j * F₁ j - T j * F j = (T₁ j - T j) * F₁ j + T j * (F₁ j - F j) := by ring
    rw [e]
    calc _ ≤ ‖(T₁ j - T j) * F₁ j‖ + ‖T j * (F₁ j - F j)‖ := norm_add_le _ _
      _ ≤ ‖T₁ j - T j‖ * MF + ‖T j‖ * eF := by
          rw [norm_mul, norm_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (hF j) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hFe j) (norm_nonneg _))
      _ = MF * ‖T₁ j - T j‖ + eF * ‖T j‖ := by ring
  have expand : ∑ j, (MF * ‖T₁ j - T j‖ + eF * ‖T j‖) ^ 2 =
      MF ^ 2 * ∑ j, ‖T₁ j - T j‖ ^ 2 + 2 * MF * eF * ∑ j, ‖T₁ j - T j‖ * ‖T j‖ +
        eF ^ 2 * ∑ j, ‖T j‖ ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcs : (∑ j, ‖T₁ j - T j‖ * ‖T j‖) ^ 2 ≤
      (∑ j, ‖T₁ j - T j‖ ^ 2) * ∑ j, ‖T j‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hab : ∑ j, ‖T₁ j - T j‖ * ‖T j‖ ≤ L * R := by
    have h1 : (∑ j, ‖T₁ j - T j‖ * ‖T j‖) ^ 2 ≤ (L * R) ^ 2 := by
      rw [mul_pow]
      exact hcs.trans (mul_le_mul hT hTn (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (sq_nonneg _))
    nlinarith [mul_nonneg hL hR]
  have hMe : 0 ≤ 2 * MF * eF := mul_nonneg (mul_nonneg zero_le_two hMF) heF
  calc _ ≤ ∑ j, (MF * ‖T₁ j - T j‖ + eF * ‖T j‖) ^ 2 := Finset.sum_le_sum fun j _ => hpt j
    _ = _ := expand
    _ ≤ MF ^ 2 * L ^ 2 + 2 * MF * eF * (L * R) + eF ^ 2 * R ^ 2 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hT (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hab hMe)) (mul_le_mul_of_nonneg_left hTn (sq_nonneg _))
    _ = (L * MF + R * eF) ^ 2 := by ring

end FFTStages

end Falcon

end
