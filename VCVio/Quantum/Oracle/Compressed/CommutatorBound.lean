/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.MatrixMap.OpNorm
public import VCVio.Quantum.MatrixMap.Pinching
public import VCVio.Quantum.Oracle.Compressed.Instability
public import VCVio.Quantum.Oracle.Compressed.Phase


/-!
# Lemmas 5.9 and 5.10 for the truncated compressed oracle

Let `π` label the databases, so that `P^(i)` is the projector onto the databases of label `i`,
and let `I = I(π, t)` be the instability of `π` with query bound `t`
(`Quantum.Database.instability`, Definition 5.3 of A. Chiesa, Z. Di, Z. Hu and Y. Zheng, *How to
Prove Post-Quantum Security for Succinct Non-Interactive Reductions*, ePrint 2025/2166, cited as
[CDHZ] below). This file proves, for the truncated compressed oracle `O^(t)`:

* **Lemma 5.9 with the constant `8`**
  (`Quantum.l2_opNorm_pinch_truncatedOracle_sub_sq_le_eight_mul`):
  `‖∑ i, P^(i) O^(t) P^(i) - O^(t)‖² ≤ 8 I`, with the phase-basis form
  `Quantum.l2_opNorm_pinch_truncatedPhaseOracle_sub_sq_le_eight_mul`. The statements with the
  paper's constant `20`, `Quantum.l2_opNorm_pinch_truncatedOracle_sub_sq_le` and
  `Quantum.l2_opNorm_pinch_truncatedPhaseOracle_sub_sq_le`, are corollaries.
* **Lemma 5.10** (`Quantum.l2_opNorm_commutator_truncatedOracle_le_pinch`, after A. Chiesa,
  P. Manohar and N. Spooner, *Succinct Arguments in the Quantum Random Oracle Model*, TCC 2019,
  Lemma 5.10, cited as [CMS19]): for a label-controlled unitary `V = ∑ i, P^(i) W_i` whose
  `W_i` preserve the labels and commute with `O^(t) ⊗ 1`,
  `‖[V, O^(t) ⊗ 1]‖ ≤ 2 ‖∑ i, P^(i) O^(t) P^(i) - O^(t)‖`.

`∑ i, P^(i) A P^(i)` is the pinching `Matrix.pinch β A` of `A` by the labelling
`β ((x, y), D) = π D` (`Matrix.pinch_eq_sum`).

## Comparison with [CDHZ]

* [CDHZ] prove Lemma 5.9 with the constant `20`; this file proves `8`. The constant `8` is
  optimal. This optimality is not formalized; the argument is as follows. Take `X` a point,
  `t = 1`, `Y = Fin s → ZMod 2` with `N = 2 ^ s`, a nonzero character `χ`, and `m` contents `u`
  with `χ u = -1`, each its own label, every other content (and `⊥`) in the label of `⊥`. Then
  `I = b = m / N`. Work with `E = O_ph^(t) - pinch O_ph^(t) = -Δ` in the block of the empty
  database. Let `e₁` be the uniform unit vector on these `m` contents and `e₀` the normalized
  component of `E e₁` in the label of `⊥`. In the basis `(e₀, e₁)` (up to the sign of `e₀`), `E`
  restricted to their span is `[[0, √(6b - 9b²)], [√(6b - 9b²), 3 (m - 1) / N]]`, and `E` is
  `-3 / N` or `0` on the complement. With `m` the nearest integer to `2N / 9` and `s → ∞`,
  `b → 2 / 9` and the largest eigenvalue of `E` tends to `4 / 3`, so
  `‖Δ‖² / I = ‖E‖² / I → (4 / 3)² / (2 / 9) = 8`.
* For labellings with at most two values the pinching constant is `6`, the constant of [CMS19,
  Lemma 5.10], here with a proof that also covers databases of size exactly `t`
  (`VCVio.Quantum.Oracle.Compressed.BinaryPartition`).
* [CDHZ] prove Theorem 5.4 as `4 × 20 = 80` through Lemmas 5.9 and 5.10. With the constant `8`,
  Lemma 5.10 gives only `32`. The optimal constant `24` needs a label-preserving approximation that
  is closer than the pinching; Theorem 5.4 and Corollary 5.6 are therefore stated in
  `VCVio.Quantum.Oracle.Compressed.CommutatorSharp`, with `24` and the paper's `80` as a
  corollary.

## Proof of Lemma 5.9

By equation (4) the standard and phase forms have the same norm, and in the phase basis the
operator `Δ = pinch O_ph^(t) - O_ph^(t)` is block diagonal: its entry at `((x', χ'), D')`,
`((x, χ), D)` vanishes unless `(x', χ') = (x, χ)` and `D'`, `D` agree off `x`
(`Quantum.l2_opNorm_le_of_queryBlock`). A block is therefore given by `(x, χ)` and a database `r`
with `r x = ⊥`, and is indexed by the content `a` of the cell `x`. When `|r| < t` the truncation
keeps the whole block, and the entries of the block of `Δ` are `-[π r[x ↦ a'] ≠ π r[x ↦ a]] C a' a`,
with `C = Quantum.phaseCell Y χ`. When `|r| ≥ t` every filled content `r[x ↦ u]` has more than
`t` entries, so of the block of `O_ph^(t)` at most the empty-to-empty entry survives, which
pinching keeps.

The block of `Δ` vanishes on the contents `a` with `π r[x ↦ a] = π r`, a set containing `⊥`. Every
other row is the row of a filled content `u` in `B = {u | π r[x ↦ u] ≠ π r}`. Off the diagonal its
squared entries sum to at most `6 / N` (`Quantum.sum_ite_norm_phaseCell_sq_le`): Lemma 4.5 gives
`1 / N` at `⊥` and `|1 - χ u - χ v|² / N²` at `v`, and `∑ v, |1 - χ u - χ v|² ≤ 5 N` because `χ`
sums to zero. The phase cell is symmetric, so the same holds for the columns. Outside the vanishing
corner the rows and the columns thus carry squared entries summing to at most `6 |B| / N ≤ 6 I`,
and the two-by-two corner bound `Matrix.l2_opNorm_sq_le_of_corner_eq_zero` gives
`‖Δ‖² ≤ (4 / 3) · 6 I = 8 I`. [CDHZ] bound the block by its Frobenius norm, which gives `20`.

The decomposition in the proof of [CDHZ, Lemma 5.9] treats inputs with `|D| = t` as acquiring
only a phase. For a filled queried cell and `χ ≠ 0`, `O_ph^(t)` also produces the `t − 1` and
resized terms of Lemma 4.5, since every database it reaches has at most `t` entries (for example
`X = Unit`, `Y = ZMod 2`, `t = 1`). The proof here uses the block decomposition above instead, and
the statement of the lemma holds as stated.

The statements involving the instability take `X Y : Type`, as VCVio's query caches do; the other
statements are universe polymorphic.
-/

public section

open Matrix
open OracleSpec
open scoped Matrix.Norms.L2Operator Kronecker

namespace Quantum

/-! ## Databases that differ in one cell -/

namespace Database

variable {X Y : Type*} [DecidableEq X]

theorem update_none_of_eq_none {r : Database X Y} {x : X} (hr : r x = none) :
    Function.update r x none = r := by
  rw [← hr]
  exact Function.update_eq_self x r

variable [Fintype X]

/-- Filling an empty cell adds one to the size. -/
theorem size_update_some_of_eq_none {r : Database X Y} {x : X} (hr : r x = none) (u : Y) :
    size (Function.update r x (some u)) = r.size + 1 := by
  rw [size, size, ← Finset.card_insert_of_notMem (s := Finset.univ.filter fun j ↦ (r j).isSome)
    (a := x) (by simp [hr])]
  congr 1
  ext j
  by_cases h : j = x
  · subst h
    simp
  · simp [h]

/-- The databases that agree with `r` off an empty cell `x` of `r` are the databases `r[x ↦ a]`. -/
theorem sum_ite_update_none_eq [Fintype Y] [DecidableEq Y] {M : Type*} [AddCommMonoid M]
    {r : Database X Y} {x : X} (hr : r x = none) (g : Database X Y → M) :
    ∑ D, (if Function.update D x none = r then g D else 0) = ∑ a, g (Function.update r x a) := by
  rw [← Finset.sum_filter]
  have himg : Finset.univ.filter (fun D : Database X Y ↦ Function.update D x none = r) =
      Finset.univ.image (Function.update r x) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro rfl
      exact ⟨D x, by simp⟩
    · rintro ⟨a, rfl⟩
      rw [Function.update_idem, update_none_of_eq_none hr]
  rw [himg, Finset.sum_image]
  intro a _ b _ h
  simpa using congrFun h x

end Database

/-! ## The rows of the phase cell -/

section cell

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

omit [DecidableEq Y] [AddCommGroup Y] in
/-- The squared amplitude of the uniform superposition over `Y` is `1 / |Y|`. -/
theorem norm_cellAmp_sq : ‖cellAmp Y‖ ^ 2 = (Fintype.card Y : ℝ)⁻¹ := by
  rw [sq, ← norm_mul, cellAmp_mul_self, norm_inv, Complex.norm_natCast]

omit [AddCommGroup Y] in
/-- The one-cell compression is symmetric. -/
theorem cellCompress_apply_comm (a' a : Option Y) : cellCompress Y a' a = cellCompress Y a a' := by
  rcases a' with _ | y <;> rcases a with _ | y' <;> simp [eq_comm]

/-- The phase cell is symmetric. -/
theorem phaseCell_apply_comm (χ : AddChar Y ℂ) (a' a : Option Y) :
    phaseCell Y χ a' a = phaseCell Y χ a a' := by
  rw [phaseCell_apply, phaseCell_apply]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [cellCompress_apply_comm a' b, cellCompress_apply_comm b a]
  ring

/-- **The rows of the phase cell.** Off the diagonal, the squared entries of the row of a filled
content `u` sum to at most `6 / N`: by Lemma 4.5 of ePrint 2025/2166 they are `1 / N` at `⊥` and
`|1 - χ u - χ v|² / N²` at `v ≠ u`, and since a nontrivial character sums to zero,
`∑ v, |1 - χ u - χ v|² = N (|1 - χ u|² + 1) ≤ 5 N`. -/
theorem sum_ite_norm_phaseCell_sq_le (χ : AddChar Y ℂ) (u : Y) :
    ∑ a, (if some u = a then 0 else ‖phaseCell Y χ (some u) a‖ ^ 2) ≤
      6 / Fintype.card Y := by
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Fintype.card Y := ⟨_, rfl⟩
  have hN : 0 < N := hNdef ▸ Nat.cast_pos.mpr Fintype.card_pos
  rw [← hNdef]
  by_cases hχ : χ = 0
  · have h0 : ∀ a, (if some u = a then 0 else ‖phaseCell Y χ (some u) a‖ ^ 2) = 0 := by
      intro a
      by_cases h : some u = a
      · simp [h]
      · rw [hχ, phaseCell_zero, one_apply_ne h]
        simp
    simp only [h0, Finset.sum_const_zero]
    positivity
  have hs := sum_apply_eq_zero_of_ne_zero hχ
  set c : ℂ := 1 - χ u with hc
  have hterm : ∀ v, (if some u = some v then 0 else ‖phaseCell Y χ (some u) (some v)‖ ^ 2) ≤
      N⁻¹ ^ 2 * (‖c‖ ^ 2 + 1 - 2 * (c * starRingEnd ℂ (χ v)).re) := by
    intro v
    have heq : ‖(Fintype.card Y : ℂ)⁻¹ * (c - χ v)‖ ^ 2 =
        N⁻¹ ^ 2 * (‖c‖ ^ 2 + 1 - 2 * (c * starRingEnd ℂ (χ v)).re) := by
      rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast, ← hNdef, Complex.sq_norm (c - χ v),
        Complex.normSq_sub, ← Complex.sq_norm, ← Complex.sq_norm (χ v), AddChar.norm_apply,
        one_pow]
    split_ifs with h
    · exact heq ▸ sq_nonneg _
    · have huv : u ≠ v := fun huv ↦ h (huv ▸ rfl)
      rw [phaseCell_some_some hχ, ite_eq_right huv, zero_add, ← heq, hc]
  have hsum : ∑ v, N⁻¹ ^ 2 * (‖c‖ ^ 2 + 1 - 2 * (c * starRingEnd ℂ (χ v)).re) =
      N⁻¹ * (‖c‖ ^ 2 + 1) := by
    have hre : ∑ v, (c * starRingEnd ℂ (χ v)).re = 0 := by
      rw [← Complex.re_sum, ← Finset.mul_sum, ← map_sum, hs, map_zero, mul_zero, Complex.zero_re]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hre, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← hNdef]
    field_simp
    ring
  have hc2 : ‖c‖ ≤ 2 := by
    calc ‖c‖ ≤ ‖(1 : ℂ)‖ + ‖χ u‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, AddChar.norm_apply]; norm_num
  have hamp : ‖phaseCell Y χ (some u) none‖ ^ 2 = N⁻¹ := by
    rw [phaseCell_some_none hχ, norm_mul, AddChar.norm_apply, mul_one, norm_cellAmp_sq, hNdef]
  rw [Fintype.sum_option, ite_eq_right (Option.some_ne_none u), hamp]
  calc N⁻¹ + ∑ v, (if some u = some v then 0 else ‖phaseCell Y χ (some u) (some v)‖ ^ 2)
      ≤ N⁻¹ + N⁻¹ * (‖c‖ ^ 2 + 1) := by
        rw [← hsum]
        exact add_le_add le_rfl (Finset.sum_le_sum fun v _ ↦ hterm v)
    _ ≤ N⁻¹ + N⁻¹ * (2 ^ 2 + 1) := by gcongr
    _ = 6 / N := by field_simp; ring

end cell

/-! ## Blocks of a query register and a database -/

section queryBlock

variable {X Y Q : Type*} [DecidableEq X]

/-- The block of a basis state `(q, D)` of a query register and a database: the query `q` and the
database `D` with the queried cell `q.1` emptied. The truncated phase oracle keeps every block
(`Quantum.phaseBlock_eq_of_truncatedPhaseOracle_ne_zero`). -/
@[expose]
def queryBlock (m : (X × Q) × Database X Y) : (X × Q) × Database X Y :=
  (m.1, Function.update m.2 m.1.1 none)

/-- The basis states in the block of `(q, r)`, for `r` empty at the queried cell, are the states
`(q, r[q.1 ↦ a])`, one for each content `a` of the cell. -/
@[expose]
def queryBlockEquiv (q : X × Q) {r : Database X Y} (hr : r q.1 = none) :
    Option Y ≃ {m : (X × Q) × Database X Y // queryBlock m = (q, r)} where
  toFun a := ⟨(q, Function.update r q.1 a), by
    simp only [queryBlock, Function.update_idem, Database.update_none_of_eq_none hr]⟩
  invFun m := m.1.2 q.1
  left_inv a := by simp
  right_inv := by
    rintro ⟨⟨q', D⟩, h⟩
    simp only [queryBlock, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Subtype.ext (Prod.ext rfl (by simp [Function.update_idem]))

@[simp]
theorem coe_queryBlockEquiv (q : X × Q) {r : Database X Y} (hr : r q.1 = none) (a : Option Y) :
    (queryBlockEquiv q hr a : (X × Q) × Database X Y) = (q, Function.update r q.1 a) :=
  rfl

/-- A block whose database is filled at the queried cell is empty. -/
theorem isEmpty_queryBlock {q : X × Q} {r : Database X Y} (hr : r q.1 ≠ none) :
    IsEmpty {m : (X × Q) × Database X Y // queryBlock m = (q, r)} := by
  refine ⟨fun ⟨m, hm⟩ ↦ hr ?_⟩
  have h := congrArg (fun k : (X × Q) × Database X Y ↦ k.2 k.1.1) hm
  simpa [queryBlock] using h.symm

variable [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Q] [DecidableEq Q]
  {𝕜 : Type*} [RCLike 𝕜]

/-- The restriction of a matrix to the block of `(q, r)` has the norm of the matrix indexed by
the contents of the queried cell. -/
theorem l2_opNorm_submatrix_queryBlock
    (A : Matrix ((X × Q) × Database X Y) ((X × Q) × Database X Y) 𝕜) (q : X × Q)
    {r : Database X Y} (hr : r q.1 = none) :
    ‖A.submatrix (Subtype.val : {m // queryBlock m = (q, r)} → (X × Q) × Database X Y)
        (Subtype.val : {m // queryBlock m = (q, r)} → (X × Q) × Database X Y)‖ =
      ‖of fun a' a : Option Y ↦ A (q, Function.update r q.1 a') (q, Function.update r q.1 a)‖ := by
  rw [← l2_opNorm_submatrix_equiv (A.submatrix Subtype.val Subtype.val) (queryBlockEquiv q hr)
    (queryBlockEquiv q hr)]
  rfl

/-- **Block reduction.** A matrix that keeps every block of the query register and the database
has norm at most `c` as soon as every block, as a matrix indexed by the contents of the queried
cell, has norm at most `c`. -/
theorem l2_opNorm_le_of_queryBlock
    {A : Matrix ((X × Q) × Database X Y) ((X × Q) × Database X Y) 𝕜}
    (hA : ∀ m' m, A m' m ≠ 0 → queryBlock m' = queryBlock m) {c : ℝ} (hc : 0 ≤ c)
    (hblock : ∀ (q : X × Q) (r : Database X Y), r q.1 = none →
      ‖of fun a' a : Option Y ↦ A (q, Function.update r q.1 a') (q, Function.update r q.1 a)‖ ≤
        c) :
    ‖A‖ ≤ c := by
  refine l2_opNorm_le_of_submatrix_le queryBlock queryBlock hA hc fun ⟨q, r⟩ ↦ ?_
  by_cases hr : r q.1 = none
  · rw [l2_opNorm_submatrix_queryBlock A q hr]
    exact hblock q r hr
  · have := isEmpty_queryBlock (Y := Y) hr
    have h0 : A.submatrix (Subtype.val : {m // queryBlock m = (q, r)} → (X × Q) × Database X Y)
        (Subtype.val : {m // queryBlock m = (q, r)} → (X × Q) × Database X Y) = 0 := by
      ext i
      exact isEmptyElim i
    rw [h0, norm_zero]
    exact hc

end queryBlock

/-! ## The blocks of the truncated phase oracle -/

section phaseBlock

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Summing over the databases of a block of the phase basis: the basis states
`((x', χ'), D')` with `(x', χ') = (x, χ)` and `D'[x ↦ ⊥] = r` are the states
`((x, χ), r[x ↦ a])`. -/
theorem sum_ite_phaseBlock {M : Type*} [AddCommMonoid M] (x : X) (χ : AddChar Y ℂ)
    {r : Database X Y} (hr : r x = none) (g : (X × AddChar Y ℂ) × Database X Y → M) :
    ∑ m : (X × AddChar Y ℂ) × Database X Y,
      (if (m.1, Function.update m.2 m.1.1 none) = ((x, χ), r) then g m else 0) =
      ∑ a, g ((x, χ), Function.update r x a) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (x, χ)]
  · simp only [Prod.mk.injEq, true_and]
    exact Database.sum_ite_update_none_eq hr _
  · intro q _ hq
    exact Finset.sum_eq_zero fun D _ ↦ by simp [hq]
  · simp

/-- The truncated phase oracle keeps the query register and every cell but the queried one. -/
theorem phaseBlock_eq_of_truncatedPhaseOracle_ne_zero {t : ℕ}
    {m' m : (X × AddChar Y ℂ) × Database X Y} (h : truncatedPhaseOracle X Y t m' m ≠ 0) :
    (m'.1, Function.update m'.2 m'.1.1 none) = (m.1, Function.update m.2 m.1.1 none) := by
  obtain ⟨⟨x', χ'⟩, D'⟩ := m'
  obtain ⟨⟨x, χ⟩, D⟩ := m
  rw [truncatedPhaseOracle_apply, phaseOracle_apply] at h
  by_cases hc : (x', χ') = (x, χ) ∧ ∀ j ≠ x, D' j = D j
  · obtain ⟨hq, hj⟩ := hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
    simp only [Prod.mk.injEq, true_and]
    funext j
    by_cases hjx : j = x'
    · subst hjx
      simp
    · simp [Function.update_of_ne hjx, hj j hjx]
  · simp only [hc, ↓reduceIte, mul_zero, zero_mul, ne_eq, not_true_eq_false] at h


/-- The truncated phase oracle is symmetric. -/
theorem truncatedPhaseOracle_apply_comm (t : ℕ) (m' m : (X × AddChar Y ℂ) × Database X Y) :
    truncatedPhaseOracle X Y t m' m = truncatedPhaseOracle X Y t m m' := by
  obtain ⟨⟨x', χ'⟩, D'⟩ := m'
  obtain ⟨⟨x, χ⟩, D⟩ := m
  rw [truncatedPhaseOracle_apply, truncatedPhaseOracle_apply, phaseOracle_apply,
    phaseOracle_apply]
  by_cases hc : (x', χ') = (x, χ) ∧ ∀ j ≠ x, D' j = D j
  · have hc' : (x, χ) = (x', χ') ∧ ∀ j ≠ x', D j = D' j := by
      obtain ⟨hq, hj⟩ := hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      exact ⟨rfl, fun j h ↦ (hj j h).symm⟩
    rw [ite_eq_left hc, ite_eq_left hc']
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc.1
    rw [phaseCell_apply_comm]
    ring
  · have hc' : ¬ ((x, χ) = (x', χ') ∧ ∀ j ≠ x', D j = D' j) := by
      rintro ⟨hq, hj⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      exact hc ⟨rfl, fun j h ↦ (hj j h).symm⟩
    rw [ite_eq_right hc, ite_eq_right hc']
    ring

/-- The entries of the truncated phase oracle inside the block of `((x, χ), r)`: the phase cell,
kept when both databases have at most `t` nonempty cells. -/
theorem truncatedPhaseOracle_apply_update (t : ℕ) (x : X) (χ : AddChar Y ℂ) (r : Database X Y)
    (a' a : Option Y) :
    truncatedPhaseOracle X Y t ((x, χ), Function.update r x a') ((x, χ), Function.update r x a) =
      (if Database.size (Function.update r x a') ≤ t then 1 else 0) * phaseCell Y χ a' a *
        (if Database.size (Function.update r x a) ≤ t then 1 else 0) := by
  have hcond : (x, χ) = (x, χ) ∧ ∀ j ≠ x, Function.update r x a' j = Function.update r x a j :=
    ⟨rfl, fun j hj ↦ by rw [Function.update_of_ne hj, Function.update_of_ne hj]⟩
  rw [truncatedPhaseOracle_apply, phaseOracle_apply, ite_eq_left hcond, Function.update_self,
    Function.update_self]

/-- **The rows of a block of the truncated phase oracle.** Off the diagonal, the squared entries
of the row of a filled content `u` in the block of `((x, χ), r)` sum to at most `6 / N` when
`|r| < t`, and vanish when `|r| ≥ t`. -/
theorem sum_ite_norm_truncatedPhaseOracle_row_sq_le (t : ℕ) (x : X) (χ : AddChar Y ℂ)
    {r : Database X Y} (hr : r x = none) (u : Y) :
    ∑ a, (if some u = a then 0 else ‖truncatedPhaseOracle X Y t
        ((x, χ), Function.update r x (some u)) ((x, χ), Function.update r x a)‖ ^ 2) ≤
      if Database.size r < t then (6 / Fintype.card Y : ℝ) else 0 := by
  simp only [truncatedPhaseOracle_apply_update]
  by_cases hs : Database.size r < t
  · have hmask : ∀ a, Database.size (Function.update r x a) ≤ t := fun a ↦
      (Database.size_update_le r x a).trans hs
    simp only [hmask, ↓reduceIte, one_mul, mul_one, hs]
    exact sum_ite_norm_phaseCell_sq_le χ u
  · have hbig : ¬ Database.size (Function.update r x (some u)) ≤ t := by
      rw [Database.size_update_some_of_eq_none hr]
      omega
    simp [hbig, hs]

/-- **The columns of a block of the truncated phase oracle**, by symmetry: off the diagonal, the
squared entries of the column of a filled content `u` in the block of `((x, χ), r)` sum to at most
`6 / N` when `|r| < t`, and vanish when `|r| ≥ t`. -/
theorem sum_ite_norm_truncatedPhaseOracle_col_sq_le (t : ℕ) (x : X) (χ : AddChar Y ℂ)
    {r : Database X Y} (hr : r x = none) (u : Y) :
    ∑ a, (if a = some u then 0 else ‖truncatedPhaseOracle X Y t
        ((x, χ), Function.update r x a) ((x, χ), Function.update r x (some u))‖ ^ 2) ≤
      if Database.size r < t then (6 / Fintype.card Y : ℝ) else 0 := by
  refine le_of_eq_of_le (Finset.sum_congr rfl fun a _ ↦ ?_)
    (sum_ite_norm_truncatedPhaseOracle_row_sq_le t x χ hr u)
  by_cases h : a = some u
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), truncatedPhaseOracle_apply_comm]

end phaseBlock

/-! ## From the phase basis to the standard basis -/

section basis

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {ι : Type*} [DecidableEq ι]

/-- By equation (4) of ePrint 2025/2166, pinching the truncated standard oracle by the labels of
the databases moves it by at most as much as pinching the truncated phase oracle. -/
theorem l2_opNorm_pinch_truncatedOracle_sub_le (π : Database X Y → ι) (t : ℕ) :
    ‖pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) -
        truncatedOracle X Y t‖ ≤
      ‖pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) (truncatedPhaseOracle X Y t) -
        truncatedPhaseOracle X Y t‖ := by
  have hU : ∀ a b, (queryFourier X Y)ᴴ a b ≠ 0 →
      (fun m : (X × Y) × Database X Y ↦ π m.2) a =
        (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) b := by
    rintro ⟨⟨x, y⟩, D⟩ ⟨⟨x', χ⟩, D'⟩ h
    rw [conjTranspose_apply, queryFourier_apply] at h
    by_cases hc : x' = x ∧ D' = D
    · simp [hc.2]
    · simp only [hc, ↓reduceIte, star_zero, ne_eq, not_true_eq_false] at h
  have e := mul_pinch_mul_conjTranspose (fun m : (X × Y) × Database X Y ↦ π m.2)
    (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) hU (truncatedPhaseOracle X Y t)
  rw [conjTranspose_conjTranspose] at e
  rw [truncatedOracle_eq, ← e, ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact l2_opNorm_conjTranspose_mul_mul_le (queryFourier_mul_conjTranspose X Y) _

end basis

/-! ## Lemma 5.9 -/

section lemma59

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [UniformAnswerMeasure (X →ₒ Y)] {ι : Type*} [DecidableEq ι]

omit [DecidableEq Y] [AddCommGroup Y] in
/-- Summing the bound `c / N` over the answers `u` that change the label of `r[x ↦ u]` gives at
most `c I(π, t)` when `|r| < t`; the bound `0` is summed when `|r| ≥ t`. -/
theorem sum_ite_le_mul_instability (π : Database X Y → ι) (t : ℕ) {r : Database X Y} {x : X}
    (hr : r x = none) {c : ℝ} (hc : 0 ≤ c) :
    ∑ u : Y, (if π (Function.update r x (some u)) = π r then 0 else
      if Database.size r < t then c / Fintype.card Y else 0) ≤
        c * (Database.instability π t).toReal := by
  have hI : 0 ≤ (Database.instability π t).toReal := ENNReal.toReal_nonneg
  by_cases hs : Database.size r < t
  · have h := Database.card_div_le_instability π hs hr
    simp only [ne_eq] at h
    simp only [hs, ↓reduceIte]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    calc ((Finset.univ.filter fun u ↦ ¬ π (Function.update r x (some u)) = π r).card : ℝ) *
          (c / Fintype.card Y) =
        c * (((Finset.univ.filter fun u ↦ ¬ π (Function.update r x (some u)) = π r).card : ℝ) /
          Fintype.card Y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h hc
  · simp only [hs, ↓reduceIte, ite_self, Finset.sum_const_zero]
    positivity

/-- **The rows of a block that change the label.** In the block of `((x, χ), r)` of the truncated
phase oracle, the rows of the contents `a` with `π r[x ↦ a] ≠ π r` carry, off the diagonal,
squared entries summing to at most `6 I(π, t)`. -/
theorem sum_ite_sum_norm_truncatedPhaseOracle_row_sq_le (π : Database X Y → ι) (t : ℕ) (x : X)
    (χ : AddChar Y ℂ) {r : Database X Y} (hr : r x = none) :
    ∑ a', (if π (Function.update r x a') = π r then 0 else
      ∑ a, (if a' = a then 0 else ‖truncatedPhaseOracle X Y t ((x, χ), Function.update r x a')
        ((x, χ), Function.update r x a)‖ ^ 2)) ≤ 6 * (Database.instability π t).toReal := by
  have hnone : π (Function.update r x none) = π r := by
    rw [Database.update_none_of_eq_none hr]
  refine le_trans ?_ (sum_ite_le_mul_instability π t hr (c := 6) (by norm_num))
  rw [Fintype.sum_option, ite_eq_left hnone, zero_add]
  refine Finset.sum_le_sum fun u _ ↦ ?_
  by_cases h : π (Function.update r x (some u)) = π r
  · simp only [h, ↓reduceIte, le_refl]
  · rw [ite_eq_right h, ite_eq_right h]
    exact sum_ite_norm_truncatedPhaseOracle_row_sq_le t x χ hr u

/-- **The columns of a block that change the label.** In the block of `((x, χ), r)` of the
truncated phase oracle, the columns of the contents `a` with `π r[x ↦ a] ≠ π r` carry, off the
diagonal, squared entries summing to at most `6 I(π, t)`. -/
theorem sum_ite_sum_norm_truncatedPhaseOracle_col_sq_le (π : Database X Y → ι) (t : ℕ) (x : X)
    (χ : AddChar Y ℂ) {r : Database X Y} (hr : r x = none) :
    ∑ a, (if π (Function.update r x a) = π r then 0 else
      ∑ a', (if a' = a then 0 else ‖truncatedPhaseOracle X Y t ((x, χ), Function.update r x a')
        ((x, χ), Function.update r x a)‖ ^ 2)) ≤ 6 * (Database.instability π t).toReal := by
  have hnone : π (Function.update r x none) = π r := by
    rw [Database.update_none_of_eq_none hr]
  refine le_trans ?_ (sum_ite_le_mul_instability π t hr (c := 6) (by norm_num))
  rw [Fintype.sum_option, ite_eq_left hnone, zero_add]
  refine Finset.sum_le_sum fun u _ ↦ ?_
  by_cases h : π (Function.update r x (some u)) = π r
  · simp only [h, ↓reduceIte, le_refl]
  · rw [ite_eq_right h, ite_eq_right h]
    exact sum_ite_norm_truncatedPhaseOracle_col_sq_le t x χ hr u

/-- **Lemma 5.9 of ePrint 2025/2166 with the constant `8`, phase basis.** Pinching the truncated
phase oracle by the labels of the databases moves it by at most `√(8 I)` in operator norm. -/
theorem l2_opNorm_pinch_truncatedPhaseOracle_sub_sq_le_eight_mul (π : Database X Y → ι) (t : ℕ) :
    ‖pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) (truncatedPhaseOracle X Y t) -
        truncatedPhaseOracle X Y t‖ ^ 2 ≤ 8 * (Database.instability π t).toReal := by
  have hI : 0 ≤ (Database.instability π t).toReal := ENNReal.toReal_nonneg
  set Δ := pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2)
    (truncatedPhaseOracle X Y t) - truncatedPhaseOracle X Y t with hΔdef
  have hΔ : ∀ m' m, Δ m' m = if π m'.2 = π m.2 then 0 else -truncatedPhaseOracle X Y t m' m := by
    intro m' m
    rw [hΔdef, Matrix.sub_apply, pinch_apply]
    split_ifs <;> simp
  suffices key : ‖Δ‖ ≤ √(8 * (Database.instability π t).toReal) by
    calc ‖Δ‖ ^ 2 ≤ √(8 * (Database.instability π t).toReal) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) key 2
      _ = 8 * (Database.instability π t).toReal := Real.sq_sqrt (by positivity)
  refine l2_opNorm_le_of_queryBlock (fun m' m h ↦ phaseBlock_eq_of_truncatedPhaseOracle_ne_zero
    fun h0 ↦ h (by rw [hΔ, h0]; simp)) (Real.sqrt_nonneg _) ?_
  rintro ⟨x, χ⟩ r hr
  change r x = none at hr
  change ‖of fun a' a : Option Y ↦ Δ ((x, χ), Function.update r x a')
    ((x, χ), Function.update r x a)‖ ≤ _
  have hle : ∀ a' a, ‖Δ ((x, χ), Function.update r x a') ((x, χ), Function.update r x a)‖ ^ 2 ≤
      if a' = a then 0 else ‖truncatedPhaseOracle X Y t ((x, χ), Function.update r x a')
        ((x, χ), Function.update r x a)‖ ^ 2 := by
    intro a' a
    rw [hΔ]
    by_cases h : a' = a
    · subst h
      simp
    · split_ifs <;> simp
  rw [← Real.sqrt_sq (norm_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  have hcorner := l2_opNorm_sq_le_of_corner_eq_zero
    (E := of fun a' a : Option Y ↦ Δ ((x, χ), Function.update r x a')
      ((x, χ), Function.update r x a))
    (fun a ↦ π (Function.update r x a) = π r) (fun a ↦ π (Function.update r x a) = π r)
    (fun a' a ha' ha ↦ by rw [of_apply, hΔ, ite_eq_left (ha'.trans ha.symm)])
    (c := 6 * (Database.instability π t).toReal)
    ((Finset.sum_le_sum fun a' _ ↦ ?_).trans
      (sum_ite_sum_norm_truncatedPhaseOracle_row_sq_le π t x χ hr))
    ((Finset.sum_le_sum fun a _ ↦ ?_).trans
      (sum_ite_sum_norm_truncatedPhaseOracle_col_sq_le π t x χ hr))
  · calc _ ≤ 4 / 3 * (6 * (Database.instability π t).toReal) := hcorner
      _ = 8 * (Database.instability π t).toReal := by ring
  · split_ifs
    · exact le_rfl
    · exact Finset.sum_le_sum fun a _ ↦ hle a' a
  · split_ifs
    · exact le_rfl
    · exact Finset.sum_le_sum fun a' _ ↦ hle a' a

/-- **Lemma 5.9 of ePrint 2025/2166 with the constant `8`.** Pinching the truncated compressed
oracle by the labels of the databases, `∑ i, P^(i) O^(t) P^(i)`, moves it by at most `√(8 I)` in
operator norm: `‖∑ i, P^(i) O^(t) P^(i) - O^(t)‖² ≤ 8 I(π, t)`. The constant `8` is optimal
(proved on paper). -/
theorem l2_opNorm_pinch_truncatedOracle_sub_sq_le_eight_mul (π : Database X Y → ι) (t : ℕ) :
    ‖pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) -
        truncatedOracle X Y t‖ ^ 2 ≤ 8 * (Database.instability π t).toReal :=
  (pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_pinch_truncatedOracle_sub_le π t) 2).trans
    (l2_opNorm_pinch_truncatedPhaseOracle_sub_sq_le_eight_mul π t)

/-- **Lemma 5.9 of ePrint 2025/2166, phase basis**, with the paper's constant `20`: a corollary of
`Quantum.l2_opNorm_pinch_truncatedPhaseOracle_sub_sq_le_eight_mul`. -/
theorem l2_opNorm_pinch_truncatedPhaseOracle_sub_sq_le (π : Database X Y → ι) (t : ℕ) :
    ‖pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) (truncatedPhaseOracle X Y t) -
        truncatedPhaseOracle X Y t‖ ^ 2 ≤ 20 * (Database.instability π t).toReal :=
  (l2_opNorm_pinch_truncatedPhaseOracle_sub_sq_le_eight_mul π t).trans
    (mul_le_mul_of_nonneg_right (by norm_num) ENNReal.toReal_nonneg)

/-- **Lemma 5.9 of ePrint 2025/2166**, with the paper's constant `20`:
`‖∑ i, P^(i) O^(t) P^(i) - O^(t)‖² ≤ 20 I(π, t)`. A corollary of
`Quantum.l2_opNorm_pinch_truncatedOracle_sub_sq_le_eight_mul`. -/
theorem l2_opNorm_pinch_truncatedOracle_sub_sq_le (π : Database X Y → ι) (t : ℕ) :
    ‖pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) -
        truncatedOracle X Y t‖ ^ 2 ≤ 20 * (Database.instability π t).toReal :=
  (l2_opNorm_pinch_truncatedOracle_sub_sq_le_eight_mul π t).trans
    (mul_le_mul_of_nonneg_right (by norm_num) ENNReal.toReal_nonneg)

end lemma59

/-! ## Lemma 5.10 -/

section lemma510

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {ι : Type*} {E : Type*} [Fintype E] [DecidableEq E]

/-- **Lemma 5.10 of ePrint 2025/2166** (after Chiesa, Manohar and Spooner, TCC 2019, Lemma 5.10).
Let `W i` be unitaries on the joint register `((X × Y) × Database X Y) × E` that preserve the
label `π D` of the database and commute with `O^(t) ⊗ 1_E`, and let `V = ∑ i, P^(i) W i` be the
label-controlled unitary. Then `‖[V, O^(t) ⊗ 1_E]‖ ≤ 2 ‖∑ i, P^(i) O^(t) P^(i) - O^(t)‖`. -/
theorem l2_opNorm_commutator_truncatedOracle_le_pinch [DecidableEq ι] (π : Database X Y → ι) (t : ℕ)
    {W : ι → Matrix (((X × Y) × Database X Y) × E) (((X × Y) × Database X Y) × E) ℂ}
    (hW : ∀ k a b, W k a b ≠ 0 → π a.1.2 = π b.1.2) (hU : ∀ k, W k ∈ unitaryGroup _ ℂ)
    (hA : ∀ k, W k * (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) =
      (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) * W k) :
    ‖labelControlled (fun a ↦ π a.1.2) W * (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) * labelControlled (fun a ↦ π a.1.2) W‖ ≤
      2 * ‖pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) -
        truncatedOracle X Y t‖ := by
  refine (l2_opNorm_commutator_labelControlled_le hW hU hA).trans ?_
  have hp := pinch_kronecker_one (p := E) (fun m : (X × Y) × Database X Y ↦ π m.2)
    (truncatedOracle X Y t)
  have hsub : pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) ⊗ₖ
      (1 : Matrix E E ℂ) - truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ) =
        (pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) -
          truncatedOracle X Y t) ⊗ₖ (1 : Matrix E E ℂ) := by
    ext a b
    simp only [Matrix.sub_apply, kroneckerMap_apply, sub_mul]
  rw [hp, hsub]
  gcongr
  exact l2_opNorm_kronecker_one_le _

end lemma510

end Quantum
