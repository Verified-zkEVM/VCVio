/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.MatrixMap.Commutant
public import VCVio.Quantum.MatrixMap.Completion
public import VCVio.Quantum.Oracle.Compressed.CommutatorBound

/-!
# Theorem 5.4 for the truncated compressed oracle, with the optimal constant `24`

Let `π` label the databases, let `I = I(π, t)` be the instability of `π` with query bound `t`
(`Quantum.Database.instability`, Definition 5.3 of [CDHZ]), and let `V = ∑ i, P^(i) W i` be a
label-controlled unitary whose `W i` preserve the labels and commute with the truncated compressed
oracle `O^(t) ⊗ 1_E`. This file proves

  `‖[V, O^(t) ⊗ 1_E]‖² ≤ 24 I(π, t)`
  (`Quantum.l2_opNorm_commutator_truncatedOracle_sq_le_twentyFour_mul`).

The `W i` act on the whole joint register `((X × Y) × Database X Y) × E`, not only on an ancilla,
and `π` is an arbitrary labelling. The purified measurement `V = ∑ i, P^(i) ⊗ U i` of
Corollary 5.6 and its XOR instance follow
(`Quantum.l2_opNorm_commutator_purifiedMeasurement_sq_le_twentyFour_mul`,
`Quantum.l2_opNorm_commutator_xorMeasurement_sq_le_twentyFour_mul`), and so do the statements with
the paper's constant `80` (`Quantum.l2_opNorm_commutator_truncatedOracle_sq_le`,
`Quantum.l2_opNorm_commutator_purifiedMeasurement_sq_le`,
`Quantum.l2_opNorm_commutator_xorMeasurement_sq_le`).

## Comparison with [CDHZ]

[CDHZ] prove Theorem 5.4 with the constant `80`, as `4 × 20`: Lemma 5.10 (after [CMS19,
Lemma 5.10]) bounds `‖[V, O]‖` by twice the distance from `O` to its pinching, and Lemma 5.9 bounds
that squared distance by `20 I`. The factor `2` cannot be improved, and the optimal pinching
constant is `8` (`Quantum.l2_opNorm_pinch_truncatedOracle_sub_sq_le_eight_mul`), which gives only
`32`. This file compares `O` with a closer label-preserving operator than its pinching:
`Matrix.l2_opNorm_commutator_labelControlled_le_of_pinch_eq` accepts any label-preserving `S`, and
here `S` comes from a matrix completion with `‖O - S‖² ≤ 6 I`
(`Quantum.exists_pinch_eq_truncatedOracle_sub_sq_le`). The resulting constant `24` is optimal
(see *Optimality* below).

| statement | [CDHZ] | here | optimality |
|---|---|---|---|
| Lemma 5.9 (pinching) | `20` | `8` | on paper only |
| pinching, two labels | — | `6` | follows from formalized bounds |
| Theorem 5.4, Corollary 5.6 | `80` | `24` | formalized |

All three upper bounds are formalized (`8` in `VCVio.Quantum.Oracle.Compressed.CommutatorBound`,
`6` in `VCVio.Quantum.Oracle.Compressed.BinaryPartition`, `24` here).

## Proof

Work in the phase basis, where `O_ph^(t) = H O^(t) H†` (`Quantum.truncatedOracle_eq`) is block
diagonal: a block is a query `(x, χ)` with a database `r` that is empty at `x`, and is indexed by
the content `a` of the cell `x`. Call a basis state `((x, χ), r[x ↦ some y])` **bad** if `χ ≠ 0`,
`|r| < t` and `π r[x ↦ y] ≠ π r`.

1. **Row identity.** Remove the phase `χ y` from the diagonal entry of a bad row. The row of the
   phase cell becomes `N^(-1/2) χ y` at `⊥` and `N⁻¹ (1 - χ y - χ w)` at `w`, of squared norm
   `(4 - 2 Re χ y) / N ≤ 6 / N` (`Quantum.sum_norm_phaseCell_sub_sq`). The column is the same,
   since the phase cell is symmetric. With `P` the projector onto the bad states and
   `M = O_ph^(t) - diag(χ (D x))`, the block bound on squared entries and the count of bad states
   per block, `|B| / N ≤ I`, give `‖P M‖ ≤ √(6 I)` and `‖M P‖ ≤ √(6 I)`.
2. **Completion.** Parrott's theorem (`Matrix.exists_completion`) gives `T` with `P T = P M`,
   `T P = M P` and `‖T‖ ≤ √(6 I)`.
3. **Localization.** Pinch `T` to the blocks with `χ ≠ 0` and `|r| < t`, each block its own label,
   and every other basis state its own label. Pinching is a contraction
   (`Matrix.l2_opNorm_pinch_le`). Then `S = O_ph^(t) - pinch T` preserves every label: on a bad
   row or column it is the diagonal phase, between good states of an active block both labels are
   `π r`, and on the other blocks `O_ph^(t)` is diagonal (the trivial character, or a block of
   size at least `t`, of which the truncation keeps only the entry from `r` to `r`).
4. **Unique minimum.** Conjugate back by `H` and tensor with `1_E`. Among the label-preserving
   operators at distance at most `‖O - S‖` from `O`, the one of least squared Frobenius norm is
   unique, so it is fixed by conjugation by every `W i`, and commutes with `V`
   (`Matrix.l2_opNorm_commutator_labelControlled_le_of_pinch_eq`). Then
   `‖[V, O]‖ ≤ 2 ‖O - S‖ ≤ 2 √(6 I)`.

As in `Quantum.l2_opNorm_pinch_truncatedOracle_sub_sq_le`, the blocks with `|r| ≥ t` are handled by
the decomposition itself, so filled cells of databases of size exactly `t` are covered.

## Optimality

The constant `24` cannot be lowered, already for the scalar control `V = P_A - P_B` of a labelling
with two values. Take a character `χ` and an answer `y₀` with `χ y₀ = -1`, a point `x₀`, and
`t ≥ 1`, and label a database by whether `D x₀ = y₀`. Then `I ≤ 1 / N`
(`Quantum.instability_decide_eq_some_le`), and the column of the bad state
`((x₀, χ), ∅[x₀ ↦ y₀])` in the phase basis gives `‖[V, O^(t)]‖² ≥ 24 / N - 36 / N²`
(`Quantum.le_l2_opNorm_commutator_truncatedOracle_sq`). Hence
`(24 - 36 / N) I ≤ ‖[V, O^(t)]‖²`
(`Quantum.mul_instability_le_l2_opNorm_commutator_truncatedOracle_sq`), and every constant
`c < 24` fails as soon as `(24 - c) N > 36`
(`Quantum.mul_instability_lt_l2_opNorm_commutator_truncatedOracle_sq`; for `c = 20` this means
`N ≥ 10`, `Quantum.twenty_mul_instability_lt_l2_opNorm_commutator_truncatedOracle_sq`). The bit
strings `Y = Fin (s + 1) → ZMod 2` have such a character for every `s`, with `N = 2 ^ (s + 1)`
(`Quantum.exists_addChar_eq_neg_one_bitString`), so every `c < 24` fails for some `Y`
(`Quantum.exists_mul_instability_lt_l2_opNorm_commutator_truncatedOracle_sq`). All of this is
formalized.

Not formalized: that the bounds above are equalities, `I = 1 / N` and, for `X` a point and
`t = 1`, `‖[V, O^(1)]‖² = 4 (6 / N - 9 / N²)`, so that the ratio is exactly `24 - 36 / N`. The
lower bound on the norm is the squared norm of one column of the commutator; the matching upper
bound needs the full spectral computation of the commutator on the block of the empty database.
Optimality does not depend on these equalities.

## Main results

* `Quantum.sum_norm_phaseCell_sub_sq`: the row identity.
* `Quantum.exists_pinch_eq_truncatedPhaseOracle_sub_sq_le`,
  `Quantum.exists_pinch_eq_truncatedOracle_sub_sq_le`: a label-preserving operator at squared
  distance at most `6 I` from the truncated oracle.
* `Quantum.l2_opNorm_commutator_truncatedPhaseOracle_sq_le_twentyFour_mul`,
  `Quantum.l2_opNorm_commutator_truncatedOracle_sq_le_twentyFour_mul`: Theorem 5.4 with `24`.
* `Quantum.l2_opNorm_commutator_purifiedMeasurement_sq_le_twentyFour_mul`,
  `Quantum.l2_opNorm_commutator_xorMeasurement_sq_le_twentyFour_mul`: Corollary 5.6 with `24`.
* `Quantum.mul_instability_le_l2_opNorm_commutator_truncatedOracle_sq`,
  `Quantum.exists_mul_instability_lt_l2_opNorm_commutator_truncatedOracle_sq`: optimality of `24`.

The statements involving the instability take `X Y : Type`, as VCVio's query caches do; the other
statements are universe polymorphic.

## References

* [CDHZ] A. Chiesa, Z. Di, Z. Hu and Y. Zheng, *How to Prove Post-Quantum Security for Succinct
  Non-Interactive Reductions*, ePrint 2025/2166, Lemmas 5.9–5.10, Theorem 5.4, Corollary 5.6.
* [CMS19] A. Chiesa, P. Manohar and N. Spooner, *Succinct Arguments in the Quantum Random Oracle
  Model*, TCC 2019, Lemma 5.10.
* [DFMS22] J. Don, S. Fehr, C. Majenz and C. Schaffner, *Online-Extractability in the Quantum
  Random-Oracle Model*, EUROCRYPT 2022, Theorem 3.1.
* S. Parrott, *On a quotient norm and the Sz.-Nagy–Foiaş lifting theorem*, J. Funct. Anal. 30
  (1978).
-/

public section

open Matrix
open OracleSpec
open scoped Matrix.Norms.L2Operator Kronecker ComplexConjugate

namespace Matrix

/-- Complete the rows and columns that change a label, then localize the completion to
invariant blocks. The resulting approximation preserves the labels. -/
theorem exists_pinch_eq_sub_sq_le_of_completion
    {n κ Λ : Type*} [Fintype n] [DecidableEq n] [DecidableEq κ]
    (β : n → κ) (γ : n → Λ) (bad : n → Prop) [DecidablePred bad]
    (A : Matrix n n ℂ) (d : n → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hrow : ‖diagonal (fun i ↦ if bad i then (1 : ℂ) else 0) * (A - diagonal d)‖ ≤ √c)
    (hcol : ‖(A - diagonal d) * diagonal (fun i ↦ if bad i then (1 : ℂ) else 0)‖ ≤ √c)
    (hblock : ∀ i j, A i j ≠ 0 → i ≠ j → γ i = γ j)
    (hgood : ∀ i j, γ i = γ j → i ≠ j → ¬bad i → ¬bad j → β i = β j) :
    ∃ S, pinch β S = S ∧ ‖A - S‖ ^ 2 ≤ c := by
  classical
  let P : Matrix n n ℂ := diagonal (fun i ↦ if bad i then 1 else 0)
  have hP : IsStarProjection P := by
    refine ⟨?_, ?_⟩
    · dsimp [P]
      rw [IsIdempotentElem, diagonal_mul_diagonal]
      congr 1
      funext i
      split_ifs <;> simp
    · dsimp only [P]
      rw [IsSelfAdjoint, star_eq_conjTranspose, diagonal_conjTranspose]
      congr 1
      funext i
      split_ifs <;> simp_all
  obtain ⟨T, hPT, hTP, hT⟩ := exists_completion hP hrow hcol
  have hr : ∀ i j, bad i → T i j = (A - diagonal d) i j := by
    intro i j hi
    have h := congrFun (congrFun hPT i) j
    simpa [P, diagonal_mul, hi] using h
  have hl : ∀ i j, bad j → T i j = (A - diagonal d) i j := by
    intro i j hj
    have h := congrFun (congrFun hTP i) j
    simpa [P, mul_diagonal, hj] using h
  refine ⟨A - pinch γ T, ?_, ?_⟩
  · rw [pinch_eq_self_iff]
    intro i j hij
    by_cases he : i = j
    · simp [he]
    rw [Matrix.sub_apply, pinch_apply] at hij
    by_cases hg : γ i = γ j
    · rw [ite_eq_left hg] at hij
      have hi : ¬bad i := by
        intro hi
        simp [hr i j hi, Matrix.sub_apply, diagonal_apply_ne _ he] at hij
      have hj : ¬bad j := by
        intro hj
        simp [hl i j hj, Matrix.sub_apply, diagonal_apply_ne _ he] at hij
      exact hgood i j hg he hi hj
    · rw [ite_eq_right hg, sub_zero] at hij
      exact False.elim (hg (hblock i j hij he))
  · rw [sub_sub_cancel]
    exact (pow_le_pow_left₀ (norm_nonneg _) ((l2_opNorm_pinch_le γ T).trans hT) 2).trans_eq
      (Real.sq_sqrt hc)

end Matrix

namespace Quantum

/-! ## The row identity -/


section cell

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The phase cell is symmetric. -/
theorem phaseCell_comm (χ : AddChar Y ℂ) (a b : Option Y) :
    phaseCell Y χ a b = phaseCell Y χ b a := by
  by_cases hχ : χ = 0
  · subst hχ
    rw [phaseCell_zero, one_apply, one_apply]
    simp only [eq_comm]
  rcases a with _ | u <;> rcases b with _ | w
  · rfl
  · rw [phaseCell_none_some hχ, phaseCell_some_none hχ]
  · rw [phaseCell_none_some hχ, phaseCell_some_none hχ]
  · rw [phaseCell_some_some hχ, phaseCell_some_some hχ]
    by_cases h : u = w
    · subst h; rfl
    · simp only [h, Ne.symm h, ite_false, zero_add]
      ring

/-- **The row identity.** For a nontrivial character, the row of the phase cell at a filled
content `u`, with the phase `χ u` removed from its diagonal entry, has squared norm
`(4 - 2 Re χ u) / N`. -/
theorem sum_norm_phaseCell_sub_sq {χ : AddChar Y ℂ} (hχ : χ ≠ 0) (u : Y) :
    ∑ a, ‖phaseCell Y χ (some u) a - if a = some u then χ u else 0‖ ^ 2 =
      (4 - 2 * (χ u).re) / Fintype.card Y := by
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  have hw : ∀ w : Y, phaseCell Y χ (some u) (some w) - (if some w = some u then χ u else 0) =
      (Fintype.card Y : ℂ)⁻¹ * ((1 - χ u) - χ w) := fun w ↦ by
    rw [phaseCell_some_some hχ]
    by_cases h : u = w
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Fintype.sum_option]
  simp only [hw, reduceCtorEq, ite_false, sub_zero, phaseCell_some_none hχ, norm_mul,
    AddChar.norm_apply, mul_one, norm_cellAmp_sq, mul_pow, ← Finset.mul_sum,
    norm_inv, Complex.norm_natCast]
  have hs := sum_norm_sub_signed_char_sq hχ (norm_one (α := ℂ)) (1 - χ u)
  simp only [one_mul] at hs
  rw [hs]
  have h1 : ‖(1 : ℂ) - χ u‖ ^ 2 = 2 - 2 * (χ u).re := by
    rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm (χ u), AddChar.norm_apply]
    simp
    ring
  rw [h1]
  field_simp
  ring

/-- The row identity bounds the row by `6 / N`. -/
theorem sum_norm_phaseCell_sub_sq_le {χ : AddChar Y ℂ} (hχ : χ ≠ 0) (u : Y) :
    ∑ a, ‖phaseCell Y χ (some u) a - if a = some u then χ u else 0‖ ^ 2 ≤
      6 / Fintype.card Y := by
  rw [sum_norm_phaseCell_sub_sq hχ u]
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  have : -1 ≤ (χ u).re := by
    have := Complex.abs_re_le_norm (χ u)
    rw [AddChar.norm_apply] at this
    linarith [neg_abs_le (χ u).re]
  gcongr
  linarith

end cell


/-! ## A label-preserving approximation -/

section approx

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

omit [Fintype Y] [DecidableEq Y] [AddCommGroup Y] in
/-- A database with a filled cell `x` has one more nonempty cell than after emptying `x`. -/
theorem Database.size_eq_size_update_none_add_one {D : Database X Y} {x : X} {u : Y}
    (h : D x = some u) : D.size = Database.size (Function.update D x none) + 1 := by
  have e : Function.update (Function.update D x none) x (some u) = D := by
    rw [Function.update_idem, ← h, Function.update_eq_self]
  conv_lhs => rw [← e]
  exact Database.size_update_some_of_eq_none (Function.update_self x none D) u

/-- The entries of `O_ph^(t)` minus the phase diagonal inside a block of size below `t`. -/
theorem truncatedPhaseOracle_sub_phaseDiagonal_apply {t : ℕ} (x : X) (χ : AddChar Y ℂ)
    {r : Database X Y} (hsize : r.size < t) (a' a : Option Y) :
    (truncatedPhaseOracle X Y t - phaseDiagonal X Y) ((x, χ), Function.update r x a')
        ((x, χ), Function.update r x a) =
      phaseCell Y χ a' a - if a' = a then χ (a.getD 0) else 0 := by
  have hmask : ∀ a, Database.size (Function.update r x a) ≤ t := fun a ↦
    (Database.size_update_le r x a).trans hsize
  have hinj : (((x, χ), Function.update r x a') : (X × AddChar Y ℂ) × Database X Y) =
      ((x, χ), Function.update r x a) ↔ a' = a := by
    constructor
    · intro h
      simpa using congrFun (congrArg Prod.snd h) x
    · rintro rfl; rfl
  have hcond : (x, χ) = (x, χ) ∧
      ∀ j ≠ x, Function.update r x a' j = Function.update r x a j :=
    ⟨rfl, fun j hj ↦ by rw [Function.update_of_ne hj, Function.update_of_ne hj]⟩
  rw [Matrix.sub_apply, truncatedPhaseOracle_apply, phaseOracle_apply, ite_eq_left hcond,
    phaseDiagonal, diagonal_apply]
  simp only [hmask, ite_true, one_mul, mul_one, Function.update_self, hinj,
    Database.lookup_apply]
  split_ifs with h
  · rw [h]
  · rfl

/-- The truncated phase oracle minus the phase diagonal keeps the phase blocks. -/
theorem phaseBlock_eq_of_truncatedPhaseOracle_sub_phaseDiagonal_ne_zero {t : ℕ}
    {m' m : (X × AddChar Y ℂ) × Database X Y}
    (h : (truncatedPhaseOracle X Y t - phaseDiagonal X Y) m' m ≠ 0) :
    (m'.1, Function.update m'.2 m'.1.1 none) = (m.1, Function.update m.2 m.1.1 none) := by
  by_cases hA : truncatedPhaseOracle X Y t m' m = 0
  · rw [Matrix.sub_apply, hA, phaseDiagonal, diagonal_apply] at h
    by_cases hm : m' = m
    · rw [hm]
    · simp [hm] at h
  · exact phaseBlock_eq_of_truncatedPhaseOracle_ne_zero hA

omit [DecidableEq Y] in
/-- A sum over the basis that only sees one phase block is a sum over the contents of the queried
cell. -/
theorem sum_eq_sum_phaseBlock {f : (X × AddChar Y ℂ) × Database X Y → ℝ} (x : X)
    (χ : AddChar Y ℂ) {r : Database X Y} (hr : r x = none)
    (hf : ∀ m, f m ≠ 0 → (m.1, Function.update m.2 m.1.1 none) = ((x, χ), r)) :
    ∑ m, f m = ∑ a, f ((x, χ), Function.update r x a) := by
  classical
  rw [← sum_ite_phaseBlock x χ hr f]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hf m hne)

/-- **The bad rows.** In a block of size below `t` with a nontrivial character, the row of
`O_ph^(t)` minus the phase diagonal at a filled content has squared norm at most `6 / N`; so does
the column. -/
theorem sum_norm_truncatedPhaseOracle_sub_phaseDiagonal_sq_le {t : ℕ} {x : X}
    {χ : AddChar Y ℂ} (hχ : χ ≠ 0) {r : Database X Y} (hr : r x = none) (hsize : r.size < t)
    (u : Y) :
    ∑ m, ‖(truncatedPhaseOracle X Y t - phaseDiagonal X Y) ((x, χ), Function.update r x (some u))
        m‖ ^ 2 ≤ 6 / Fintype.card Y ∧
    ∑ m, ‖(truncatedPhaseOracle X Y t - phaseDiagonal X Y) m
        ((x, χ), Function.update r x (some u))‖ ^ 2 ≤ 6 / Fintype.card Y := by
  have hblk : ∀ a, Function.update (Function.update r x a) x none = r := fun a ↦ by
    rw [Function.update_idem, Database.update_none_of_eq_none hr]
  have hcell : ∀ a, ‖phaseCell Y χ (some u) a - if a = some u then χ u else 0‖ ^ 2 =
      ‖phaseCell Y χ (some u) a - if some u = a then χ (a.getD 0) else 0‖ ^ 2 := fun a ↦ by
    by_cases h : a = some u
    · subst h; simp
    · simp [h, Ne.symm h]
  constructor
  · rw [sum_eq_sum_phaseBlock x χ hr fun m hm ↦ by
      have := phaseBlock_eq_of_truncatedPhaseOracle_sub_phaseDiagonal_ne_zero
        (fun h ↦ hm (by rw [h, norm_zero, zero_pow two_ne_zero]))
      rw [← this]; simp only [hblk]]
    simp only [truncatedPhaseOracle_sub_phaseDiagonal_apply x χ hsize]
    simp only [← hcell]
    exact sum_norm_phaseCell_sub_sq_le hχ u
  · rw [sum_eq_sum_phaseBlock x χ hr fun m hm ↦ by
      have := phaseBlock_eq_of_truncatedPhaseOracle_sub_phaseDiagonal_ne_zero
        (fun h ↦ hm (by rw [h, norm_zero, zero_pow two_ne_zero]))
      rw [this]; simp only [hblk]]
    simp only [truncatedPhaseOracle_sub_phaseDiagonal_apply x χ hsize]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun a _ ↦ ?_) (sum_norm_phaseCell_sub_sq_le hχ u)
    rw [hcell, phaseCell_comm]
    by_cases h : a = some u
    · subst h; simp
    · simp [h, Ne.symm h]

/-- Outside the blocks with a nontrivial character and size below `t`, the truncated phase
oracle is diagonal. -/
theorem eq_of_truncatedPhaseOracle_ne_zero {t : ℕ} {m' m : (X × AddChar Y ℂ) × Database X Y}
    (h : truncatedPhaseOracle X Y t m' m ≠ 0)
    (hm : ¬(m.1.2 ≠ 0 ∧ Database.size (Function.update m.2 m.1.1 none) < t)) : m' = m := by
  obtain ⟨⟨x', χ'⟩, D'⟩ := m'
  obtain ⟨⟨x, χ⟩, D⟩ := m
  rw [truncatedPhaseOracle_apply, phaseOracle_apply] at h
  by_cases hc : (x', χ') = (x, χ) ∧ ∀ j ≠ x, D' j = D j
  swap
  · rw [ite_eq_right hc] at h
    simp at h
  rw [ite_eq_left hc] at h
  obtain ⟨hq, hj⟩ := hc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
  suffices hx : D' x' = D x' by
    have : D' = D := funext fun j ↦ by
      by_cases hjx : j = x'
      · rw [hjx, hx]
      · exact hj j hjx
    rw [this]
  dsimp only at hm
  by_cases hχ : χ' = 0
  · subst hχ
    by_contra hne
    simp [phaseCell_zero, one_apply_ne hne] at h
  have hsize : t ≤ Database.size (Function.update D x' none) := by
    by_contra hlt
    exact hm ⟨hχ, not_le.mp hlt⟩
  have hupd : Function.update D' x' none = Function.update D x' none := funext fun j ↦ by
    by_cases hjx : j = x'
    · subst hjx; simp
    · simp [Function.update_of_ne hjx, hj j hjx]
  have hnone : ∀ D₁ : Database X Y, Function.update D₁ x' none = Function.update D x' none →
      Database.size D₁ ≤ t → D₁ x' = none := fun D₁ h₁ h₂ ↦ by
    by_contra hne
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hne
    have := Database.size_eq_size_update_none_add_one hu
    rw [h₁] at this
    omega
  have hD' : Database.size D' ≤ t := by
    by_contra hlt
    exact h (by simp [hlt])
  have hD : Database.size D ≤ t := by
    by_contra hlt
    exact h (by simp [hlt])
  rw [hnone D' hupd hD', hnone D rfl hD]

variable {ι : Type*} [DecidableEq ι]

/-- The bad basis states of the phase basis for `π` and `t`: a nontrivial character, a block of
size below `t`, and a content of the queried cell that changes the label. -/
private def IsBad (π : Database X Y → ι) (t : ℕ) (m : (X × AddChar Y ℂ) × Database X Y) : Prop :=
  m.1.2 ≠ 0 ∧ Database.size (Function.update m.2 m.1.1 none) < t ∧
    π m.2 ≠ π (Function.update m.2 m.1.1 none)

private noncomputable instance (π : Database X Y → ι) (t : ℕ) : DecidablePred (IsBad π t) :=
  Classical.decPred _

/-- The projector onto the bad basis states. -/
private noncomputable def badProjector (π : Database X Y → ι) (t : ℕ) :
    Matrix ((X × AddChar Y ℂ) × Database X Y) ((X × AddChar Y ℂ) × Database X Y) ℂ :=
  diagonal fun m ↦ if IsBad π t m then 1 else 0

omit [DecidableEq ι] in
private theorem isStarProjection_badProjector (π : Database X Y → ι) (t : ℕ) :
    IsStarProjection (badProjector π t) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, badProjector, diagonal_mul_diagonal]
    congr 1
    funext m
    by_cases h : IsBad π t m <;> simp [h]
  · rw [IsSelfAdjoint, badProjector, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1
    funext m
    by_cases h : IsBad π t m <;> simp [h]

omit [DecidableEq ι] in
private theorem badProjector_mul_apply (π : Database X Y → ι) (t : ℕ)
    (A : Matrix ((X × AddChar Y ℂ) × Database X Y) ((X × AddChar Y ℂ) × Database X Y) ℂ)
    (i j : (X × AddChar Y ℂ) × Database X Y) :
    (badProjector π t * A) i j = if IsBad π t i then A i j else 0 := by
  rw [badProjector, diagonal_mul]
  split_ifs <;> simp

omit [DecidableEq ι] in
private theorem mul_badProjector_apply (π : Database X Y → ι) (t : ℕ)
    (A : Matrix ((X × AddChar Y ℂ) × Database X Y) ((X × AddChar Y ℂ) × Database X Y) ℂ)
    (i j : (X × AddChar Y ℂ) × Database X Y) :
    (A * badProjector π t) i j = if IsBad π t j then A i j else 0 := by
  rw [badProjector, mul_diagonal]
  split_ifs <;> simp

end approx

section labelChangingRows

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {Q : Type*} [Fintype Q] [DecidableEq Q] {ι : Type*} [DecidableEq ι]

/-- Counting label-changing filled rows in each active cell block bounds their operator norm
by the square root of the row constant times database instability. -/
theorem l2_opNorm_labelChangingRows_le [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    (π : Database X Y → ι) (t : ℕ) (active : X → Q → Prop)
    [∀ x q, Decidable (active x q)] {c : ℝ} (hc : 0 ≤ c)
    {A : Matrix ((X × Q) × Database X Y) ((X × Q) × Database X Y) ℂ}
    (hA : ∀ i j, A i j ≠ 0 →
      (i.1, Function.update i.2 i.1.1 none) = (j.1, Function.update j.2 j.1.1 none))
    (hrow : ∀ x q (r : Database X Y), r x = none → r.size < t → active x q → ∀ u,
      ∑ m, ‖A ((x, q), Function.update r x (some u)) m‖ ^ 2 ≤ c / Fintype.card Y) :
    ‖diagonal (fun m ↦ if active m.1.1 m.1.2 ∧
        Database.size (Function.update m.2 m.1.1 none) < t ∧
        π m.2 ≠ π (Function.update m.2 m.1.1 none) then (1 : ℂ) else 0) * A‖ ≤
      √(c * (Database.instability π t).toReal) := by
  classical
  let Bad (m : (X × Q) × Database X Y) := active m.1.1 m.1.2 ∧
    Database.size (Function.update m.2 m.1.1 none) < t ∧
    π m.2 ≠ π (Function.update m.2 m.1.1 none)
  have he : ∀ (i j : (X × Q) × Database X Y),
      (diagonal (fun m ↦ if Bad m then (1 : ℂ) else 0) * A :
        Matrix ((X × Q) × Database X Y) ((X × Q) × Database X Y) ℂ) i j =
      if Bad i then A i j else 0 := by
    intro i j
    rw [diagonal_mul]
    split_ifs <;> simp_all
  refine l2_opNorm_le_of_blocks
    (fun m : (X × Q) × Database X Y ↦ (m.1, Function.update m.2 m.1.1 none))
    (fun m : (X × Q) × Database X Y ↦ (m.1, Function.update m.2 m.1.1 none))
    (fun i j h ↦ hA i j fun h0 ↦ h (by rw [he, h0, ite_self]))
    (Real.sqrt_nonneg _) ?_
  rintro ⟨⟨x, q⟩, D₀⟩
  rw [Real.sq_sqrt (mul_nonneg hc ENNReal.toReal_nonneg)]
  dsimp only
  let r : Database X Y := Function.update D₀ x none
  have hr : r x = none := Function.update_self x none D₀
  have hblk : ∀ a, Function.update (Function.update r x a) x none = r := fun a ↦ by
    rw [Function.update_idem, Database.update_none_of_eq_none hr]
  rw [sum_ite_cellBlock x q hr]
  have hterm : ∀ a, ∑ m, ‖(diagonal (fun m ↦ if Bad m then (1 : ℂ) else 0) * A :
      Matrix ((X × Q) × Database X Y) ((X × Q) × Database X Y) ℂ)
      ((x, q), Function.update r x a) m‖ ^ 2 ≤
        if active x q ∧ r.size < t ∧ π (Function.update r x a) ≠ π r then
          c / Fintype.card Y else 0 := by
    intro a
    simp_rw [he]
    simp only [Bad, hblk]
    split_ifs with hb
    · cases a with
      | none => exact False.elim (hb.2.2 (by rw [Database.update_none_of_eq_none hr]))
      | some u => exact hrow x q r hr hb.2.1 hb.1 u
    · simp
  refine (Finset.sum_le_sum fun a _ ↦ hterm a).trans ?_
  rw [Fintype.sum_option]
  simp only [Database.update_none_of_eq_none hr, ne_eq, not_true_eq_false, and_false,
    ite_false, zero_add]
  by_cases hs : active x q ∧ r.size < t
  · have heq : ∀ u, (if active x q ∧ r.size < t ∧ π (Function.update r x (some u)) ≠ π r then
        c / (Fintype.card Y : ℝ) else 0) =
        c / Fintype.card Y * if π (Function.update r x (some u)) ≠ π r then 1 else 0 := by
      intro u
      simp only [hs.1, hs.2, true_and]
      split_ifs <;> simp_all
    simp only [ne_eq] at heq
    rw [Finset.sum_congr rfl fun u _ ↦ heq u, ← Finset.mul_sum, Finset.sum_boole]
    calc c / (Fintype.card Y : ℝ) *
          ((Finset.univ.filter fun u ↦ ¬π (Function.update r x (some u)) = π r).card : ℝ)
        = c * (((Finset.univ.filter fun u ↦ π (Function.update r x (some u)) ≠ π r).card : ℝ) /
            Fintype.card Y) := by ring
      _ ≤ c * (Database.instability π t).toReal :=
        mul_le_mul_of_nonneg_left (Database.card_div_le_instability π hs.2 hr) hc
  · have hz : ∀ u, ¬(active x q ∧ r.size < t ∧
        π (Function.update r x (some u)) ≠ π r) := fun _ h ↦ hs ⟨h.1, h.2.1⟩
    simp only [hz, ite_false, Finset.sum_const_zero]
    exact mul_nonneg hc ENNReal.toReal_nonneg


end labelChangingRows

section approxInstability

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- The bad rows of a block-diagonal matrix whose bad rows have squared norm at most `6 / N`
span an operator of norm at most `√(6 I)`. -/
private theorem l2_opNorm_badProjector_mul_le [UniformAnswerMeasure (X →ₒ Y)]
    (π : Database X Y → ι) (t : ℕ)
    {A : Matrix ((X × AddChar Y ℂ) × Database X Y) ((X × AddChar Y ℂ) × Database X Y) ℂ}
    (hA : ∀ i j, A i j ≠ 0 →
      (i.1, Function.update i.2 i.1.1 none) = (j.1, Function.update j.2 j.1.1 none))
    (hrow : ∀ (x : X) (χ : AddChar Y ℂ), χ ≠ 0 → ∀ r : Database X Y, r x = none →
      Database.size r < t →
        ∀ u, ∑ m, ‖A ((x, χ), Function.update r x (some u)) m‖ ^ 2 ≤ 6 / Fintype.card Y) :
    ‖badProjector π t * A‖ ≤ √(6 * (Database.instability π t).toReal) := by
  classical
  convert l2_opNorm_labelChangingRows_le π t (fun _ χ ↦ χ ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 6) hA (fun x χ r hr hs hχ u ↦ hrow x χ hχ r hr hs u) using 1
  congr 2
  unfold badProjector
  congr 1
  funext m
  simp only [IsBad]
  split_ifs with h
  · exact ite_eq_left h
  · exact ite_eq_right h

/-- **The label-preserving approximation, phase basis.** There is an operator `S` that preserves
the label `π D` of the database with `‖O_ph^(t) - S‖² ≤ 6 I(π, t)`. -/
theorem exists_pinch_eq_truncatedPhaseOracle_sub_sq_le [UniformAnswerMeasure (X →ₒ Y)]
    (π : Database X Y → ι) (t : ℕ) :
    ∃ S, pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) S = S ∧
      ‖truncatedPhaseOracle X Y t - S‖ ^ 2 ≤ 6 * (Database.instability π t).toReal := by
  classical
  have hI : 0 ≤ (Database.instability π t).toReal := ENNReal.toReal_nonneg
  have hP := isStarProjection_badProjector π t
  have hPh : (badProjector π t)ᴴ = badProjector π t := hP.isSelfAdjoint
  have hMblk : ∀ i j, (truncatedPhaseOracle X Y t - phaseDiagonal X Y) i j ≠ 0 →
      (i.1, Function.update i.2 i.1.1 none) = (j.1, Function.update j.2 j.1.1 none) :=
    fun i j h ↦ phaseBlock_eq_of_truncatedPhaseOracle_sub_phaseDiagonal_ne_zero h
  -- the row and the column of the bad states
  have hrow : ‖badProjector π t * (truncatedPhaseOracle X Y t - phaseDiagonal X Y)‖ ≤
      √(6 * (Database.instability π t).toReal) :=
    l2_opNorm_badProjector_mul_le π t hMblk fun x χ hχ r hr hs u ↦
      (sum_norm_truncatedPhaseOracle_sub_phaseDiagonal_sq_le hχ hr hs u).1
  have hcol : ‖(truncatedPhaseOracle X Y t - phaseDiagonal X Y) * badProjector π t‖ ≤
      √(6 * (Database.instability π t).toReal) := by
    rw [← l2_opNorm_conjTranspose, conjTranspose_mul, hPh]
    refine l2_opNorm_badProjector_mul_le π t (fun i j h ↦ (hMblk j i ?_).symm)
      fun x χ hχ r hr hs u ↦ ?_
    · rwa [conjTranspose_apply, star_ne_zero] at h
    · simpa only [conjTranspose_apply, norm_star] using
        (sum_norm_truncatedPhaseOracle_sub_phaseDiagonal_sq_le hχ hr hs u).2
  obtain ⟨γ, hγ⟩ : ∃ γ : (X × AddChar Y ℂ) × Database X Y →
      ((X × AddChar Y ℂ) × Database X Y) ⊕ ((X × AddChar Y ℂ) × Database X Y),
      γ = fun m : (X × AddChar Y ℂ) × Database X Y ↦
        if m.1.2 ≠ 0 ∧ Database.size (Function.update m.2 m.1.1 none) < t then
          Sum.inl (m.1, Function.update m.2 m.1.1 none)
        else Sum.inr m := ⟨_, rfl⟩
  have hγeq : ∀ i j, γ i = γ j → i ≠ j →
      (i.1.2 ≠ 0 ∧ Database.size (Function.update i.2 i.1.1 none) < t) ∧
      (j.1.2 ≠ 0 ∧ Database.size (Function.update j.2 j.1.1 none) < t) ∧
      (i.1, Function.update i.2 i.1.1 none) = (j.1, Function.update j.2 j.1.1 none) := by
    intro i j h hne
    rw [hγ] at h
    dsimp only at h
    split_ifs at h with hi hj
    · exact ⟨hi, hj, Sum.inl_injective h⟩
    · exact absurd (Sum.inr_injective h) hne
  refine exists_pinch_eq_sub_sq_le_of_completion
    (fun m ↦ π m.2) γ (IsBad π t) (truncatedPhaseOracle X Y t)
    (fun m ↦ m.1.2 (m.2.lookup m.1.1)) (by positivity) hrow hcol ?_ ?_
  · intro i j hS hij
    have hk := phaseBlock_eq_of_truncatedPhaseOracle_ne_zero hS
    by_cases haj : j.1.2 ≠ 0 ∧ Database.size (Function.update j.2 j.1.1 none) < t
    · have hai : i.1.2 ≠ 0 ∧ Database.size (Function.update i.2 i.1.1 none) < t := by
        obtain ⟨h₁, h₂⟩ := Prod.mk.inj hk
        rw [h₂, h₁]
        exact haj
      rw [hγ]
      dsimp only
      rw [ite_eq_left hai, ite_eq_left haj, hk]
    · exact False.elim (hij (eq_of_truncatedPhaseOracle_ne_zero hS haj))
  · intro i j hg hij hbi hbj
    obtain ⟨hai, haj, hk⟩ := hγeq i j hg hij
    have h₁ : π i.2 = π (Function.update i.2 i.1.1 none) := by
      by_contra h
      exact hbi ⟨hai.1, hai.2, h⟩
    have h₂ : π j.2 = π (Function.update j.2 j.1.1 none) := by
      by_contra h
      exact hbj ⟨haj.1, haj.2, h⟩
    rw [h₁, h₂]
    exact congrArg (fun p ↦ π p.2) hk

/-- **The label-preserving approximation.** There is an operator `S` on the joint register that
preserves the label `π D` of the database with `‖O^(t) - S‖² ≤ 6 I(π, t)`. For the pinching of
`O^(t)` the constant is `20` in [CDHZ, Lemma 5.9]
(`Quantum.l2_opNorm_pinch_truncatedOracle_sub_sq_le`) and `8` at best. -/
theorem exists_pinch_eq_truncatedOracle_sub_sq_le [UniformAnswerMeasure (X →ₒ Y)]
    (π : Database X Y → ι) (t : ℕ) :
    ∃ S, pinch (fun m : (X × Y) × Database X Y ↦ π m.2) S = S ∧
      ‖truncatedOracle X Y t - S‖ ^ 2 ≤ 6 * (Database.instability π t).toReal := by
  obtain ⟨S, hS, hdist⟩ := exists_pinch_eq_truncatedPhaseOracle_sub_sq_le π t
  have hU : ∀ a b, (queryFourier X Y)ᴴ a b ≠ 0 →
      (fun m : (X × Y) × Database X Y ↦ π m.2) a =
        (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) b := by
    rintro ⟨⟨x, y⟩, D⟩ ⟨⟨x', χ⟩, D'⟩ h
    rw [conjTranspose_apply, queryFourier_apply] at h
    by_cases hc : x' = x ∧ D' = D
    · simp [hc.2]
    · simp only [hc, ↓reduceIte, star_zero, ne_eq, not_true_eq_false] at h
  have e := mul_pinch_mul_conjTranspose (fun m : (X × Y) × Database X Y ↦ π m.2)
    (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) hU S
  rw [conjTranspose_conjTranspose, hS] at e
  refine ⟨(queryFourier X Y)ᴴ * S * queryFourier X Y, e.symm, ?_⟩
  rw [truncatedOracle_eq, ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact (pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_conjTranspose_mul_mul_le
    (queryFourier_mul_conjTranspose X Y) _) 2).trans hdist

end approxInstability

/-! ## Theorem 5.4 and Corollary 5.6 with the constant `24` -/

section theorem54

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [UniformAnswerMeasure (X →ₒ Y)] {ι : Type*} {E : Type*} [Fintype E] [DecidableEq E]

/-- **Theorem 5.4 of ePrint 2025/2166 with the constant `24`, phase basis.** Let `W i` be unitaries
on the joint register `((X × Ŷ) × Database X Y) × E` that preserve the label `π D` of the database
and commute with `O_ph^(t) ⊗ 1_E`. Then `V = ∑ i, P^(i) W i` satisfies
`‖[V, O_ph^(t) ⊗ 1_E]‖² ≤ 24 I(π, t)`. -/
theorem l2_opNorm_commutator_truncatedPhaseOracle_sq_le_twentyFour_mul (π : Database X Y → ι)
    (t : ℕ)
    {W : ι → Matrix (((X × AddChar Y ℂ) × Database X Y) × E)
      (((X × AddChar Y ℂ) × Database X Y) × E) ℂ}
    (hW : ∀ k a b, W k a b ≠ 0 → π a.1.2 = π b.1.2) (hU : ∀ k, W k ∈ unitaryGroup _ ℂ)
    (hA : ∀ k, W k * (truncatedPhaseOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) =
      (truncatedPhaseOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) * W k) :
    ‖labelControlled (fun a ↦ π a.1.2) W * (truncatedPhaseOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedPhaseOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) *
          labelControlled (fun a ↦ π a.1.2) W‖ ^ 2
      ≤ 24 * (Database.instability π t).toReal := by
  classical
  obtain ⟨S, hS, hdist⟩ := exists_pinch_eq_truncatedPhaseOracle_sub_sq_le π t
  have h := l2_opNorm_commutator_labelControlled_kronecker_one_le hS hW hU hA
  calc _ ≤ (2 * ‖truncatedPhaseOracle X Y t - S‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 4 * ‖truncatedPhaseOracle X Y t - S‖ ^ 2 := by ring
    _ ≤ 4 * (6 * (Database.instability π t).toReal) := by gcongr
    _ = 24 * (Database.instability π t).toReal := by ring

/-- **Theorem 5.4 of ePrint 2025/2166 with the constant `24`.** Let `W i` be unitaries on the joint
register `((X × Y) × Database X Y) × E` that preserve the label `π D` of the database and commute
with `O^(t) ⊗ 1_E`. The label-controlled unitary `V = ∑ i, P^(i) W i` almost commutes with the
truncated compressed oracle: `‖[V, O^(t) ⊗ 1_E]‖² ≤ 24 I(π, t)`. [CDHZ] state the constant `80`
(`Quantum.l2_opNorm_commutator_truncatedOracle_sq_le`, a corollary). The constant `24` is optimal
(`Quantum.exists_mul_instability_lt_l2_opNorm_commutator_truncatedOracle_sq`). -/
theorem l2_opNorm_commutator_truncatedOracle_sq_le_twentyFour_mul (π : Database X Y → ι) (t : ℕ)
    {W : ι → Matrix (((X × Y) × Database X Y) × E) (((X × Y) × Database X Y) × E) ℂ}
    (hW : ∀ k a b, W k a b ≠ 0 → π a.1.2 = π b.1.2) (hU : ∀ k, W k ∈ unitaryGroup _ ℂ)
    (hA : ∀ k, W k * (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) =
      (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) * W k) :
    ‖labelControlled (fun a ↦ π a.1.2) W * (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) * labelControlled (fun a ↦ π a.1.2) W‖ ^ 2
      ≤ 24 * (Database.instability π t).toReal := by
  classical
  obtain ⟨S, hS, hdist⟩ := exists_pinch_eq_truncatedOracle_sub_sq_le π t
  have h := l2_opNorm_commutator_labelControlled_kronecker_one_le hS hW hU hA
  calc _ ≤ (2 * ‖truncatedOracle X Y t - S‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 4 * ‖truncatedOracle X Y t - S‖ ^ 2 := by ring
    _ ≤ 4 * (6 * (Database.instability π t).toReal) := by gcongr
    _ = 24 * (Database.instability π t).toReal := by ring

/-- **Corollary 5.6 of ePrint 2025/2166 with the constant `24`, phase basis.** The purified
measurement `V = ∑ i, P^(i) ⊗ U i`, with any unitaries `U i` on a register `B`, satisfies
`‖[V, O_ph^(t) ⊗ 1_B]‖² ≤ 24 I(π, t)`. -/
theorem l2_opNorm_commutator_truncatedPhaseOracle_purifiedMeasurement_sq_le_twentyFour_mul
    (π : Database X Y → ι) (t : ℕ) {U : ι → Matrix E E ℂ} (hU : ∀ i, U i ∈ unitaryGroup E ℂ) :
    ‖labelControlled (fun a ↦ π a.1.2)
          (fun i ↦ (1 : Matrix ((X × AddChar Y ℂ) × Database X Y)
            ((X × AddChar Y ℂ) × Database X Y) ℂ) ⊗ₖ U i) *
          (truncatedPhaseOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedPhaseOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) *
          labelControlled (fun a ↦ π a.1.2)
            (fun i ↦ (1 : Matrix ((X × AddChar Y ℂ) × Database X Y)
              ((X × AddChar Y ℂ) × Database X Y) ℂ) ⊗ₖ U i)‖ ^ 2
      ≤ 24 * (Database.instability π t).toReal := by
  classical
  obtain ⟨S, hS, hdist⟩ := exists_pinch_eq_truncatedPhaseOracle_sub_sq_le π t
  have h := l2_opNorm_commutator_labelControlled_one_kronecker_le
    (A := truncatedPhaseOracle X Y t) hS hU
  calc _ ≤ (2 * ‖truncatedPhaseOracle X Y t - S‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 4 * ‖truncatedPhaseOracle X Y t - S‖ ^ 2 := by ring
    _ ≤ 4 * (6 * (Database.instability π t).toReal) := by gcongr
    _ = 24 * (Database.instability π t).toReal := by ring

/-- **Corollary 5.6 of ePrint 2025/2166 with the constant `24`.** The purified measurement of the
label of the database into a register `B`, `V = ∑ i, P^(i) ⊗ U i` with any unitaries `U i` on
`B`, almost commutes with the truncated compressed oracle: `‖[V, O^(t) ⊗ 1_B]‖² ≤ 24 I(π, t)`. -/
theorem l2_opNorm_commutator_purifiedMeasurement_sq_le_twentyFour_mul (π : Database X Y → ι) (t : ℕ)
    {U : ι → Matrix E E ℂ} (hU : ∀ i, U i ∈ unitaryGroup E ℂ) :
    ‖labelControlled (fun a ↦ π a.1.2)
          (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ U i) *
          (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) *
          labelControlled (fun a ↦ π a.1.2)
            (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ U i)‖ ^ 2
      ≤ 24 * (Database.instability π t).toReal := by
  classical
  obtain ⟨S, hS, hdist⟩ := exists_pinch_eq_truncatedOracle_sub_sq_le π t
  have h := l2_opNorm_commutator_labelControlled_one_kronecker_le
    (A := truncatedOracle X Y t) hS hU
  calc _ ≤ (2 * ‖truncatedOracle X Y t - S‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 4 * ‖truncatedOracle X Y t - S‖ ^ 2 := by ring
    _ ≤ 4 * (6 * (Database.instability π t).toReal) := by gcongr
    _ = 24 * (Database.instability π t).toReal := by ring

/-- **Theorem 5.4 of ePrint 2025/2166**, with the paper's constant `80`:
`‖[V, O^(t) ⊗ 1_E]‖² ≤ 80 I(π, t)`. A corollary of
`Quantum.l2_opNorm_commutator_truncatedOracle_sq_le_twentyFour_mul`. -/
theorem l2_opNorm_commutator_truncatedOracle_sq_le (π : Database X Y → ι) (t : ℕ)
    {W : ι → Matrix (((X × Y) × Database X Y) × E) (((X × Y) × Database X Y) × E) ℂ}
    (hW : ∀ k a b, W k a b ≠ 0 → π a.1.2 = π b.1.2) (hU : ∀ k, W k ∈ unitaryGroup _ ℂ)
    (hA : ∀ k, W k * (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) =
      (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) * W k) :
    ‖labelControlled (fun a ↦ π a.1.2) W * (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) * labelControlled (fun a ↦ π a.1.2) W‖ ^ 2
      ≤ 80 * (Database.instability π t).toReal :=
  (l2_opNorm_commutator_truncatedOracle_sq_le_twentyFour_mul π t hW hU hA).trans
    (mul_le_mul_of_nonneg_right (by norm_num) ENNReal.toReal_nonneg)

/-- **Corollary 5.6 of ePrint 2025/2166**, with the paper's constant `80`. A corollary of
`Quantum.l2_opNorm_commutator_purifiedMeasurement_sq_le_twentyFour_mul`. -/
theorem l2_opNorm_commutator_purifiedMeasurement_sq_le (π : Database X Y → ι) (t : ℕ)
    {U : ι → Matrix E E ℂ} (hU : ∀ i, U i ∈ unitaryGroup E ℂ) :
    ‖labelControlled (fun a ↦ π a.1.2)
          (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ U i) *
          (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) *
          labelControlled (fun a ↦ π a.1.2)
            (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ U i)‖ ^ 2
      ≤ 80 * (Database.instability π t).toReal :=
  (l2_opNorm_commutator_purifiedMeasurement_sq_le_twentyFour_mul π t hU).trans
    (mul_le_mul_of_nonneg_right (by norm_num) ENNReal.toReal_nonneg)

end theorem54

/-! ## The XOR measurement -/

section xor

variable (B : Type*) [Fintype B] [DecidableEq B] [AddGroup B]

/-- The shift `|b⟩ ↦ |b + i⟩` of a register indexed by an additive group: for `B = (ZMod 2)^n` it
XORs `i` into the register. -/
@[expose]
def xorShift (i : B) : Matrix B B ℂ :=
  of fun b' b ↦ if b' = b + i then 1 else 0

variable {B}

omit [Fintype B] in
@[simp]
theorem xorShift_apply (i b' b : B) : xorShift B i b' b = if b' = b + i then 1 else 0 :=
  rfl

theorem xorShift_mem_unitaryGroup (i : B) : xorShift B i ∈ unitaryGroup B ℂ := by
  rw [mem_unitaryGroup_iff]
  ext b' b''
  rw [Matrix.mul_apply, Finset.sum_eq_single (b' - i)]
  · by_cases h : b' = b''
    · subst h
      simp [star_apply]
    · simp [star_apply, one_apply_ne h, Ne.symm h]
  · intro b _ hb
    have : b' ≠ b + i := fun h ↦ hb (by rw [h, add_sub_cancel_right])
    simp [this]
  · simp

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [UniformAnswerMeasure (X →ₒ Y)]

/-- **Corollary 5.6 of ePrint 2025/2166 with the constant `24`, XOR form.** Measuring the label
`π D ∈ B` of the database by XORing it into a register `B` almost commutes with the truncated
compressed oracle: `‖[V, O^(t) ⊗ 1_B]‖² ≤ 24 I(π, t)`, where `V |q, D, b⟩ = |q, D, b + π D⟩` (as
in [DFMS22, Theorem 3.1]). -/
theorem l2_opNorm_commutator_xorMeasurement_sq_le_twentyFour_mul (π : Database X Y → B) (t : ℕ) :
    ‖labelControlled (fun a ↦ π a.1.2)
          (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
            xorShift B i) * (truncatedOracle X Y t ⊗ₖ (1 : Matrix B B ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix B B ℂ)) *
          labelControlled (fun a ↦ π a.1.2)
            (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
              xorShift B i)‖ ^ 2
      ≤ 24 * (Database.instability π t).toReal :=
  l2_opNorm_commutator_purifiedMeasurement_sq_le_twentyFour_mul π t xorShift_mem_unitaryGroup

/-- **Corollary 5.6 of ePrint 2025/2166, XOR form**, with the paper's constant `80`:
`‖[V, O^(t) ⊗ 1_B]‖² ≤ 80 I(π, t)`, where `V |q, D, b⟩ = |q, D, b + π D⟩`. -/
theorem l2_opNorm_commutator_xorMeasurement_sq_le (π : Database X Y → B) (t : ℕ) :
    ‖labelControlled (fun a ↦ π a.1.2)
          (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
            xorShift B i) * (truncatedOracle X Y t ⊗ₖ (1 : Matrix B B ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix B B ℂ)) *
          labelControlled (fun a ↦ π a.1.2)
            (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
              xorShift B i)‖ ^ 2
      ≤ 80 * (Database.instability π t).toReal :=
  l2_opNorm_commutator_purifiedMeasurement_sq_le π t xorShift_mem_unitaryGroup

end xor

/-! ## Optimality -/


section sharpness

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Inside an active block, a query `(x, χ)` to a database `r` of size below `t`, the truncated
phase oracle is the phase cell. -/
theorem truncatedPhaseOracle_apply_update_of_size_lt {t : ℕ} (x : X) (χ : AddChar Y ℂ)
    {r : Database X Y} (hsize : r.size < t) (a' a : Option Y) :
    truncatedPhaseOracle X Y t ((x, χ), Function.update r x a') ((x, χ), Function.update r x a) =
      phaseCell Y χ a' a := by
  have hmask : ∀ a, Database.size (Function.update r x a) ≤ t := fun a ↦
    (Database.size_update_le r x a).trans hsize
  have hcond : (x, χ) = (x, χ) ∧
      ∀ j ≠ x, Function.update r x a' j = Function.update r x a j :=
    ⟨rfl, fun j hj ↦ by rw [Function.update_of_ne hj, Function.update_of_ne hj]⟩
  rw [truncatedPhaseOracle_apply, phaseOracle_apply, ite_eq_left hcond]
  simp only [hmask, ite_true, one_mul, mul_one, Function.update_self]

omit [Fintype X] [Fintype Y] [AddCommGroup Y] in
/-- A label-controlled operator of scalars is diagonal. -/
theorem labelControlled_smul_one {n κ : Type*} [DecidableEq n] (β : n → κ) (c : κ → ℂ) :
    labelControlled β (fun k ↦ c k • (1 : Matrix n n ℂ)) = diagonal fun a ↦ c (β a) := by
  ext a b
  rw [labelControlled_apply, Matrix.smul_apply, one_apply, diagonal_apply]
  split_ifs <;> simp

/-- **Sharpness of the constant `24`, the commutator.** Let `χ y₀ = -1`, `t ≥ 1`, and label the
databases by whether `D x₀ = y₀`. For the scalar control `V = P_A - P_B`,
`‖[V, O^(t)]‖² ≥ 24 / N - 36 / N²`. -/
theorem le_l2_opNorm_commutator_truncatedOracle_sq (x₀ : X) {y₀ : Y} {χ : AddChar Y ℂ}
    (hχ : χ y₀ = -1) {t : ℕ} (ht : 1 ≤ t) :
    24 / (Fintype.card Y : ℝ) - 36 / (Fintype.card Y : ℝ) ^ 2 ≤
      ‖labelControlled (fun m : (X × Y) × Database X Y ↦ decide (m.2 x₀ = some y₀))
            (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ)) * truncatedOracle X Y t -
          truncatedOracle X Y t *
            labelControlled (fun m : (X × Y) × Database X Y ↦ decide (m.2 x₀ = some y₀))
              (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ))‖ ^ 2 := by
  have hχ0 : χ ≠ 0 := fun h ↦ by
    rw [h, AddChar.zero_apply] at hχ
    norm_num at hχ
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  set s : Database X Y → ℂ := fun D ↦ if D x₀ = some y₀ then -1 else 1 with hs
  rw [labelControlled_smul_one]
  have hV : (diagonal fun m : (X × Y) × Database X Y ↦
      if decide (m.2 x₀ = some y₀) then (-1 : ℂ) else 1) = diagonal fun m ↦ s m.2 := by
    congr 1
    funext m
    simp [hs]
  rw [hV]
  -- move to the phase basis
  set Vs : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ :=
    diagonal fun m ↦ s m.2 with hVs
  set Vp : Matrix ((X × AddChar Y ℂ) × Database X Y) ((X × AddChar Y ℂ) × Database X Y) ℂ :=
    diagonal fun m ↦ s m.2 with hVp
  have hFV : queryFourier X Y * Vs = Vp * queryFourier X Y := by
    ext ⟨⟨x', χ'⟩, D'⟩ ⟨⟨x, y⟩, D⟩
    rw [hVs, hVp, mul_diagonal, diagonal_mul, queryFourier_apply]
    split_ifs with h
    · rw [h.2]; ring
    · simp
  have hVF : Vs * (queryFourier X Y)ᴴ = (queryFourier X Y)ᴴ * Vp := by
    ext ⟨⟨x, y⟩, D⟩ ⟨⟨x', χ'⟩, D'⟩
    rw [hVs, hVp, mul_diagonal, diagonal_mul, conjTranspose_apply, queryFourier_apply]
    split_ifs with h
    · rw [h.2]; ring
    · simp
  have hconj : queryFourier X Y * (Vs * truncatedOracle X Y t - truncatedOracle X Y t * Vs) *
      (queryFourier X Y)ᴴ = Vp * truncatedPhaseOracle X Y t - truncatedPhaseOracle X Y t * Vp := by
    rw [truncatedPhaseOracle_eq, Matrix.mul_sub, Matrix.sub_mul]
    simp only [← Matrix.mul_assoc, hFV]
    simp only [Matrix.mul_assoc, hVF]
  have hle : ‖Vp * truncatedPhaseOracle X Y t - truncatedPhaseOracle X Y t * Vp‖ ≤
      ‖Vs * truncatedOracle X Y t - truncatedOracle X Y t * Vs‖ := by
    rw [← hconj]
    exact l2_opNorm_mul_mul_conjTranspose_le (conjTranspose_queryFourier_mul X Y) _
  refine le_trans ?_ (pow_le_pow_left₀ (norm_nonneg _) hle 2)
  -- the column of a bad state
  set r : Database X Y := Database.empty with hr
  have hr0 : r x₀ = none := Database.empty_apply x₀
  have hrs : r.size < t := by rw [hr, Database.size_empty]; omega
  set m : (X × AddChar Y ℂ) × Database X Y := ((x₀, χ), Function.update r x₀ (some y₀)) with hm
  have h1 := sum_norm_mulVec_sq_le (Vp * truncatedPhaseOracle X Y t -
    truncatedPhaseOracle X Y t * Vp) (Pi.single m 1)
  have hsingle : ∑ j, ‖(Pi.single m (1 : ℂ) : _ → ℂ) j‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single m]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  rw [hsingle, mul_one, mulVec_single_one] at h1
  refine le_trans (le_of_eq ?_) h1
  simp only [col_apply]
  have hsm : s m.2 = -1 := by simp [hs, hm]
  have hentry : ∀ i, (Vp * truncatedPhaseOracle X Y t - truncatedPhaseOracle X Y t * Vp) i m =
      (s i.2 + 1) * truncatedPhaseOracle X Y t i m := fun i ↦ by
    rw [Matrix.sub_apply, hVp, diagonal_mul, mul_diagonal, hsm]
    ring
  simp only [hentry]
  have hblk : Function.update (Function.update r x₀ (some y₀)) x₀ none = r := by
    rw [Function.update_idem, Database.update_none_of_eq_none hr0]
  rw [sum_eq_sum_phaseBlock x₀ χ hr0 fun i hi ↦ by
    have h0 : truncatedPhaseOracle X Y t i m ≠ 0 := fun h ↦ hi (by rw [h]; simp)
    rw [phaseBlock_eq_of_truncatedPhaseOracle_ne_zero h0, hm]
    simp only [hblk]]
  simp only [hm, truncatedPhaseOracle_apply_update_of_size_lt x₀ χ hrs]
  have hsa : ∀ a, s (Function.update r x₀ a) = if a = some y₀ then -1 else 1 := fun a ↦ by
    simp [hs]
  have hterm : ∀ a, ‖(s (Function.update r x₀ a) + 1) * phaseCell Y χ a (some y₀)‖ ^ 2 =
      4 * ‖phaseCell Y χ (some y₀) a - if a = some y₀ then χ y₀ else 0‖ ^ 2 -
        if a = some y₀ then 36 / (Fintype.card Y : ℝ) ^ 2 else 0 := fun a ↦ by
    rw [hsa]
    by_cases ha : a = some y₀
    · subst ha
      rw [phaseCell_some_some hχ0, hχ]
      simp only [ite_true, neg_add_cancel, zero_mul, norm_zero]
      rw [show (-1 : ℂ) + (Fintype.card Y : ℂ)⁻¹ * (1 - -1 - -1) - -1 =
        ((3 / Fintype.card Y : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      field_simp
      ring
    · simp only [ha, ite_false, sub_zero]
      rw [show (1 : ℂ) + 1 = 2 by norm_num, norm_mul, mul_pow, phaseCell_comm χ a]
      norm_num
  rw [Finset.sum_congr rfl fun a _ ↦ hterm a, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_norm_phaseCell_sub_sq hχ0, hχ, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
  simp only [Complex.neg_re, Complex.one_re]
  field_simp
  ring

end sharpness

section sharpnessInstability

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

omit [Fintype X] [AddCommGroup Y] in
/-- **Sharpness of the constant `24`, the instability.** Labelling the databases by whether
`D x₀ = y₀` has instability at most `1 / N`: only the answer `y₀` at `x₀` changes the label. -/
theorem instability_decide_eq_some_le [Finite X] [Nonempty Y] [UniformAnswerMeasure (X →ₒ Y)]
    (x₀ : X) (y₀ : Y) (t : ℕ) :
    (Database.instability (fun D : Database X Y ↦ decide (D x₀ = some y₀)) t).toReal ≤
      1 / Fintype.card Y := by
  have := Fintype.ofFinite X
  have h : Database.instability (fun D : Database X Y ↦ decide (D x₀ = some y₀)) t ≤
      1 / Fintype.card Y := by
    rw [Database.instability_eq_iSup]
    refine iSup_le fun i ↦ iSup_le fun D ↦ iSup_le fun hi ↦ iSup_le fun _ ↦ iSup_le fun x ↦
      iSup_le fun hx ↦ ?_
    gcongr
    suffices hc : (Finset.univ.filter fun u : Y ↦
        decide (Function.update D x (some u) x₀ = some y₀) ≠ i).card ≤ 1 by exact_mod_cast hc
    refine (Finset.card_le_card fun u hu ↦ ?_).trans (Finset.card_singleton y₀).le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [Finset.mem_singleton]
    by_cases hxx : x = x₀
    · subst hxx
      subst hi
      simp only [hx, Function.update_self, Option.some.injEq, reduceCtorEq, decide_false,
        ne_eq, decide_eq_false_iff_not, not_not] at hu
      exact hu
    · subst hi
      exact absurd (by rw [Function.update_of_ne (Ne.symm hxx)]) hu
  have h' := ENNReal.toReal_mono (by simp) h
  simpa using h'

/-- **The constant `24` is optimal up to `36 / N`.** For `χ y₀ = -1` and `t ≥ 1`, the scalar
control `V = P_A - P_B` of the labelling by whether `D x₀ = y₀` satisfies
`(24 - 36 / N) I(π, t) ≤ ‖[V, O^(t)]‖²`. -/
theorem mul_instability_le_l2_opNorm_commutator_truncatedOracle_sq
    [UniformAnswerMeasure (X →ₒ Y)] (x₀ : X) {y₀ : Y} {χ : AddChar Y ℂ} (hχ : χ y₀ = -1) {t : ℕ}
    (ht : 1 ≤ t) :
    (24 - 36 / (Fintype.card Y : ℝ)) *
        (Database.instability (fun D : Database X Y ↦ decide (D x₀ = some y₀)) t).toReal ≤
      ‖labelControlled (fun m : (X × Y) × Database X Y ↦ decide (m.2 x₀ = some y₀))
            (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ)) * truncatedOracle X Y t -
          truncatedOracle X Y t *
            labelControlled (fun m : (X × Y) × Database X Y ↦ decide (m.2 x₀ = some y₀))
              (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ))‖ ^ 2 := by
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  have h2 : (2 : ℝ) ≤ Fintype.card Y := by
    have : 1 < Fintype.card Y := by
      by_contra h
      have hsub : Subsingleton Y := Fintype.card_le_one_iff_subsingleton.mp (not_lt.mp h)
      have : χ y₀ = 1 := by rw [Subsingleton.elim y₀ 0, AddChar.map_zero_eq_one]
      rw [this] at hχ
      norm_num at hχ
    exact_mod_cast this
  refine le_trans ?_ (le_l2_opNorm_commutator_truncatedOracle_sq x₀ hχ ht)
  have hc : 0 ≤ 24 - 36 / (Fintype.card Y : ℝ) := by
    rw [sub_nonneg, div_le_iff₀ hN]; linarith
  calc (24 - 36 / (Fintype.card Y : ℝ)) *
        (Database.instability (fun D : Database X Y ↦ decide (D x₀ = some y₀)) t).toReal
      ≤ (24 - 36 / (Fintype.card Y : ℝ)) * (1 / Fintype.card Y) :=
        mul_le_mul_of_nonneg_left (instability_decide_eq_some_le x₀ y₀ t) hc
    _ = 24 / (Fintype.card Y : ℝ) - 36 / (Fintype.card Y : ℝ) ^ 2 := by
        field_simp

/-- **Every constant below `24` fails.** For `χ y₀ = -1`, `t ≥ 1` and `0 ≤ c` with
`(24 - c) N > 36`, the scalar control of the labelling by whether `D x₀ = y₀` violates
`‖[V, O^(t)]‖² ≤ c I(π, t)`. -/
theorem mul_instability_lt_l2_opNorm_commutator_truncatedOracle_sq
    [UniformAnswerMeasure (X →ₒ Y)] (x₀ : X) {y₀ : Y} {χ : AddChar Y ℂ} (hχ : χ y₀ = -1) {t : ℕ}
    (ht : 1 ≤ t) {c : ℝ} (hc0 : 0 ≤ c) (hc : 36 < (24 - c) * Fintype.card Y) :
    c * (Database.instability (fun D : Database X Y ↦ decide (D x₀ = some y₀)) t).toReal <
      ‖labelControlled (fun m : (X × Y) × Database X Y ↦ decide (m.2 x₀ = some y₀))
            (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ)) * truncatedOracle X Y t -
          truncatedOracle X Y t *
            labelControlled (fun m : (X × Y) × Database X Y ↦ decide (m.2 x₀ = some y₀))
              (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ))‖ ^ 2 := by
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  refine lt_of_lt_of_le ?_ (le_l2_opNorm_commutator_truncatedOracle_sq x₀ hχ ht)
  have e : 24 / (Fintype.card Y : ℝ) - 36 / (Fintype.card Y : ℝ) ^ 2 - c * (1 / Fintype.card Y) =
      ((24 - c) * Fintype.card Y - 36) / (Fintype.card Y : ℝ) ^ 2 := by
    field_simp
    ring
  have hpos : 0 < ((24 - c) * Fintype.card Y - 36) / (Fintype.card Y : ℝ) ^ 2 :=
    div_pos (by linarith) (by positivity)
  calc c * (Database.instability (fun D : Database X Y ↦ decide (D x₀ = some y₀)) t).toReal
      ≤ c * (1 / Fintype.card Y) :=
        mul_le_mul_of_nonneg_left (instability_decide_eq_some_le x₀ y₀ t) hc0
    _ < 24 / (Fintype.card Y : ℝ) - 36 / (Fintype.card Y : ℝ) ^ 2 := by linarith

/-- **The constant `20` fails.** For `χ y₀ = -1`, `t ≥ 1` and `|Y| ≥ 10`, the scalar control of
the labelling by whether `D x₀ = y₀` violates `‖[V, O^(t)]‖² ≤ 20 I(π, t)`, the constant of
[CDHZ, Lemma 5.9] for the pinching. -/
theorem twenty_mul_instability_lt_l2_opNorm_commutator_truncatedOracle_sq
    [UniformAnswerMeasure (X →ₒ Y)] (x₀ : X) {y₀ : Y} {χ : AddChar Y ℂ} (hχ : χ y₀ = -1) {t : ℕ}
    (ht : 1 ≤ t) (hY : 10 ≤ Fintype.card Y) :
    20 * (Database.instability (fun D : Database X Y ↦ decide (D x₀ = some y₀)) t).toReal <
      ‖labelControlled (fun m : (X × Y) × Database X Y ↦ decide (m.2 x₀ = some y₀))
            (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ)) * truncatedOracle X Y t -
          truncatedOracle X Y t *
            labelControlled (fun m : (X × Y) × Database X Y ↦ decide (m.2 x₀ = some y₀))
              (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ))‖ ^ 2 := by
  have hN : (10 : ℝ) ≤ Fintype.card Y := by exact_mod_cast hY
  exact mul_instability_lt_l2_opNorm_commutator_truncatedOracle_sq x₀ hχ ht (by norm_num)
    (by linarith)

end sharpnessInstability

/-! ### Bit strings -/

section bitString

/-- The character `(-1) ^ b` of `ZMod 2`. -/
noncomputable def signChar : AddChar (ZMod 2) ℂ where
  toFun b := if b = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h a with rfl | rfl <;> rcases h b with rfl | rfl <;>
      simp [show (1 : ZMod 2) + 1 = 0 from rfl]

/-- The sign character is `-1` at `1`. -/
@[simp]
theorem signChar_one : signChar 1 = -1 := by
  simp [signChar]

/-- **Bit strings have a character with value `-1`.** On `Y = Fin (s + 1) → ZMod 2`, the
character `χ v = (-1) ^ (v 0)` takes the value `-1` at the indicator of `0`. -/
theorem exists_addChar_eq_neg_one_bitString (s : ℕ) :
    ∃ (χ : AddChar (Fin (s + 1) → ZMod 2) ℂ) (y₀ : Fin (s + 1) → ZMod 2), χ y₀ = -1 :=
  ⟨signChar.compAddMonoidHom (Pi.evalAddMonoidHom (fun _ ↦ ZMod 2) 0), Pi.single 0 1, by
    simp⟩

/-- **The constant `24` is optimal.** For every `0 ≤ c < 24`, every nonempty `X` and every query
bound `t ≥ 1`, there are bit strings `Y = Fin (s + 1) → ZMod 2`, a point `x₀` and an answer `y₀`
such that the scalar control of the labelling by whether `D x₀ = y₀` violates
`‖[V, O^(t)]‖² ≤ c I(π, t)`, for every uniform answer measure on `Y`. -/
theorem exists_mul_instability_lt_l2_opNorm_commutator_truncatedOracle_sq (X : Type) [Fintype X]
    [DecidableEq X] [Nonempty X] {t : ℕ} (ht : 1 ≤ t) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 24) :
    ∃ s : ℕ, ∀ [UniformAnswerMeasure (X →ₒ (Fin (s + 1) → ZMod 2))],
      ∃ (x₀ : X) (y₀ : Fin (s + 1) → ZMod 2),
        c * (Database.instability (fun D : Database X (Fin (s + 1) → ZMod 2) ↦
            decide (D x₀ = some y₀)) t).toReal <
          ‖labelControlled (fun m : (X × (Fin (s + 1) → ZMod 2)) ×
                Database X (Fin (s + 1) → ZMod 2) ↦ decide (m.2 x₀ = some y₀))
                (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ)) *
                truncatedOracle X (Fin (s + 1) → ZMod 2) t -
              truncatedOracle X (Fin (s + 1) → ZMod 2) t *
                labelControlled (fun m : (X × (Fin (s + 1) → ZMod 2)) ×
                  Database X (Fin (s + 1) → ZMod 2) ↦ decide (m.2 x₀ = some y₀))
                  (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ))‖ ^ 2 := by
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt (36 / (24 - c)) (by norm_num : (1 : ℝ) < 2)
  refine ⟨s, fun {_} ↦ ?_⟩
  obtain ⟨χ, y₀, hχ⟩ := exists_addChar_eq_neg_one_bitString s
  refine ⟨Classical.arbitrary X, y₀, ?_⟩
  refine mul_instability_lt_l2_opNorm_commutator_truncatedOracle_sq _ hχ ht hc0 ?_
  have h24 : 0 < 24 - c := by linarith
  have hcard : (Fintype.card (Fin (s + 1) → ZMod 2) : ℝ) = 2 ^ (s + 1) := by
    simp [ZMod.card]
  rw [div_lt_iff₀ h24] at hs
  rw [hcard]
  nlinarith [pow_succ (2 : ℝ) s, pow_pos (by norm_num : (0 : ℝ) < 2) s]

end bitString

end Quantum
