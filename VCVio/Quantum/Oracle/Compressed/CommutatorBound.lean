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
# The commutator bound for the truncated compressed oracle

Let `π` label the databases, so that `P^(i)` is the projector onto the databases of label `i`,
and let `I = I(π, t)` be the instability of `π` with query bound `t`
(`Quantum.Database.instability`, Definition 5.3 of Chiesa, Di, Hu and Zheng, *How to Prove
Post-Quantum Security for Succinct Non-Interactive Reductions*, ePrint 2025/2166, cited as [CDHZ]
below). This file proves, for the truncated compressed oracle `O^(t)`:

* **Lemma 5.9** (`Quantum.l2_opNorm_pinch_truncatedOracle_sub_sq_le`):
  `‖∑ i, P^(i) O^(t) P^(i) - O^(t)‖² ≤ 20 I`, with the paper's constant `20`. The phase-basis
  form is `Quantum.l2_opNorm_pinch_truncatedPhaseOracle_sub_sq_le`.
* **Lemma 5.10** (`Quantum.l2_opNorm_commutator_truncatedOracle_le_pinch`, after Chiesa, Manohar
  and Spooner, TCC 2019, Lemma 5.10): for a label-controlled unitary
  `V = ∑ i, P^(i) W_i` whose `W_i` preserve the labels and commute with `O^(t) ⊗ 1`,
  `‖[V, O^(t) ⊗ 1]‖ ≤ 2 ‖∑ i, P^(i) O^(t) P^(i) - O^(t)‖`.
* **Theorem 5.4** (`Quantum.l2_opNorm_commutator_truncatedOracle_sq_le`):
  `‖[V, O^(t) ⊗ 1]‖² ≤ 80 I`.
* **Corollary 5.6** (`Quantum.l2_opNorm_commutator_purifiedMeasurement_sq_le`): the bound for the
  purified measurement `V = ∑ i, P^(i) ⊗ U_i` with any unitaries `U_i` on a separate register `B`,
  and its XOR instance `Quantum.l2_opNorm_commutator_xorMeasurement_sq_le`, which records the
  label in `B` by `|b⟩ ↦ |b + i⟩` (as in Don, Fehr, Majenz and Schaffner, EUROCRYPT 2022,
  Thm 3.1).

`∑ i, P^(i) A P^(i)` is the pinching `Matrix.pinch β A` of `A` by the labelling
`β ((x, y), D) = π D` (`Matrix.pinch_eq_sum`).

## Proof of Lemma 5.9

By equation (4) the standard and phase forms have the same norm, and in the phase basis the
operator `Δ = pinch O_ph^(t) - O_ph^(t)` is block diagonal: its entry at `((x', χ'), D')`,
`((x, χ), D)` vanishes unless `(x', χ') = (x, χ)` and `D'`, `D` agree off `x`. A block is therefore
given by `(x, χ)` and a database `r` with `r x = ⊥`, and is indexed by the content `a` of the cell
`x`. When `|r| < t` the truncation keeps the whole block, and the entries of the block of `Δ` are
`-[π r[x ↦ a'] ≠ π r[x ↦ a]] C a' a`, with `C = Quantum.phaseCell Y χ`. When `|r| ≥ t` every
filled content `r[x ↦ u]` has more than `t` entries, so of the block of `O_ph^(t)` at most the
empty-to-empty entry, from `r` to `r`, survives. Pinching keeps that entry, so the block of `Δ`
vanishes. Lemma 4.5 gives the entries of `C` for `χ ≠ 0`: `0` at `(⊥, ⊥)`, of square norm `1 / N`
between `⊥` and `y`, and of square norm at most `9 / N²` between distinct `u` and `w`. Writing
`B` for the answers `u` with `π r[x ↦ u] ≠ π r`, the squared entries of the block of `Δ` sum to at
most `|B| / N + |B| / N + 18 |B| / N = 20 |B| / N ≤ 20 I` (`Quantum.sum_phaseCell_sq_le`), and the
block Frobenius bound `Matrix.l2_opNorm_le_of_blocks` concludes.

The decomposition in the proof of [CDHZ, Lemma 5.9] treats inputs with `|D| = t` as acquiring
only a phase. For a filled queried cell and `χ ≠ 0`, `O_ph^(t)` also produces the `t − 1` and
resized terms of Lemma 4.5, since every database it reaches has at most `t` entries (for example
`X = Unit`, `Y = ZMod 2`, `t = 1`). The proof here uses the block decomposition above instead; the
bound `20 I(π, t)` and the constant are unchanged.

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

/-! ## The squared entries of a block of the phase cell -/

section cell

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

omit [DecidableEq Y] [AddCommGroup Y] in
theorem norm_cellAmp_sq : ‖cellAmp Y‖ ^ 2 = (Fintype.card Y : ℝ)⁻¹ := by
  rw [sq, ← norm_mul, cellAmp_mul_self, norm_inv, Complex.norm_natCast]

/-- **The block estimate of Lemma 5.9.** For a labelling `κ` of the contents of one cell, the
squared entries of the phase cell between contents of different labels sum to at most
`20 |B| / N`, where `B` is the set of answers `u` with `κ u ≠ κ ⊥`. -/
theorem sum_phaseCell_sq_le {ι : Type*} [DecidableEq ι] (χ : AddChar Y ℂ) (κ : Option Y → ι) :
    ∑ a', ∑ a, (if κ a' = κ a then 0 else ‖phaseCell Y χ a' a‖ ^ 2) ≤
      20 * ((Finset.univ.filter fun u ↦ κ (some u) ≠ κ none).card / Fintype.card Y : ℝ) := by
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Fintype.card Y := ⟨_, rfl⟩
  have hN : 0 < N := hNdef ▸ Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨e, he⟩ : ∃ e : Y → ℝ, e = fun u ↦ if κ (some u) ≠ κ none then 1 else 0 := ⟨_, rfl⟩
  have he0 : ∀ u, 0 ≤ e u := fun u ↦ by rw [he]; beta_reduce; split_ifs <;> norm_num
  have hb : ((Finset.univ.filter fun u ↦ κ (some u) ≠ κ none).card : ℝ) = ∑ u, e u := by
    rw [he, Finset.sum_boole]
  rw [hb, ← hNdef]
  by_cases hχ : χ = 0
  · have h0 : ∀ a' a, (if κ a' = κ a then 0 else ‖phaseCell Y χ a' a‖ ^ 2) = 0 := by
      intro a' a
      by_cases h : a' = a
      · subst h
        simp
      · rw [hχ, phaseCell_zero, one_apply_ne h]
        simp
    simp only [h0, Finset.sum_const_zero]
    exact mul_nonneg (by norm_num) (div_nonneg (Finset.sum_nonneg fun u _ ↦ he0 u) hN.le)
  have hamp : ‖cellAmp Y‖ ^ 2 = N⁻¹ := by rw [norm_cellAmp_sq, hNdef]
  have h2 : ∀ w, (if κ none = κ (some w) then 0 else ‖phaseCell Y χ none (some w)‖ ^ 2) ≤
      e w * N⁻¹ := by
    intro w
    rw [phaseCell_none_some hχ, norm_mul, AddChar.norm_apply, mul_one, hamp, he]
    by_cases h : κ none = κ (some w)
    · simp [h]
    · simp [h, Ne.symm h]
  have h3 : ∀ u, (if κ (some u) = κ none then 0 else ‖phaseCell Y χ (some u) none‖ ^ 2) ≤
      e u * N⁻¹ := by
    intro u
    rw [phaseCell_some_none hχ, norm_mul, AddChar.norm_apply, mul_one, hamp, he]
    by_cases h : κ (some u) = κ none
    · simp [h]
    · simp [h]
  have h4 : ∀ u w, (if κ (some u) = κ (some w) then 0 else
      ‖phaseCell Y χ (some u) (some w)‖ ^ 2) ≤ (e u + e w) * (9 * (N⁻¹ * N⁻¹)) := by
    intro u w
    by_cases h : κ (some u) = κ (some w)
    · simp only [h, ↓reduceIte]
      exact mul_nonneg (add_nonneg (he0 u) (he0 w)) (by positivity)
    simp only [h, ↓reduceIte]
    have huw : u ≠ w := fun huw ↦ h (huw ▸ rfl)
    have hsum : 1 ≤ e u + e w := by
      rw [he]
      by_cases hu : κ (some u) = κ none
      · have hw : κ (some w) ≠ κ none := fun hw ↦ h (hu.trans hw.symm)
        simp [hu, hw]
      · simp only [ne_eq, hu, not_false_eq_true, ↓reduceIte]
        split_ifs <;> norm_num
    have hC : ‖phaseCell Y χ (some u) (some w)‖ ≤ 3 * N⁻¹ := by
      rw [phaseCell_some_some hχ]
      simp only [huw, ↓reduceIte, zero_add]
      rw [norm_mul, norm_inv, Complex.norm_natCast, ← hNdef]
      have h3' : ‖(1 : ℂ) - χ u - χ w‖ ≤ 3 := by
        calc ‖(1 : ℂ) - χ u - χ w‖ ≤ ‖(1 : ℂ) - χ u‖ + ‖χ w‖ := norm_sub_le _ _
          _ ≤ ‖(1 : ℂ)‖ + ‖χ u‖ + ‖χ w‖ := by gcongr; exact norm_sub_le _ _
          _ = 3 := by rw [norm_one, AddChar.norm_apply, AddChar.norm_apply]; norm_num
      calc N⁻¹ * ‖(1 : ℂ) - χ u - χ w‖ ≤ N⁻¹ * 3 := by gcongr
        _ = 3 * N⁻¹ := by ring
    calc ‖phaseCell Y χ (some u) (some w)‖ ^ 2 ≤ (3 * N⁻¹) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hC 2
      _ = 1 * (9 * (N⁻¹ * N⁻¹)) := by ring
      _ ≤ (e u + e w) * (9 * (N⁻¹ * N⁻¹)) := by gcongr
  have hA : ∀ u, ∑ w, (e u + e w) * (9 * (N⁻¹ * N⁻¹)) =
      (N * e u + ∑ w, e w) * (9 * (N⁻¹ * N⁻¹)) := fun u ↦ by
    rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← hNdef]
  rw [Fintype.sum_option]
  simp only [Fintype.sum_option]
  calc _ ≤ ((0 : ℝ) + ∑ w, e w * N⁻¹) +
        ∑ u, (e u * N⁻¹ + ∑ w, (e u + e w) * (9 * (N⁻¹ * N⁻¹))) :=
        add_le_add (add_le_add (by simp) (Finset.sum_le_sum fun w _ ↦ h2 w))
          (Finset.sum_le_sum fun u _ ↦
            add_le_add (h3 u) (Finset.sum_le_sum fun w _ ↦ h4 u w))
    _ = 20 * ((∑ u, e u) / N) := by
        simp only [hA]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hNdef]
        field_simp
        ring

end cell

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

end phaseBlock

/-! ## Lemma 5.9 -/

section lemma59

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [UniformAnswerMeasure (X →ₒ Y)] {ι : Type*} [DecidableEq ι]

/-- **Lemma 5.9 of ePrint 2025/2166, phase basis.** Pinching the truncated phase oracle by the
labels of the databases moves it by at most `√(20 I)` in operator norm. -/
theorem l2_opNorm_pinch_truncatedPhaseOracle_sub_sq_le (π : Database X Y → ι) (t : ℕ) :
    ‖pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) (truncatedPhaseOracle X Y t) -
        truncatedPhaseOracle X Y t‖ ^ 2 ≤ 20 * (Database.instability π t).toReal := by
  have hI : 0 ≤ (Database.instability π t).toReal := ENNReal.toReal_nonneg
  have hΔ : ∀ m' m, (pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2)
      (truncatedPhaseOracle X Y t) - truncatedPhaseOracle X Y t) m' m =
        if π m'.2 = π m.2 then 0 else -truncatedPhaseOracle X Y t m' m := by
    intro m' m
    rw [Matrix.sub_apply, pinch_apply]
    split_ifs <;> simp
  have hΔ0 : ∀ m' m, (pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2)
      (truncatedPhaseOracle X Y t) - truncatedPhaseOracle X Y t) m' m ≠ 0 →
        truncatedPhaseOracle X Y t m' m ≠ 0 := by
    intro m' m h h0
    rw [hΔ, h0] at h
    simp at h
  have key : ‖pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2)
      (truncatedPhaseOracle X Y t) - truncatedPhaseOracle X Y t‖ ≤
        √(20 * (Database.instability π t).toReal) := by
    refine l2_opNorm_le_of_blocks
      (fun m : (X × AddChar Y ℂ) × Database X Y ↦ (m.1, Function.update m.2 m.1.1 none))
      (fun m : (X × AddChar Y ℂ) × Database X Y ↦ (m.1, Function.update m.2 m.1.1 none))
      (fun m' m h ↦ phaseBlock_eq_of_truncatedPhaseOracle_ne_zero (hΔ0 m' m h))
      (Real.sqrt_nonneg _) ?_
    rintro ⟨⟨x, χ⟩, D₀⟩
    rw [Real.sq_sqrt (by positivity)]
    dsimp only
    set r := Function.update D₀ x none with hrdef
    have hr : r x = none := Function.update_self x none D₀
    have hblk : ∀ a, Function.update (Function.update r x a) x none = r := fun a ↦ by
      rw [Function.update_idem, Database.update_none_of_eq_none hr]
    rw [sum_ite_phaseBlock x χ hr]
    have hrow : ∀ a', ∑ m, ‖(pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2)
        (truncatedPhaseOracle X Y t) - truncatedPhaseOracle X Y t)
          ((x, χ), Function.update r x a') m‖ ^ 2 =
        ∑ a, ‖(pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2)
          (truncatedPhaseOracle X Y t) - truncatedPhaseOracle X Y t)
            ((x, χ), Function.update r x a') ((x, χ), Function.update r x a)‖ ^ 2 := by
      intro a'
      refine Eq.trans ?_ (sum_ite_phaseBlock x χ hr fun m ↦
        ‖(pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2)
          (truncatedPhaseOracle X Y t) - truncatedPhaseOracle X Y t)
            ((x, χ), Function.update r x a') m‖ ^ 2)
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      split_ifs with h
      · rfl
      · have h0 : (pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2)
            (truncatedPhaseOracle X Y t) - truncatedPhaseOracle X Y t)
              ((x, χ), Function.update r x a') m = 0 := by
          by_contra hne
          have hb := phaseBlock_eq_of_truncatedPhaseOracle_ne_zero (hΔ0 _ _ hne)
          simp only [hblk] at hb
          exact h hb.symm
        rw [h0, norm_zero]
        norm_num
    simp only [hrow]
    have hentry : ∀ a' a, ‖(pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2)
        (truncatedPhaseOracle X Y t) - truncatedPhaseOracle X Y t)
          ((x, χ), Function.update r x a') ((x, χ), Function.update r x a)‖ ^ 2 =
        if π (Function.update r x a') = π (Function.update r x a) then 0 else
          ‖(if Database.size (Function.update r x a') ≤ t then (1 : ℂ) else 0) *
              phaseCell Y χ a' a *
                (if Database.size (Function.update r x a) ≤ t then 1 else 0)‖ ^ 2 := by
      intro a' a
      rw [hΔ, truncatedPhaseOracle_apply, phaseOracle_apply]
      have hcond : (x, χ) = (x, χ) ∧
          ∀ j ≠ x, Function.update r x a' j = Function.update r x a j :=
        ⟨rfl, fun j hj ↦ by rw [Function.update_of_ne hj, Function.update_of_ne hj]⟩
      rw [ite_eq_left hcond, Function.update_self, Function.update_self]
      split_ifs <;> simp
    simp only [hentry]
    by_cases hsize : Database.size r < t
    · have hmask : ∀ a, Database.size (Function.update r x a) ≤ t := fun a ↦
        (Database.size_update_le r x a).trans hsize
      simp only [hmask, ↓reduceIte, one_mul, mul_one]
      refine (sum_phaseCell_sq_le χ (fun a ↦ π (Function.update r x a))).trans ?_
      gcongr
      have hc := Database.card_div_le_instability π hsize hr
      simpa only [Database.update_none_of_eq_none hr] using hc
    · have h0 : ∀ a' a, (if π (Function.update r x a') = π (Function.update r x a) then 0 else
          ‖(if Database.size (Function.update r x a') ≤ t then (1 : ℂ) else 0) *
              phaseCell Y χ a' a *
                (if Database.size (Function.update r x a) ≤ t then 1 else 0)‖ ^ 2) = 0 := by
        have hbig : ∀ u : Y, ¬ Database.size (Function.update r x (some u)) ≤ t := fun u ↦ by
          rw [Database.size_update_some_of_eq_none hr]
          omega
        rintro (_ | u') (_ | u)
        · simp
        · simp [hbig]
        · simp [hbig]
        · simp [hbig]
      simp only [h0, Finset.sum_const_zero]
      positivity
  calc _ ≤ √(20 * (Database.instability π t).toReal) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) key 2
    _ = 20 * (Database.instability π t).toReal := Real.sq_sqrt (by positivity)

/-- **Lemma 5.9 of ePrint 2025/2166.** Pinching the truncated compressed oracle by the labels of
the databases, `∑ i, P^(i) O^(t) P^(i)`, moves it by at most `√(20 I)` in operator norm:
`‖∑ i, P^(i) O^(t) P^(i) - O^(t)‖² ≤ 20 I(π, t)`. -/
theorem l2_opNorm_pinch_truncatedOracle_sub_sq_le (π : Database X Y → ι) (t : ℕ) :
    ‖pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) -
        truncatedOracle X Y t‖ ^ 2 ≤ 20 * (Database.instability π t).toReal := by
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
  exact (pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_conjTranspose_mul_mul_le
    (queryFourier_mul_conjTranspose X Y) _) 2).trans
    (l2_opNorm_pinch_truncatedPhaseOracle_sub_sq_le π t)

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

/-! ## Theorem 5.4 and Corollary 5.6 -/

section theorem54

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [UniformAnswerMeasure (X →ₒ Y)] {ι : Type*} {E : Type*} [Fintype E] [DecidableEq E]

/-- **Theorem 5.4 of ePrint 2025/2166.** Let `W i` be unitaries on the joint register
`((X × Y) × Database X Y) × E` that preserve the label `π D` of the database and commute with
`O^(t) ⊗ 1_E`. The label-controlled unitary `V = ∑ i, P^(i) W i` almost commutes with the
truncated compressed oracle: `‖[V, O^(t) ⊗ 1_E]‖² ≤ 80 I(π, t)`. -/
theorem l2_opNorm_commutator_truncatedOracle_sq_le (π : Database X Y → ι) (t : ℕ)
    {W : ι → Matrix (((X × Y) × Database X Y) × E) (((X × Y) × Database X Y) × E) ℂ}
    (hW : ∀ k a b, W k a b ≠ 0 → π a.1.2 = π b.1.2) (hU : ∀ k, W k ∈ unitaryGroup _ ℂ)
    (hA : ∀ k, W k * (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) =
      (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) * W k) :
    ‖labelControlled (fun a ↦ π a.1.2) W * (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) * labelControlled (fun a ↦ π a.1.2) W‖ ^ 2
      ≤ 80 * (Database.instability π t).toReal := by
  classical
  have h₁ := l2_opNorm_commutator_truncatedOracle_le_pinch π t hW hU hA
  have h₂ := l2_opNorm_pinch_truncatedOracle_sub_sq_le π t
  calc _ ≤ (2 * ‖pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) -
          truncatedOracle X Y t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    _ = 4 * ‖pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) -
          truncatedOracle X Y t‖ ^ 2 := by ring
    _ ≤ 4 * (20 * (Database.instability π t).toReal) := by gcongr
    _ = 80 * (Database.instability π t).toReal := by ring

/-- **Corollary 5.6 of ePrint 2025/2166.** The purified measurement of the label of the database
into a register `B`, `V = ∑ i, P^(i) ⊗ U i` with any unitaries `U i` on `B`, almost commutes with
the truncated compressed oracle: `‖[V, O^(t) ⊗ 1_B]‖² ≤ 80 I(π, t)`. -/
theorem l2_opNorm_commutator_purifiedMeasurement_sq_le (π : Database X Y → ι) (t : ℕ)
    {U : ι → Matrix E E ℂ} (hU : ∀ i, U i ∈ unitaryGroup E ℂ) :
    ‖labelControlled (fun a ↦ π a.1.2)
          (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ U i) *
          (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) *
          labelControlled (fun a ↦ π a.1.2)
            (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ U i)‖ ^ 2
      ≤ 80 * (Database.instability π t).toReal := by
  refine l2_opNorm_commutator_truncatedOracle_sq_le π t ?_ ?_ ?_
  · intro k a b h
    have hab : a.1 = b.1 := by
      by_contra hne
      simp [kroneckerMap_apply, one_apply_ne hne] at h
    rw [hab]
  · intro k
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one,
      ← mul_kronecker_mul, Matrix.one_mul, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff.mp (hU k), one_kronecker_one]
  · intro k
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
      Matrix.one_mul]

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

/-- **Corollary 5.6 of ePrint 2025/2166, XOR form.** Measuring the label `π D ∈ B` of the database
by XORing it into a register `B` almost commutes with the truncated compressed oracle:
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

end Quantum
