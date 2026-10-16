/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.MatrixMap.ProjectorPair
public import VCVio.Quantum.Oracle.Compressed.Basic

/-!
# Consistency projectors and their compressed conjugates

A list `io : List (ι × Y)` of prescribed input-output pairs defines the projector
`Quantum.checkProjector io` on the database register `Database ι Y`: the diagonal projector onto
the databases that hold every prescribed output at its input. Its conjugate by the compression of
every cell, `P̂ = F P F` with `F = Quantum.compressAll ι Y`, is the projector onto the
superposition oracles whose function satisfies the prescription
(`Quantum.compressedCheckProjector io`).

Write `d` for the number of distinct prescribed inputs and `N = |Y|`. The one-cell compression has
diagonal entry `1 - 1/N` at every value, and both projectors act cell by cell, so
`P P̂ P = α² P` and `P̂ P P̂ = α² P̂` with `α = (1 - 1/N)^d`, for every list. When the list is
consistent (no input with two different outputs), `P ≠ 0` and the two projectors are in a fixed
angle, so their distance is exact:
`‖P̂ - P‖² = 1 - (1 - 1/N)^(2d) ≤ 2d/N`
(`Quantum.l2_opNorm_compressedCheckProjector_sub_sq`). When it is inconsistent, both projectors are
zero.

This is eq. (26) of the notes on Chiesa, Di, Hu and Zheng, *How to Prove Post-Quantum Security
for Succinct Non-Interactive Reductions* (ePrint 2025/2166), and sharpens their Lemma 9.5
(pp. 60–61), which states `‖P̂ - P‖ ≤ 2√(d/N)`; that bound is the corollary
`Quantum.l2_opNorm_compressedCheckProjector_sub_le_two_mul_sqrt`.

## Main definitions

* `Quantum.ConsistentIO io`: no input is prescribed two different outputs.
* `Quantum.checkProjector io`: the projector onto the databases that satisfy `io`.
* `Quantum.compressedCheckProjector io`: its conjugate by `Quantum.compressAll ι Y`.

## Main results

* `Quantum.checkProjector_mul_compressedCheckProjector_mul_checkProjector`: `P P̂ P = α² P`.
* `Quantum.compressedCheckProjector_mul_checkProjector_mul_compressedCheckProjector`:
  `P̂ P P̂ = α² P̂`.
* `Quantum.piKron_checkProjector_mul_piKron_compressedCheckProjector_mul`: the same identity for
  prescriptions on several databases, with `d` the total number of prescribed cells.
* `Quantum.l2_opNorm_compressedCheckProjector_sub_sq`: the exact distance for a consistent list.
* `Quantum.checkProjector_eq_zero_of_not_consistentIO`,
  `Quantum.compressedCheckProjector_eq_zero_of_not_consistentIO`: the inconsistent case.
* `Quantum.l2_opNorm_compressedCheckProjector_sub_sq_le`: `‖P̂ - P‖² ≤ 2d/N` for every list.
* `Quantum.l2_opNorm_compressedCheckProjector_sub_le_two_mul_sqrt`: Lemma 9.5 of the paper.
-/

public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Quantum

variable {ι Y : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]

/-! ## The projectors -/

/-- A list of prescribed input-output pairs is consistent when no input is prescribed two different
outputs. -/
@[expose]
def ConsistentIO (io : List (ι × Y)) : Prop :=
  ∀ p ∈ io, ∀ q ∈ io, p.1 = q.1 → p.2 = q.2

omit [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] in
/-- The empty prescription is consistent. -/
@[simp]
theorem consistentIO_nil : ConsistentIO ([] : List (ι × Y)) := by
  simp [ConsistentIO]

omit [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] in
/-- A single input-output pair is consistent. -/
@[simp]
theorem consistentIO_singleton (p : ι × Y) : ConsistentIO [p] := by
  intro q hq r hr _
  rw [List.mem_singleton.mp hq, List.mem_singleton.mp hr]

/-- The set of prescribed inputs of a list of input-output pairs. -/
@[expose]
def ioCells (io : List (ι × Y)) : Finset ι :=
  (io.map Prod.fst).toFinset

omit [Fintype ι] [Fintype Y] [DecidableEq Y] in
/-- An input is prescribed exactly when some pair of the list has it as input. -/
theorem mem_ioCells {io : List (ι × Y)} {i : ι} : i ∈ ioCells io ↔ ∃ p ∈ io, p.1 = i := by
  simp [ioCells]

variable (Y) in
/-- The projector onto the databases that hold every prescribed output at its input: the diagonal
matrix with entry `1` at the databases `D` with `D x = some y` for every `(x, y) ∈ io`. -/
@[expose]
noncomputable def checkProjector (io : List (ι × Y)) : Matrix (Database ι Y) (Database ι Y) ℂ :=
  diagonal fun D ↦ if ∀ p ∈ io, D p.1 = some p.2 then 1 else 0

/-- The conjugate `F P F` of the consistency projector by the compression of every cell: the
projector onto the superposition oracles whose function satisfies the prescription. -/
@[expose]
noncomputable def compressedCheckProjector (io : List (ι × Y)) :
    Matrix (Database ι Y) (Database ι Y) ℂ :=
  compressAll ι Y * checkProjector Y io * compressAll ι Y

/-- The entries of the consistency projector: `1` on the diagonal at the databases that hold every
prescribed output, `0` elsewhere. -/
theorem checkProjector_apply (io : List (ι × Y)) (D D' : Database ι Y) :
    checkProjector Y io D D' = if D = D' ∧ ∀ p ∈ io, D p.1 = some p.2 then 1 else 0 := by
  rw [checkProjector, diagonal_apply]
  by_cases hD : D = D'
  · subst hD
    simp only [true_and, ↓reduceIte]
  · simp only [hD, false_and, ↓reduceIte]

/-- The consistency projector is Hermitian. -/
theorem conjTranspose_checkProjector (io : List (ι × Y)) :
    (checkProjector Y io)ᴴ = checkProjector Y io := by
  rw [checkProjector, diagonal_conjTranspose]
  congr 1
  funext D
  simp only [Pi.star_apply]
  split_ifs <;> simp only [star_one, star_zero]

/-- The consistency projector is idempotent. -/
theorem checkProjector_mul_self (io : List (ι × Y)) :
    checkProjector Y io * checkProjector Y io = checkProjector Y io := by
  rw [checkProjector, diagonal_mul_diagonal]
  congr 1
  funext D
  split_ifs <;> simp only [mul_one, mul_zero]

/-- The empty prescription is satisfied by every database. -/
@[simp]
theorem checkProjector_nil : checkProjector Y ([] : List (ι × Y)) = 1 := by
  simp [checkProjector]

/-- An inconsistent prescription is satisfied by no database. -/
theorem checkProjector_eq_zero_of_not_consistentIO {io : List (ι × Y)} (h : ¬ ConsistentIO io) :
    checkProjector Y io = 0 := by
  simp only [ConsistentIO, not_forall] at h
  obtain ⟨p, hp, q, hq, hpq, hne⟩ := h
  rw [checkProjector, diagonal_eq_zero]
  funext D
  rw [ite_eq_right]
  · rfl
  · intro hD
    have h₁ := hD p hp
    have h₂ := hD q hq
    rw [hpq, h₂] at h₁
    exact hne (Option.some_injective _ h₁).symm

/-- A consistent prescription is satisfied by some database, so its projector is not zero. -/
theorem checkProjector_ne_zero {io : List (ι × Y)} (h : ConsistentIO io) :
    checkProjector Y io ≠ 0 := by
  classical
  let D₀ : Database ι Y := fun i ↦
    if hi : ∃ p ∈ io, p.1 = i then some (Classical.choose hi).2 else none
  have hD₀ : ∀ p ∈ io, D₀ p.1 = some p.2 := by
    intro p hp
    have hi : ∃ q ∈ io, q.1 = p.1 := ⟨p, hp, rfl⟩
    simp only [D₀, dite_eq_left hi]
    obtain ⟨hq, hq₁⟩ := Classical.choose_spec hi
    rw [h _ hq p hp hq₁]
  intro h0
  have := congrFun (congrFun h0 D₀) D₀
  rw [checkProjector_apply, ite_eq_left ⟨rfl, hD₀⟩] at this
  exact one_ne_zero this

section compress

variable [Nonempty Y]

omit [Nonempty Y] in
/-- The compressed consistency projector is Hermitian. -/
theorem conjTranspose_compressedCheckProjector (io : List (ι × Y)) :
    (compressedCheckProjector io)ᴴ = compressedCheckProjector io := by
  rw [compressedCheckProjector, conjTranspose_mul, conjTranspose_mul, conjTranspose_compressAll,
    conjTranspose_checkProjector, Matrix.mul_assoc]

/-- The compressed consistency projector is idempotent. -/
theorem compressedCheckProjector_mul_self (io : List (ι × Y)) :
    compressedCheckProjector io * compressedCheckProjector io = compressedCheckProjector io := by
  simp only [compressedCheckProjector]
  rw [show compressAll ι Y * checkProjector Y io * compressAll ι Y *
      (compressAll ι Y * checkProjector Y io * compressAll ι Y) =
      compressAll ι Y * checkProjector Y io * (compressAll ι Y * compressAll ι Y) *
        checkProjector Y io * compressAll ι Y by simp only [Matrix.mul_assoc],
    compressAll_mul_self, Matrix.mul_one, Matrix.mul_assoc (compressAll ι Y),
    checkProjector_mul_self]

/-- The empty prescription has compressed projector the identity. -/
@[simp]
theorem compressedCheckProjector_nil : compressedCheckProjector ([] : List (ι × Y)) = 1 := by
  rw [compressedCheckProjector, checkProjector_nil, Matrix.mul_one, compressAll_mul_self]

omit [Nonempty Y] in
/-- An inconsistent prescription has zero compressed projector. -/
theorem compressedCheckProjector_eq_zero_of_not_consistentIO {io : List (ι × Y)}
    (h : ¬ ConsistentIO io) : compressedCheckProjector io = 0 := by
  rw [compressedCheckProjector, checkProjector_eq_zero_of_not_consistentIO h, Matrix.mul_zero,
    Matrix.zero_mul]

end compress

/-! ## The cell-by-cell computation -/

variable (Y) in
/-- The constraint that a prescription puts on the cell `i`: the diagonal projector onto the cell
values `u` with `u = some y` for every `(i, y) ∈ io`. -/
@[expose]
noncomputable def cellCheckProjector (io : List (ι × Y)) (i : ι) : Matrix (Option Y) (Option Y) ℂ :=
  diagonal fun u ↦ if ∀ p ∈ io, p.1 = i → u = some p.2 then 1 else 0

/-- The consistency projector is the pi-tensor product of the cell constraints. -/
theorem checkProjector_eq_piKron (io : List (ι × Y)) :
    checkProjector Y io = piKron (cellCheckProjector Y io) := by
  ext D D'
  rw [checkProjector_apply, piKron_apply]
  simp only [cellCheckProjector, diagonal_apply]
  by_cases hD : D = D'
  · subst hD
    simp only [true_and, ↓reduceIte]
    rw [Fintype.prod_boole]
    congr 1
    exact propext ⟨fun h i p hp hpi ↦ hpi ▸ h p hp, fun h p hp ↦ h p.1 p hp rfl⟩
  · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h.1 hD)]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hD
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

/-- A diagonal projector `q` onto at most one value `some y` of a cell satisfies
`q F q = (1 - 1/N) q`: the one-cell compression has diagonal entry `1 - 1/N` at every value. -/
theorem diagonal_mul_cellCompress_mul_diagonal {R : Option Y → Prop} [DecidablePred R] {y : Y}
    (hR : ∀ u, R u → u = some y) :
    diagonal (fun u ↦ if R u then (1 : ℂ) else 0) * cellCompress Y *
        diagonal (fun u ↦ if R u then (1 : ℂ) else 0) =
      (1 - (Fintype.card Y : ℂ)⁻¹) • diagonal (fun u ↦ if R u then (1 : ℂ) else 0) := by
  ext u v
  simp only [diagonal_mul, mul_diagonal, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  by_cases hu : R u
  · by_cases hv : R v
    · obtain rfl := hR u hu
      obtain rfl := hR v hv
      simp [hu]
    · have huv : u ≠ v := fun h ↦ hv (h ▸ hu)
      simp [hu, hv, huv]
  · simp [hu]

/-- On a prescribed cell, the constraint `q` satisfies `q F q = (1 - 1/N) q`: it projects onto at
most one value, where the one-cell compression has diagonal entry `1 - 1/N`. -/
theorem cellCheckProjector_mul_cellCompress_mul_self {io : List (ι × Y)} {i : ι}
    (hi : i ∈ ioCells io) :
    cellCheckProjector Y io i * cellCompress Y * cellCheckProjector Y io i =
      (1 - (Fintype.card Y : ℂ)⁻¹) • cellCheckProjector Y io i := by
  obtain ⟨p₀, hp₀, hp₀i⟩ := mem_ioCells.mp hi
  exact diagonal_mul_cellCompress_mul_diagonal fun u hu ↦ hu p₀ hp₀ hp₀i

/-- Off the prescribed cells, the constraint is the identity. -/
theorem cellCheckProjector_of_notMem {io : List (ι × Y)} {i : ι} (hi : i ∉ ioCells io) :
    cellCheckProjector Y io i = 1 := by
  have h : ∀ u : Option Y, ∀ p ∈ io, p.1 = i → u = some p.2 :=
    fun u p hp hpi ↦ absurd (mem_ioCells.mpr ⟨p, hp, hpi⟩) hi
  rw [cellCheckProjector, ← diagonal_one]
  exact congrArg diagonal (funext fun u ↦ ite_eq_left (h u))

/-- The scalar `q F q F q = s q` of one cell: `(1 - 1/N)²` on a prescribed cell, `1` elsewhere. -/
theorem cellCheckProjector_conj_eq [Nonempty Y] (io : List (ι × Y)) (i : ι) :
    cellCheckProjector Y io i * cellCompress Y * cellCheckProjector Y io i * cellCompress Y *
        cellCheckProjector Y io i =
      (if i ∈ ioCells io then (1 - (Fintype.card Y : ℂ)⁻¹) ^ 2 else 1) •
        cellCheckProjector Y io i := by
  split_ifs with hi
  · rw [cellCheckProjector_mul_cellCompress_mul_self hi, smul_mul_assoc, smul_mul_assoc,
      cellCheckProjector_mul_cellCompress_mul_self hi, smul_smul, sq]
  · rw [cellCheckProjector_of_notMem hi, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one,
      cellCompress_mul_self, one_smul]

omit [DecidableEq ι] in
/-- A pi-tensor product of scaled operators is the product of the scalars times the pi-tensor
product. -/
theorem piKron_smul {Z : Type*} (s : ι → ℂ) (A : ι → Matrix Z Z ℂ) :
    piKron (fun i ↦ s i • A i) = (∏ i, s i) • piKron A := by
  ext D D'
  simp [piKron_apply, Finset.prod_mul_distrib]

variable [Nonempty Y]

/-- `P P̂ P = α² P` with `α = (1 - 1/N)^d`, for every prescription. -/
theorem checkProjector_mul_compressedCheckProjector_mul_checkProjector (io : List (ι × Y)) :
    checkProjector Y io * compressedCheckProjector io * checkProjector Y io =
      ((1 - (Fintype.card Y : ℂ)⁻¹) ^ (2 * (ioCells io).card)) • checkProjector Y io := by
  rw [compressedCheckProjector, checkProjector_eq_piKron, compressAll]
  simp only [← Matrix.mul_assoc, piKron_mul]
  simp_rw [cellCheckProjector_conj_eq, piKron_smul]
  congr 1
  rw [Fintype.prod_ite_mem, Finset.prod_const, ← pow_mul]

/-- `P̂ P P̂ = α² P̂` with `α = (1 - 1/N)^d`, for every prescription. -/
theorem compressedCheckProjector_mul_checkProjector_mul_compressedCheckProjector
    (io : List (ι × Y)) :
    compressedCheckProjector io * checkProjector Y io * compressedCheckProjector io =
      ((1 - (Fintype.card Y : ℂ)⁻¹) ^ (2 * (ioCells io).card)) •
        compressedCheckProjector io := by
  have h := checkProjector_mul_compressedCheckProjector_mul_checkProjector io
  calc compressedCheckProjector io * checkProjector Y io * compressedCheckProjector io
      = compressAll ι Y * (checkProjector Y io * compressedCheckProjector io *
          checkProjector Y io) * compressAll ι Y := by
        simp only [compressedCheckProjector, ← Matrix.mul_assoc]
    _ = _ := by
        rw [h, Matrix.mul_smul, Matrix.smul_mul, compressedCheckProjector]

/-! ## Several databases -/

omit [Fintype ι] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- A list prescribes at most as many inputs as it has pairs. -/
theorem card_ioCells_le_length (io : List (ι × Y)) : (ioCells io).card ≤ io.length :=
  (List.toFinset_card_le _).trans (List.length_map _).le

/-- **Several databases.** For prescriptions `L j` on a family of databases `(D_j)_j`, the
pi-tensor products `P = ⊗_j P_{L j}` and `P̂ = ⊗_j P̂_{L j}` satisfy `P P̂ P = α² P` with
`α = (1 - 1/N)^d`, where `d = ∑_j d_j` counts the prescribed inputs of every database. -/
theorem piKron_checkProjector_mul_piKron_compressedCheckProjector_mul {κ : Type*} [Fintype κ]
    [DecidableEq κ] (L : κ → List (ι × Y)) :
    piKron (fun j ↦ checkProjector Y (L j)) * piKron (fun j ↦ compressedCheckProjector (L j)) *
        piKron (fun j ↦ checkProjector Y (L j)) =
      ((1 - (Fintype.card Y : ℂ)⁻¹) ^ (2 * ∑ j, (ioCells (L j)).card)) •
        piKron (fun j ↦ checkProjector Y (L j)) := by
  rw [piKron_mul, piKron_mul]
  simp_rw [checkProjector_mul_compressedCheckProjector_mul_checkProjector, piKron_smul]
  rw [Finset.prod_pow_eq_pow_sum, Finset.mul_sum]

/-! ## The exact distance (26) -/

omit [DecidableEq Y] in
/-- The real angle `α² = (1 - 1/N)^(2d)` lies in `[0, 1]`. -/
theorem one_sub_inv_card_pow_mem_Icc (d : ℕ) :
    0 ≤ (1 - (Fintype.card Y : ℝ)⁻¹) ^ d ∧ (1 - (Fintype.card Y : ℝ)⁻¹) ^ d ≤ 1 := by
  have hN : (1 : ℝ) ≤ Fintype.card Y := Nat.one_le_cast.mpr Fintype.card_pos
  have h0 : 0 ≤ 1 - (Fintype.card Y : ℝ)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hN)
  have h1 : 1 - (Fintype.card Y : ℝ)⁻¹ ≤ 1 := sub_le_self _ (by positivity)
  exact ⟨pow_nonneg h0 d, pow_le_one₀ h0 h1⟩

/-- **The exact discrepancy of a consistency projector (eq. (26)).** For a consistent prescription
on `d` distinct inputs, `‖P̂ - P‖² = 1 - (1 - 1/N)^(2d)`, where `P̂ = F P F`. This is exact; the
paper bounds the norm by `2√(d/N)` (ePrint 2025/2166, Lemma 9.5, p. 61). -/
theorem l2_opNorm_compressedCheckProjector_sub_sq {io : List (ι × Y)} (h : ConsistentIO io) :
    ‖compressedCheckProjector io - checkProjector Y io‖ ^ 2 =
      1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * (ioCells io).card) := by
  rw [norm_sub_rev]
  refine l2_opNorm_sub_sq_eq_one_sub_of_mul_mul_eq (conjTranspose_checkProjector io)
    (checkProjector_mul_self io) (conjTranspose_compressedCheckProjector io)
    (compressedCheckProjector_mul_self io) (one_sub_inv_card_pow_mem_Icc _).2 ?_ ?_
    (checkProjector_ne_zero h)
  · rw [checkProjector_mul_compressedCheckProjector_mul_checkProjector]
    push_cast
    rfl
  · rw [compressedCheckProjector_mul_checkProjector_mul_compressedCheckProjector]
    push_cast
    rfl

omit [Nonempty Y] in
/-- For an inconsistent prescription both projectors vanish. -/
theorem l2_opNorm_compressedCheckProjector_sub_of_not_consistentIO {io : List (ι × Y)}
    (h : ¬ ConsistentIO io) : ‖compressedCheckProjector io - checkProjector Y io‖ = 0 := by
  rw [compressedCheckProjector_eq_zero_of_not_consistentIO h,
    checkProjector_eq_zero_of_not_consistentIO h, sub_zero, norm_zero]

/-- The Bernoulli bound `1 - (1 - u)^m ≤ m u`, for `u ≤ 2`. -/
theorem one_sub_one_sub_pow_le (m : ℕ) {u : ℝ} (hu : u ≤ 2) :
    1 - (1 - u) ^ m ≤ m * u := by
  have h := one_add_mul_le_pow (a := -u) (by linarith) m
  rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at h
  linarith

/-- **Consistency projectors, leading order.** For every prescription on `d` distinct inputs,
`‖P̂ - P‖² ≤ 2d/N`. -/
theorem l2_opNorm_compressedCheckProjector_sub_sq_le (io : List (ι × Y)) :
    ‖compressedCheckProjector io - checkProjector Y io‖ ^ 2 ≤
      2 * (ioCells io).card / Fintype.card Y := by
  by_cases h : ConsistentIO io
  · rw [l2_opNorm_compressedCheckProjector_sub_sq h]
    have hN : (1 : ℝ) ≤ Fintype.card Y := Nat.one_le_cast.mpr Fintype.card_pos
    calc 1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * (ioCells io).card)
        ≤ ((2 * (ioCells io).card : ℕ) : ℝ) * (Fintype.card Y : ℝ)⁻¹ :=
          one_sub_one_sub_pow_le _ ((inv_le_one_of_one_le₀ hN).trans one_le_two)
      _ = 2 * (ioCells io).card / Fintype.card Y := by push_cast; ring
  · rw [l2_opNorm_compressedCheckProjector_sub_of_not_consistentIO h]
    norm_num
    positivity

/-- **Lemma 9.5 of the paper** (ePrint 2025/2166, p. 61): `‖P̂ - P‖ ≤ 2√(d/N)`. It follows from
the sharper `‖P̂ - P‖² ≤ 2d/N`. -/
theorem l2_opNorm_compressedCheckProjector_sub_le_two_mul_sqrt (io : List (ι × Y)) :
    ‖compressedCheckProjector io - checkProjector Y io‖ ≤
      2 * Real.sqrt ((ioCells io).card / Fintype.card Y) := by
  have h := l2_opNorm_compressedCheckProjector_sub_sq_le io
  have hd : (0 : ℝ) ≤ (ioCells io).card / Fintype.card Y := by positivity
  rw [← Real.sqrt_sq (norm_nonneg _)]
  calc Real.sqrt (‖compressedCheckProjector io - checkProjector Y io‖ ^ 2)
      ≤ Real.sqrt (4 * ((ioCells io).card / Fintype.card Y)) := by
        refine Real.sqrt_le_sqrt (h.trans ?_)
        rw [mul_div_assoc]
        linarith
    _ = 2 * Real.sqrt ((ioCells io).card / Fintype.card Y) := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]

end Quantum
