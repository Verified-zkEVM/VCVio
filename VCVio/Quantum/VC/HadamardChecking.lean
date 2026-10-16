/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.Hadamard
public import VCVio.Quantum.VC.Proof.Extraction

/-!
# Actual accepting maps for empty-sector extensions

A classical query initializes a fresh zero response and measures its answer. The accepting
matrix element is `Q_y + W y 0 • R`, as in equation (14) of the repair note. A list of checks
multiplies these amplitudes, retaining repeated queries and conflicting prescriptions.
The resulting operator is generally not a projector. Its effect nevertheless dominates the
filled-only consistency projector conjugated by compression.
-/

public section

open Matrix OracleSpec
open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Quantum

section amplitudes

variable {X Y : Type*} [DecidableEq Y]

/-- The accepting amplitude for one prescribed value, with empty-sector amplitudes `g`. -/
@[expose]
def acceptValue (g : Y → ℂ) (y : Y) : Option Y → ℂ
  | none => g y
  | some z => if z = y then 1 else 0

/-- The accepting amplitude of a list on a decompressed database. Each occurrence contributes
one factor, so repeated prescriptions are retained. -/
@[expose]
def acceptWeight (g : Y → ℂ) (io : List (X × Y)) (d : X → Option Y) : ℂ :=
  (io.map fun p ↦ acceptValue g p.2 (d p.1)).prod

/-- An empty list has accepting amplitude one. -/
@[simp]
theorem acceptWeight_nil (g : Y → ℂ) (d : X → Option Y) : acceptWeight g [] d = 1 := rfl

/-- A list's accepting amplitude is the product of its head and tail amplitudes. -/
@[simp]
theorem acceptWeight_cons (g : Y → ℂ) (p : X × Y) (io : List (X × Y)) (d : X → Option Y) :
    acceptWeight g (p :: io) d = acceptValue g p.2 (d p.1) * acceptWeight g io d := rfl

/-- Prescriptions already satisfied by filled cells have accepting amplitude one. -/
theorem acceptWeight_eq_one (g : Y → ℂ) (io : List (X × Y)) (d : X → Option Y)
    (h : ∀ p ∈ io, d p.1 = some p.2) : acceptWeight g io d = 1 := by
  apply List.prod_eq_one
  intro z hz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
  simp [h p hp, acceptValue]

/-- A response amplitude bounded by one makes every list amplitude a contraction. -/
theorem norm_acceptWeight_le_one (g : Y → ℂ) (hg : ∀ y, ‖g y‖ ≤ 1)
    (io : List (X × Y)) (d : X → Option Y) : ‖acceptWeight g io d‖ ≤ 1 := by
  induction io with
  | nil => simp
  | cons p io ih =>
    rw [acceptWeight_cons, norm_mul]
    have hp : ‖acceptValue g p.2 (d p.1)‖ ≤ 1 := by
      cases d p.1 <;> simp only [acceptValue]
      · exact hg p.2
      · split_ifs <;> simp
    exact (mul_le_mul hp ih (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- If a partial database fails a list, its accepting amplitude is bounded by the largest
empty-sector amplitude. A wrong filled value makes that amplitude zero. -/
theorem norm_acceptWeight_le_of_not_consistent (g : Y → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hc1 : c ≤ 1) (hg : ∀ y, ‖g y‖ ≤ c) (io : List (X × Y)) (d : X → Option Y)
    (h : ¬ ∀ p ∈ io, d p.1 = some p.2) : ‖acceptWeight g io d‖ ≤ c := by
  induction io with
  | nil => exact False.elim (h (by simp))
  | cons p io ih =>
    rw [acceptWeight_cons, norm_mul]
    by_cases hp : d p.1 = some p.2
    · simp only [hp, acceptValue, ↓reduceIte, norm_one, one_mul]
      exact ih (fun ht ↦ h (by simpa [hp] using ht))
    · have hhead : ‖acceptValue g p.2 (d p.1)‖ ≤ c := by
        cases he : d p.1 with
        | none => exact hg p.2
        | some y =>
          have hy : y ≠ p.2 := fun hy ↦ hp (by simp [he, hy])
          simpa [acceptValue, hy] using hc
      exact (mul_le_mul hhead (norm_acceptWeight_le_one g (fun y ↦ (hg y).trans hc1) io d)
        (norm_nonneg _) hc).trans_eq (mul_one c)

/-- Repeating the same query `m` times multiplies its accepting amplitude `m` times. -/
theorem acceptWeight_replicate (g : Y → ℂ) (m : ℕ) (p : X × Y) (d : X → Option Y) :
    acceptWeight g (List.replicate m p) d = acceptValue g p.2 (d p.1) ^ m := by
  simp [acceptWeight]

/-- Two conflicting prescriptions at the same cell can accept only through its empty sector. -/
theorem acceptValue_mul_of_ne (g : Y → ℂ) {y z : Y} (hyz : y ≠ z) (a : Option Y) :
    acceptValue g y a * acceptValue g z a = if a = none then g y * g z else 0 := by
  cases a with
  | none => rfl
  | some t =>
    by_cases ht : t = y
    · subst t
      simp [acceptValue, hyz]
    · simp [acceptValue, ht]

/-- With a constant empty amplitude, the list amplitude is its power at the number of
empty-cell occurrences, unless a filled cell contradicts a prescription. This includes
arbitrary multiplicities and conflicting repeated prescriptions, as in repair-note (15). -/
theorem acceptWeight_const (a : ℂ) (io : List (X × Y)) (d : X → Option Y) :
    acceptWeight (fun _ ↦ a) io d =
      if ∀ p ∈ io, d p.1 = none ∨ d p.1 = some p.2 then
        a ^ (io.countP fun p ↦ (d p.1).isNone) else 0 := by
  have hgood : ∀ l : List (X × Y), (∀ p ∈ l, d p.1 = none ∨ d p.1 = some p.2) →
      acceptWeight (fun _ ↦ a) l d = a ^ (l.countP fun p ↦ (d p.1).isNone) := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons p l ih =>
      intro h
      have hp := h p (by simp)
      have ht := ih (fun q hq ↦ h q (by simp [hq]))
      rw [acceptWeight_cons, ht, List.countP_cons]
      rcases hp with hp | hp
      · simp [hp, acceptValue, pow_succ, mul_comm]
      · simp [hp, acceptValue]
  by_cases h : ∀ p ∈ io, d p.1 = none ∨ d p.1 = some p.2
  · rw [ite_eq_left h]
    exact hgood io h
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨p, hp, hnone, hval⟩ := h
    have hz : acceptValue (fun _ : Y ↦ a) p.2 (d p.1) = 0 := by
      cases hd : d p.1 with
      | none => exact False.elim (hnone hd)
      | some y =>
        have hy : y ≠ p.2 := fun hy ↦ hval (by simp [hd, hy])
        simp [acceptValue, hy]
    exact List.prod_eq_zero (List.mem_map.mpr ⟨p, hp, hz⟩)

end amplitudes

section cell

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The projector onto the compressed filled value `y`. -/
@[expose]
noncomputable def cellFilledProjector (y : Y) : Matrix (Option Y) (Option Y) ℂ :=
  cellCompress Y * Matrix.single (some y) (some y) 1 * cellCompress Y

omit [Fintype Y] in
/-- A single decompressed query accepts with the corresponding diagonal response amplitude. -/
theorem submatrix_decompressedCell (W : Matrix Y Y ℂ) (y : Y) :
    (decompressedCell W).submatrix (fun a ↦ (y, a)) (fun a ↦ (0, a)) =
      diagonal (acceptValue (fun z ↦ W z 0) y) := by
  ext a b
  by_cases hab : a = b
  · subst b
    cases a <;> simp [decompressedCell, blockDiagonal_apply, emptyExtensionBlock,
      acceptValue, eq_comm]
  · simp [decompressedCell, blockDiagonal_apply, hab]

/-- Equation (14) of the repair note with the exact matrix entry of arbitrary `W`.
No unitarity, involution, or flat-column assumption is used by this matrix-element identity. -/
theorem submatrix_compressedCell (W : Matrix Y Y ℂ) (y : Y) :
    (compressedCell W).submatrix (fun a ↦ (y, a)) (fun a ↦ (0, a)) =
      cellFilledProjector y + (W y 0) • cellInvalidProjector (Y := Y) := by
  rw [compressedCell, submatrix_one_kronecker_mul_mul_one_kronecker,
    submatrix_decompressedCell]
  have h : diagonal (acceptValue (fun z ↦ W z 0) y) =
      Matrix.single (some y) (some y) 1 + (W y 0) • Matrix.single none none 1 := by
    ext a b
    cases a <;> cases b <;>
      simp [acceptValue, diagonal_apply, Matrix.single_apply, eq_comm]
    split_ifs <;> simp_all
    aesop
  rw [h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    cellFilledProjector, cellInvalidProjector]

end cell

section diagonal

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Conjugated diagonal amplitudes multiply in the order of the corresponding checks. -/
theorem conj_diagonal_mul_conj_diagonal {C : Matrix S S ℂ} (hCC : C * C = 1)
    (f g : S → ℂ) :
    (C * diagonal f * C) * (C * diagonal g * C) =
      C * diagonal (fun d ↦ f d * g d) * C := by
  calc
    _ = C * diagonal f * (C * C) * diagonal g * C := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hCC, Matrix.mul_one, Matrix.mul_assoc C, diagonal_mul_diagonal]

/-- An accepting amplitude equal to one on a predicate has an effect dominating that
predicate's projector. No bound on its other amplitudes is required. -/
theorem diagonal_accept_effect_ge (f : S → ℂ) (p : S → Prop) [DecidablePred p]
    (hf : ∀ d, p d → f d = 1) :
    diagonal (fun d ↦ if p d then (1 : ℂ) else 0) ≤ (diagonal f)ᴴ * diagonal f := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← sub_nonneg, diagonal_sub]
  exact (Matrix.PosSemidef.diagonal fun d ↦ by
    by_cases h : p d
    · simp [h, hf d h]
    · simpa [h] using star_mul_self_nonneg (f d)).nonneg

/-- Conjugation transports the diagonal accepting-effect inequality. -/
theorem conjugated_accept_effect_ge {C : Matrix S S ℂ} (hC : Cᴴ = C) (hCC : C * C = 1)
    (f : S → ℂ) (p : S → Prop) [DecidablePred p] (hf : ∀ d, p d → f d = 1) :
    C * diagonal (fun d ↦ if p d then (1 : ℂ) else 0) * C ≤
      (C * diagonal f * C)ᴴ * (C * diagonal f * C) := by
  have h := (sub_nonneg.mpr (diagonal_accept_effect_ge f p hf)).posSemidef
  have hc := (h.mul_mul_conjTranspose_same C).nonneg
  rw [hC, Matrix.mul_sub, Matrix.sub_mul, sub_nonneg] at hc
  convert hc using 1
  simp only [conjTranspose_mul, hC]
  calc
    _ = C * (diagonal f)ᴴ * (C * C) * diagonal f * C := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hCC, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/-- A uniform pointwise amplitude error bounds the conjugated operator error. -/
theorem norm_conjugated_diagonal_sub_le {C : Matrix S S ℂ} (hC : Cᴴ = C)
    (hCC : C * C = 1) (f g : S → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hfg : ∀ d, ‖f d - g d‖ ≤ c) :
    ‖C * diagonal f * C - C * diagonal g * C‖ ≤ c := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  rw [MatrixMap.l2_opNorm_mul_coisometry (by rw [hC, hCC]),
    MatrixMap.l2_opNorm_isometry_mul (by rw [hC, hCC]), l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hc).mpr hfg

end diagonal

section lists

variable {X Y S : Type*} [DecidableEq Y] [Fintype S] [DecidableEq S]

/-- The actual accepting operator of a list in a compressed basis. This definition does not
deduplicate the list, even when its prescriptions conflict. -/
@[expose]
noncomputable def acceptingList (C : Matrix S S ℂ) (g : Y → ℂ) (io : List (X × Y))
    (read : S → X → Option Y) : Matrix S S ℂ :=
  C * diagonal (fun d ↦ acceptWeight g io (read d)) * C

/-- The accepting operator is the product of the single-query Kraus operators, retaining
all list occurrences. No consistency or distinctness hypothesis is imposed. -/
theorem acceptingList_eq_prod {C : Matrix S S ℂ} (hCC : C * C = 1)
    (g : Y → ℂ) (io : List (X × Y)) (read : S → X → Option Y) :
    acceptingList C g io read =
      (io.map fun p ↦ C * diagonal (fun d ↦ acceptValue g p.2 (read d p.1)) * C).prod := by
  induction io with
  | nil => simp [acceptingList, acceptWeight, hCC]
  | cons p io ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    simp only [acceptingList, conj_diagonal_mul_conj_diagonal hCC, acceptWeight_cons]

/-- The partial-database consistency projector for a prescribed list. -/
@[expose]
noncomputable def filledListProjector (io : List (X × Y)) (read : S → X → Option Y) :
    Matrix S S ℂ :=
  diagonal fun d ↦ if ∀ p ∈ io, read d p.1 = some p.2 then 1 else 0

/-- The actual list effect dominates the compressed filled-only consistency projector,
including conflicting and repeated prescriptions. This needs no bound on empty amplitudes. -/
theorem acceptingList_effect_ge {C : Matrix S S ℂ} (hC : Cᴴ = C) (hCC : C * C = 1)
    (g : Y → ℂ) (io : List (X × Y)) (read : S → X → Option Y) :
    C * filledListProjector io read * C ≤
      (acceptingList C g io read)ᴴ * acceptingList C g io read := by
  apply conjugated_accept_effect_ge hC hCC
  exact fun d h ↦ acceptWeight_eq_one g io (read d) h

/-- The operator-norm part of equation (16) of the repair note, in a general amplitude form.
Taking `c = |Y|^(-1/2)` and a flat zero column of `W` gives its stated constant. -/
theorem norm_acceptingList_sub_le {C : Matrix S S ℂ} (hC : Cᴴ = C) (hCC : C * C = 1)
    (g : Y → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (hg : ∀ y, ‖g y‖ ≤ c)
    (io : List (X × Y)) (read : S → X → Option Y) :
    ‖acceptingList C g io read - C * filledListProjector io read * C‖ ≤ c := by
  apply norm_conjugated_diagonal_sub_le hC hCC _ _ hc
  intro d
  by_cases hd : ∀ p ∈ io, read d p.1 = some p.2
  · rw [ite_eq_left hd, acceptWeight_eq_one g io (read d) hd, sub_self, norm_zero]
    exact hc
  · rw [ite_eq_right hd, sub_zero]
    exact norm_acceptWeight_le_of_not_consistent g hc hc1 hg io (read d) hd

/-- Equation (16) with the explicit `N^(-1/2)` constant for a flat empty-sector column.
This is uniform over all input states and all lists, including the empty list. -/
theorem norm_acceptingList_sub_le_cellAmp [Fintype Y] [Nonempty Y]
    {C : Matrix S S ℂ} (hC : Cᴴ = C) (hCC : C * C = 1)
    (io : List (X × Y)) (read : S → X → Option Y) :
    ‖acceptingList C (fun _ ↦ cellAmp Y) io read - C * filledListProjector io read * C‖ ≤
      (Real.sqrt (Fintype.card Y))⁻¹ := by
  have hc : 0 ≤ (Real.sqrt (Fintype.card Y))⁻¹ := by positivity
  have hc1 : (Real.sqrt (Fintype.card Y))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact Real.one_le_sqrt.mpr (by exact_mod_cast Fintype.card_pos)
  apply norm_acceptingList_sub_le hC hCC _ hc hc1
  intro y
  simp [cellAmp, Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _)]

end lists

end Quantum
