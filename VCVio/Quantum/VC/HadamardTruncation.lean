/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.HadamardDatabase
public import VCVio.Quantum.MatrixMap.BlockNorm

/-!
# Truncated database commutators

The query input and the unaddressed cell contents label orthogonal blocks. Interior blocks
contain the complete cell, whereas boundary blocks retain only the empty label.
-/

public section

open Matrix OracleSpec
open scoped Kronecker Matrix.Norms.L2Operator ENNReal

namespace Quantum

/-- The commutator between an operator and a label-controlled auxiliary operation. -/
@[expose]
noncomputable def auxiliaryCommutator {A L E : Type*} [Fintype A] [DecidableEq A]
    [Fintype E] [DecidableEq E] (O : Matrix A A ℂ) (π : A → L) (U : L → Matrix E E ℂ) :
    Matrix (A × E) (A × E) ℂ :=
  labelControlled (fun p ↦ π p.1) (fun l ↦ (1 : Matrix A A ℂ) ⊗ₖ U l) * (O ⊗ₖ 1) -
    (O ⊗ₖ 1) * labelControlled (fun p ↦ π p.1) (fun l ↦ (1 : Matrix A A ℂ) ⊗ₖ U l)

/-- The entries of the auxiliary commutator are the oracle entries times the difference
between the two controlled auxiliary entries. -/
theorem auxiliaryCommutator_apply {A L E : Type*} [Fintype A] [DecidableEq A]
    [Fintype E] [DecidableEq E] (O : Matrix A A ℂ) (π : A → L) (U : L → Matrix E E ℂ)
    (a b : A) (e f : E) :
    auxiliaryCommutator O π U (a, e) (b, f) = O a b * (U (π a) e f - U (π b) e f) := by
  simp [auxiliaryCommutator, Matrix.mul_apply, Fintype.sum_prod_type,
    labelControlled_apply, kroneckerMap_apply, Matrix.one_apply, mul_sub, mul_comm]

variable {X Y L E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [DecidableEq L] [Fintype E] [DecidableEq E]

/-- Removing the addressed cell identifies the oracle's input/rest-of-database block. -/
@[expose]
def extendedDatabaseBlock (p : ((X × Y) × Database X Y) × E) : X × Database X Y :=
  (p.1.1.1, Function.update p.1.2 p.1.1.1 none)

omit [Fintype X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] in
/-- Restoring the addressed cell reconstructs a database in a fixed block. -/
theorem database_eq_update_of_erase_eq {d r : Database X Y} {x : X}
    (h : Function.update d x none = r) : d = Function.update r x (d x) := by
  rw [← h, Function.update_idem, Function.update_eq_self]

omit [DecidableEq L] in
/-- Every nonzero entry of the auxiliary commutator lies in an input/rest block. -/
theorem auxiliaryCommutator_extended_block_eq (W : Matrix Y Y ℂ) (t : ℕ)
    (π : Database X Y → L) (U : L → Matrix E E ℂ)
    (p q : ((X × Y) × Database X Y) × E)
    (h : auxiliaryCommutator (truncatedExtendedOracle W t) (fun a ↦ π a.2) U p q ≠ 0) :
    extendedDatabaseBlock p = extendedDatabaseBlock q := by
  obtain ⟨⟨⟨x, r⟩, d⟩, e⟩ := p
  obtain ⟨⟨⟨z, s⟩, d'⟩, f⟩ := q
  rw [auxiliaryCommutator_apply] at h
  have ho := left_ne_zero_of_mul h
  rw [truncatedExtendedOracle_apply] at ho
  split_ifs at ho with hs
  · rw [extendedCompressedOracle_apply] at ho
    split_ifs at ho with hc
    · obtain ⟨rfl, hc⟩ := hc
      change (x, Function.update d x none) = (x, Function.update d' x none)
      congr 1
      funext j
      by_cases hj : j = x
      · subst j; simp
      · simp only [Function.update_of_ne hj]
        exact hc j hj
    · exact False.elim (ho rfl)
  · exact False.elim (ho rfl)

omit [Fintype Y] [DecidableEq Y] [AddCommGroup Y] in
/-- On an interior block, all restored databases satisfy the truncation bound. -/
theorem size_le_of_erase_eq {d r : Database X Y} {x : X} {t : ℕ}
    (hd : Function.update d x none = r) (hr : r.size < t) : d.size ≤ t := by
  rw [database_eq_update_of_erase_eq hd]
  exact (Database.size_update_le r x _).trans hr

omit [Fintype Y] [DecidableEq Y] [AddCommGroup Y] in
/-- At the boundary, the only retained database in a block is its empty-cell database. -/
theorem database_eq_of_erase_eq_of_boundary {d r : Database X Y} {x : X} {t : ℕ}
    (hd : Function.update d x none = r) (hr : t ≤ r.size) (hs : d.size ≤ t) : d = r := by
  have hx : d x = none := by
    by_contra hx
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hx
    have he := Database.size_eq_size_update_none_add_one hy
    rw [hd] at he
    omega
  rw [← hd, ← hx, Function.update_eq_self]

/-- Two database states in the same interior block have exactly the one-cell oracle entry. -/
theorem truncatedExtendedOracle_apply_of_interior (W : Matrix Y Y ℂ) {t : ℕ}
    {x : X} {r d e : Database X Y} (hr : r.size < t)
    (hd : Function.update d x none = r) (he : Function.update e x none = r) (a b : Y) :
    truncatedExtendedOracle W t ((x, a), d) ((x, b), e) =
      compressedCell W (a, d x) (b, e x) := by
  rw [truncatedExtendedOracle_apply, ite_eq_left
    ⟨size_le_of_erase_eq hd hr, size_le_of_erase_eq he hr⟩, extendedCompressedOracle_apply]
  apply ite_eq_left
  refine ⟨rfl, ?_⟩
  intro j hj
  have hh := congrFun (hd.trans he.symm) j
  simpa only [Function.update_of_ne hj] using hh

omit [Fintype X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] in
/-- The two concrete constraints encoded by an input/rest block equality. -/
theorem extendedDatabaseBlock_properties {p : ((X × Y) × Database X Y) × E}
    {x : X} {r : Database X Y} (hp : extendedDatabaseBlock p = (x, r)) :
    p.1.1.1 = x ∧ Function.update p.1.2 x none = r := by
  obtain ⟨hx, hr⟩ := Prod.mk.inj hp
  exact ⟨hx, by simpa only [hx] using hr⟩

omit [Fintype X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] in
/-- Within one input/rest block, the response, addressed cell, and auxiliary register
uniquely determine the whole state. -/
theorem extendedDatabaseBlock_cell_injective (x : X) (r : Database X Y) :
    Function.Injective (fun p : {p : ((X × Y) × Database X Y) × E |
        extendedDatabaseBlock p = (x, r)} ↦ ((p.1.1.1.2, p.1.1.2 x), p.1.2)) := by
  intro p q he
  obtain ⟨hp, hpd⟩ := extendedDatabaseBlock_properties p.2
  obtain ⟨hq, hqd⟩ := extendedDatabaseBlock_properties q.2
  obtain ⟨hcell, haux⟩ := Prod.mk.inj he
  obtain ⟨hresp, hval⟩ := Prod.mk.inj hcell
  have hd : p.1.1.2 = q.1.1.2 := by
    rw [database_eq_update_of_erase_eq hpd, database_eq_update_of_erase_eq hqd, hval]
  apply Subtype.ext
  exact Prod.ext (Prod.ext (Prod.ext (hp.trans hq.symm) hresp) hd) haux

omit [DecidableEq L] in
/-- The generalized instability estimate for the population-truncated database extension,
with the repair note's coefficient `24`. -/
theorem norm_auxiliaryCommutator_truncatedExtendedOracle_sq_le
    [UniformAnswerMeasure (X →ₒ Y)] (hY : ∀ y : Y, y + y = 0)
    {W : Matrix Y Y ℂ} (hW : W ∈ unitaryGroup Y ℂ) (hWW : W * W = 1)
    (π : Database X Y → L) (t : ℕ) (U : L → Matrix E E ℂ)
    (hU : ∀ l, U l ∈ unitaryGroup E ℂ) :
    ‖auxiliaryCommutator (truncatedExtendedOracle W t) (fun a ↦ π a.2) U‖ ^ 2 ≤
      24 * (Database.instability π t).toReal := by
  classical
  let A := auxiliaryCommutator (truncatedExtendedOracle W t) (fun a ↦ π a.2) U
  have hnorm : ‖A‖ ≤ Real.sqrt (24 * (Database.instability π t).toReal) := by
    apply l2_opNorm_le_of_submatrix_le extendedDatabaseBlock extendedDatabaseBlock
      (auxiliaryCommutator_extended_block_eq W t π U) (by positivity)
    rintro ⟨x, r⟩
    let F := {p : ((X × Y) × Database X Y) × E // extendedDatabaseBlock p = (x, r)}
    change ‖A.submatrix (Subtype.val : F → _) (Subtype.val : F → _)‖ ≤ _
    by_cases hr : r.size < t
    · by_cases hx : r x = none
      · let f : F → (Y × Option Y) × E := fun p ↦ ((p.1.1.1.2, p.1.1.2 x), p.1.2)
        let lab : Option Y → L := fun a ↦ π (Function.update r x a)
        have he : A.submatrix (Subtype.val : F → _) (Subtype.val : F → _) =
            (auxiliaryCommutator (compressedCell W) (fun a ↦ lab a.2) U).submatrix f f := by
          ext p q
          obtain ⟨hp, hpd⟩ := extendedDatabaseBlock_properties p.2
          obtain ⟨hq, hqd⟩ := extendedDatabaseBlock_properties q.2
          simp only [A, submatrix_apply]
          rw [auxiliaryCommutator_apply _ _ _ p.1.1 q.1.1 p.1.2 q.1.2]
          simp only [f, lab, auxiliaryCommutator_apply]
          have ho : truncatedExtendedOracle W t p.1.1 q.1.1 =
              compressedCell W (p.1.1.1.2, p.1.1.2 x) (q.1.1.1.2, q.1.1.2 x) := by
            have ep : p.1.1 = ((x, p.1.1.1.2), p.1.1.2) :=
              Prod.ext (Prod.ext hp rfl) rfl
            have eq : q.1.1 = ((x, q.1.1.1.2), q.1.1.2) :=
              Prod.ext (Prod.ext hq rfl) rfl
            rw [ep, eq]
            exact truncatedExtendedOracle_apply_of_interior W hr hpd hqd _ _
          rw [ho]
          congr 2
          · exact congrArg (fun d ↦ U (π d) p.1.2 q.1.2)
              (database_eq_update_of_erase_eq hpd)
          · exact congrArg (fun d ↦ U (π d) p.1.2 q.1.2)
              (database_eq_update_of_erase_eq hqd)
        rw [he]
        have hsmall := norm_commutator_compressedCell_sq_le_twentyFour_mul hY hW hWW lab U hU
        have hi : cellInstability lab ≤ (Database.instability π t).toReal := by
          have hn : Function.update r x none = r := Function.update_eq_self_iff.mpr hx.symm
          simpa only [cellInstability, lab, hn] using Database.card_div_le_instability π hr hx
        exact (l2_opNorm_submatrix_le_of_injective _
          (extendedDatabaseBlock_cell_injective x r)
          (extendedDatabaseBlock_cell_injective x r)).trans
          (Real.le_sqrt_of_sq_le (hsmall.trans (by gcongr)))
      · have hF : IsEmpty F := ⟨fun p ↦ by
          obtain ⟨_, hp⟩ := extendedDatabaseBlock_properties p.2
          have he := congrFun hp x
          exact hx (by simpa using he.symm)⟩
        let := hF
        have hz : A.submatrix (Subtype.val : F → _) (Subtype.val : F → _) = 0 :=
          Subsingleton.elim _ _
        rw [hz, norm_zero]
        positivity
    · have hz : A.submatrix (Subtype.val : F → _) (Subtype.val : F → _) = 0 := by
        ext p q
        obtain ⟨hp, hpd⟩ := extendedDatabaseBlock_properties p.2
        obtain ⟨hq, hqd⟩ := extendedDatabaseBlock_properties q.2
        simp only [A, submatrix_apply, Matrix.zero_apply]
        rw [auxiliaryCommutator_apply _ _ _ p.1.1 q.1.1 p.1.2 q.1.2]
        by_cases hs : p.1.1.2.size ≤ t ∧ q.1.1.2.size ≤ t
        · have hd := database_eq_of_erase_eq_of_boundary hpd (Nat.le_of_not_gt hr) hs.1
          have he := database_eq_of_erase_eq_of_boundary hqd (Nat.le_of_not_gt hr) hs.2
          rw [hd, he, sub_self, mul_zero]
        · rw [truncatedExtendedOracle_apply, ite_eq_right hs, zero_mul]
      rw [hz, norm_zero]
      positivity
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans_eq (Real.sq_sqrt (by positivity))

end Quantum
