/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.Oracle

/-!
# The action of the compressed oracle on basis states

A query of `|x, y⟩` to the compressed oracle touches only the cell `x` of the database:
it decompresses the cell, adds its content into the response register, and compresses the cell
again. With `S = Quantum.cellCompress Y`,

  `cO |x, y⟩|D⟩ = ∑ u, ∑ u'', S u'' u * S u (D x) • |x, y + u⟩|D[x ↦ u'']⟩`,

where `u` and `u''` range over `Option Y` and an empty cell adds `0`
(`Quantum.compressedOracle_mulVec_single`). Spelling out the entries of `S` gives the two cases of
Zhandry's description, with `N = |Y|` and `c = N^(-1/2)`:

* if `D x = none` (`Quantum.compressedOracle_mulVec_single_of_eq_none`),
  `cO |x, y⟩|D⟩ = ∑ v, (N⁻¹ • |x, y + v⟩|D⟩ +
    ∑ v'', (δ v'' v - N⁻¹) * c • |x, y + v⟩|D[x ↦ v'']⟩)`;
* if `D x = some u` (`Quantum.compressedOracle_mulVec_single_of_eq_some`),
  `cO |x, y⟩|D⟩ = ∑ v'', N⁻¹ • |x, y⟩|D[x ↦ v'']⟩ +
    ∑ v, (c * (δ v u - N⁻¹) • |x, y + v⟩|D[x ↦ ⊥]⟩ +
      ∑ v'', (δ v'' v - N⁻¹) * (δ v u - N⁻¹) • |x, y + v⟩|D[x ↦ v'']⟩)`.

These are the formulas in the computational basis of the response register (the standard form).
They are proved directly from the definition, without the Fourier (phase) form of the compressed
oracle, which needs the characters of `Y`.
-/

public section

open Matrix
open scoped Kronecker

namespace Quantum

variable {X Y : Type*}

/-! ## Compressing one cell of a basis state -/

section compressAt

variable (Y) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The entry of the compression of the cell `x`: it is the entry of the one-cell compression at
the cell `x` when the two databases agree away from `x`, and zero otherwise. -/
theorem compressAt_apply (x : X) (D D' : Database X Y) :
    compressAt Y x D D' = if ∀ j ≠ x, D j = D' j then cellCompress Y (D x) (D' x) else 0 := by
  rw [compressAt, piKron_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ x),
    Pi.mulSingle_eq_same,
    Finset.prod_congr rfl fun j hj ↦ by
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hj), Matrix.one_apply],
    Finset.prod_boole]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, mul_boole]

/-- Compressing the cell `x` of a basis state `|D⟩` superposes the databases `D[x ↦ u]`. -/
theorem compressAt_mulVec_single (x : X) (D : Database X Y) :
    compressAt Y x *ᵥ Pi.single D 1 =
      ∑ u, cellCompress Y u (D x) • Pi.single (Function.update D x u) 1 := by
  ext D''
  rw [Matrix.mulVec_single_one, Matrix.col_apply, compressAt_apply, Finset.sum_apply,
    Finset.sum_eq_single (D'' x)]
  · simp [Pi.single_apply, Function.eq_update_iff]
  · intro u _ hu
    simp [Function.eq_update_iff, Ne.symm hu]
  · simp

end compressAt

/-! ## Controlled compression of a basis state -/

section controlled

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- Compressing the queried cell of a basis state `|m⟩|D⟩` superposes the databases
`D[m.1 ↦ u]`, leaving the query register at `m`. -/
theorem controlled_compressAt_mulVec_single (m : X × Y) (D : Database X Y) :
    controlled (compressAt Y) *ᵥ Pi.single (m, D) 1 =
      ∑ u, cellCompress Y u (D m.1) • Pi.single (m, Function.update D m.1 u) 1 := by
  ext ⟨m'', D''⟩
  have h := congrFun (compressAt_mulVec_single Y m.1 D) D''
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [Matrix.mulVec_single_one, Matrix.col_apply, controlled_apply, Finset.sum_apply]
  by_cases hm : m'' = m
  · subst hm
    simpa [Pi.single_apply, Finset.sum_apply] using h
  · simp [hm]

end controlled

/-! ## The compressed oracle on basis states -/

section compressed

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- **The compressed oracle on a basis state.** A query of `|x, y⟩|D⟩` decompresses the cell
`x` into `u`, adds `u` (or `0` when `u` is empty) into the response register, and compresses the
cell into `u''`. -/
theorem compressedOracle_mulVec_single (x : X) (y : Y) (D : Database X Y) :
    compressedOracle X Y *ᵥ Pi.single ((x, y), D) 1 =
      ∑ u, ∑ u'', (cellCompress Y u'' u * cellCompress Y u (D x)) •
        Pi.single ((x, y + u.getD 0), Function.update D x u'') 1 := by
  rw [compressedOracle_eq_controlled, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    controlled_compressAt_mulVec_single]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, standardOracle, tableOracle,
    basisMatrix_mulVec_single, tableOracleEquiv_apply, oracleEquiv_apply, Database.lookup_apply,
    Function.update_self, controlled_compressAt_mulVec_single, Function.update_idem,
    Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun u'' _ ↦ ?_
  rw [mul_comm]

/-- The compressed oracle on a basis state whose queried cell is empty. -/
theorem compressedOracle_mulVec_single_of_eq_none {x : X} (y : Y) {D : Database X Y}
    (h : D x = none) :
    compressedOracle X Y *ᵥ Pi.single ((x, y), D) 1 =
      ∑ v : Y, ((Fintype.card Y : ℂ)⁻¹ • Pi.single ((x, y + v), D) 1 +
        ∑ v'' : Y, (((if v'' = v then 1 else 0) - (Fintype.card Y : ℂ)⁻¹) * cellAmp Y) •
          Pi.single ((x, y + v), Function.update D x (some v'')) 1) := by
  have hD : Function.update D x none = D := by
    rw [← h, Function.update_eq_self]
  rw [compressedOracle_mulVec_single, Fintype.sum_option]
  simp only [h, cellCompress_none_none, mul_zero, zero_smul, Finset.sum_const_zero, zero_add,
    Fintype.sum_option, cellCompress_some_none, cellCompress_none_some, cellAmp_mul_self,
    cellCompress_some_some, Option.getD_some, hD]

/-- The compressed oracle on a basis state whose queried cell holds `u`. -/
theorem compressedOracle_mulVec_single_of_eq_some {x : X} (y : Y) {D : Database X Y}
    {u : Y} (h : D x = some u) :
    compressedOracle X Y *ᵥ Pi.single ((x, y), D) 1 =
      ∑ v'' : Y, (Fintype.card Y : ℂ)⁻¹ •
          Pi.single ((x, y), Function.update D x (some v'')) 1 +
        ∑ v : Y, ((cellAmp Y * ((if v = u then 1 else 0) - (Fintype.card Y : ℂ)⁻¹)) •
            Pi.single ((x, y + v), Function.update D x none) 1 +
          ∑ v'' : Y, (((if v'' = v then 1 else 0) - (Fintype.card Y : ℂ)⁻¹) *
              ((if v = u then 1 else 0) - (Fintype.card Y : ℂ)⁻¹)) •
            Pi.single ((x, y + v), Function.update D x (some v'')) 1) := by
  rw [compressedOracle_mulVec_single, Fintype.sum_option]
  simp only [h, Fintype.sum_option, cellCompress_none_none, zero_mul, zero_smul, zero_add,
    cellCompress_some_none, cellCompress_none_some, cellAmp_mul_self, cellCompress_some_some,
    Option.getD_none, Option.getD_some, add_zero]

end compressed

end Quantum
