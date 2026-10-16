/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.Compressed

/-!
# Empty-sector extensions of the compressed oracle

Definition 8.1 of ePrint 2025/2166 describes classical consistency checking and identifies its
accepting operation with a filled-cell projector. A decompressed empty cell in the totalized
oracle instead answers zero. Coherent extraction can reach that sector, so the filled-only
projector does not describe the actual checker there, and the old witness fails property P4.

The repair note, equations (4) and (6), changes only this empty sector: a response unitary `W`
acts there. Filled cells still add their value to the response. The definitions allow any
finite additive answer group and any matrix `W`; unitarity is assumed by the oracle constructor.
An involution additionally requires involutive translations and `W * W = 1`.

The response register precedes the cell register in the matrices below. Consequently the tensor
factors in the repair note's equation (6) appear in the order `(W - 1) ⊗ R`.
-/

public section

open Matrix
open scoped Kronecker

namespace Quantum

section blocks

variable {Y T : Type*} [Fintype Y] [DecidableEq Y] [Fintype T] [DecidableEq T]

/-- A finite block diagonal family of response unitaries is unitary. -/
theorem responseBlocks_mem_unitaryGroup {A : T → Matrix Y Y ℂ}
    (hA : ∀ t, A t ∈ unitaryGroup Y ℂ) :
    blockDiagonal A ∈ unitaryGroup (Y × T) ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, blockDiagonal_conjTranspose,
    ← blockDiagonal_mul]
  simp_rw [← star_eq_conjTranspose, fun t ↦ mem_unitaryGroup_iff'.mp (hA t)]
  exact blockDiagonal_one

end blocks

section cell

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The response operation conditioned on a decompressed cell: `W` at the empty label and
addition by `y` at a filled label `y`. -/
@[expose]
def emptyExtensionBlock (W : Matrix Y Y ℂ) : Option Y → Matrix Y Y ℂ
  | none => W
  | some y => xorShift Y y

/-- The decompressed one-cell extension, equation (4) of the repair note. -/
@[expose]
def decompressedCell (W : Matrix Y Y ℂ) : Matrix (Y × Option Y) (Y × Option Y) ℂ :=
  blockDiagonal (emptyExtensionBlock W)

/-- The compressed one-cell extension, obtained by conjugating the decompressed operation. -/
@[expose]
noncomputable def compressedCell (W : Matrix Y Y ℂ) :
    Matrix (Y × Option Y) (Y × Option Y) ℂ :=
  (1 ⊗ₖ cellCompress Y) * decompressedCell W * (1 ⊗ₖ cellCompress Y)

/-- Every decompressed block is unitary when the empty-sector response is unitary. -/
theorem emptyExtensionBlock_mem_unitaryGroup {W : Matrix Y Y ℂ}
    (hW : W ∈ unitaryGroup Y ℂ) (a : Option Y) :
    emptyExtensionBlock W a ∈ unitaryGroup Y ℂ := by
  cases a with
  | none => exact hW
  | some y => exact xorShift_mem_unitaryGroup y

/-- The decompressed one-cell extension is unitary for any unitary empty-sector response. -/
theorem decompressedCell_mem_unitaryGroup {W : Matrix Y Y ℂ}
    (hW : W ∈ unitaryGroup Y ℂ) :
    decompressedCell W ∈ unitaryGroup (Y × Option Y) ℂ :=
  responseBlocks_mem_unitaryGroup (emptyExtensionBlock_mem_unitaryGroup hW)

/-- The compressed one-cell extension is unitary for any unitary empty-sector response. -/
theorem compressedCell_mem_unitaryGroup {W : Matrix Y Y ℂ}
    (hW : W ∈ unitaryGroup Y ℂ) :
    compressedCell W ∈ unitaryGroup (Y × Option Y) ℂ := by
  have hF := kronecker_mem_unitary (one_mem (unitaryGroup Y ℂ))
    (cellCompress_mem_unitaryGroup (Y := Y))
  exact mul_mem (mul_mem hF (decompressedCell_mem_unitaryGroup hW)) hF

/-- In an exponent-two answer group, each response translation is an involution. This
hypothesis concerns the answer group and does not follow from unitarity of `W`. -/
theorem xorShift_mul_self_of_add_self (hY : ∀ y : Y, y + y = 0) (y : Y) :
    xorShift Y y * xorShift Y y = 1 := by
  ext a b
  simp only [Matrix.mul_apply, xorShift_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (b + y)]
  · simp [add_assoc, hY, Matrix.one_apply]
  · intro c _ hc
    simp [hc]
  · simp

/-- The decompressed extension is an involution when both filled and empty blocks are
involutions. For the paper's bitstrings, the answer-group hypothesis is the XOR identity. -/
theorem decompressedCell_mul_self (hY : ∀ y : Y, y + y = 0)
    {W : Matrix Y Y ℂ} (hW : W * W = 1) :
    decompressedCell W * decompressedCell W = 1 := by
  rw [decompressedCell, ← blockDiagonal_mul]
  convert blockDiagonal_one (m := Y) (o := Option Y) (α := ℂ) using 1
  congr 1
  funext a
  cases a with
  | none => exact hW
  | some y => exact xorShift_mul_self_of_add_self hY y

/-- The compressed extension is an involution under the same hypotheses as its decompressed
blocks; no particular Hadamard matrix is needed. -/
theorem compressedCell_mul_self (hY : ∀ y : Y, y + y = 0)
    {W : Matrix Y Y ℂ} (hW : W * W = 1) :
    compressedCell W * compressedCell W = 1 := by
  have hF : ((1 : Matrix Y Y ℂ) ⊗ₖ cellCompress Y) * (1 ⊗ₖ cellCompress Y) = 1 := by
    rw [one_kronecker_mul_one_kronecker, cellCompress_mul_self, one_kronecker_one]
  simp only [compressedCell]
  calc
    _ = (1 ⊗ₖ cellCompress Y) * decompressedCell W *
        (((1 : Matrix Y Y ℂ) ⊗ₖ cellCompress Y) * (1 ⊗ₖ cellCompress Y)) *
        decompressedCell W * (1 ⊗ₖ cellCompress Y) := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [hF, Matrix.mul_one,
        Matrix.mul_assoc (1 ⊗ₖ cellCompress Y) (decompressedCell W) (decompressedCell W),
        decompressedCell_mul_self hY hW, Matrix.mul_one, hF]

/-- The invalid-sector projector on the compressed cell, `R = F |empty⟩⟨empty| F`. -/
@[expose]
noncomputable def cellInvalidProjector : Matrix (Option Y) (Option Y) ℂ :=
  cellCompress Y * Matrix.single none none 1 * cellCompress Y

omit [AddCommGroup Y] in
/-- The invalid projector is the rank-one projector onto the uniform filled-cell vector. -/
theorem cellInvalidProjector_apply (a b : Option Y) :
    cellInvalidProjector (Y := Y) a b = cellUniform Y a * cellUniform Y b := by
  cases a <;> cases b <;>
    simp [cellInvalidProjector, Matrix.mul_apply, Fintype.sum_option, Matrix.single_apply]

omit [Fintype Y] in
/-- Changing the empty response changes the decompressed operation only at the empty cell. -/
theorem decompressedCell_sub (W V : Matrix Y Y ℂ) :
    decompressedCell W - decompressedCell V =
      (W - V) ⊗ₖ (Matrix.single none none 1 : Matrix (Option Y) (Option Y) ℂ) := by
  ext ⟨r, a⟩ ⟨s, b⟩
  cases a <;> cases b <;>
    simp [decompressedCell, emptyExtensionBlock, blockDiagonal_apply]

/-- Equation (6) of the repair note, in response-first register order. It is purely algebraic:
neither unitarity nor an exponent-two answer group is needed. -/
theorem compressedCell_sub (W V : Matrix Y Y ℂ) :
    compressedCell W - compressedCell V = (W - V) ⊗ₖ cellInvalidProjector (Y := Y) := by
  rw [compressedCell, compressedCell, ← Matrix.sub_mul, ← Matrix.mul_sub,
    decompressedCell_sub]
  simp only [cellInvalidProjector, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- Equation (6) with the old empty-sector identity response. -/
theorem compressedCell_sub_identity (W : Matrix Y Y ℂ) :
    compressedCell W - compressedCell 1 = (W - 1) ⊗ₖ cellInvalidProjector (Y := Y) :=
  compressedCell_sub W 1

/-- On the decompressed empty cell, the response is exactly `W`. -/
theorem decompressedCell_mul_empty (W : Matrix Y Y ℂ) :
    decompressedCell W *
        (1 ⊗ₖ (Matrix.single none none 1 : Matrix (Option Y) (Option Y) ℂ)) =
      W ⊗ₖ (Matrix.single none none 1 : Matrix (Option Y) (Option Y) ℂ) := by
  ext ⟨r, a⟩ ⟨s, b⟩
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type,
      decompressedCell, blockDiagonal_apply, emptyExtensionBlock, Matrix.one_apply]

/-- The decompressed operation preserves the empty-cell block. -/
theorem empty_mul_decompressedCell (W : Matrix Y Y ℂ) :
    (1 ⊗ₖ (Matrix.single none none 1 : Matrix (Option Y) (Option Y) ℂ)) *
        decompressedCell W =
      W ⊗ₖ (Matrix.single none none 1 : Matrix (Option Y) (Option Y) ℂ) := by
  ext ⟨r, a⟩ ⟨s, b⟩
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type,
      decompressedCell, blockDiagonal_apply, emptyExtensionBlock, Matrix.one_apply]

/-- The compressed operation restricted to the invalid sector acts as `W` on the response. -/
theorem compressedCell_mul_invalid (W : Matrix Y Y ℂ) :
    compressedCell W * ((1 : Matrix Y Y ℂ) ⊗ₖ cellInvalidProjector (Y := Y)) =
      W ⊗ₖ cellInvalidProjector (Y := Y) := by
  let F : Matrix (Y × Option Y) (Y × Option Y) ℂ := 1 ⊗ₖ cellCompress Y
  let S : Matrix (Y × Option Y) (Y × Option Y) ℂ := 1 ⊗ₖ Matrix.single none none 1
  have hFF : F * F = 1 := by
    simp only [F, ← mul_kronecker_mul, Matrix.one_mul, cellCompress_mul_self,
      one_kronecker_one]
  have hR : (1 : Matrix Y Y ℂ) ⊗ₖ cellInvalidProjector (Y := Y) = F * S * F := by
    simp only [F, S, cellInvalidProjector, ← mul_kronecker_mul, Matrix.one_mul]
  rw [hR]
  change (F * decompressedCell W * F) * (F * S * F) = _
  calc
    _ = F * decompressedCell W * (F * F) * S * F := by simp only [Matrix.mul_assoc]
    _ = F * (decompressedCell W * S) * F := by rw [hFF]; simp only [Matrix.mul_one,
      Matrix.mul_assoc]
    _ = _ := by
      rw [decompressedCell_mul_empty]
      simp only [F, cellInvalidProjector, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- The invalid sector is invariant on both sides of a compressed query. -/
theorem invalid_mul_compressedCell (W : Matrix Y Y ℂ) :
    ((1 : Matrix Y Y ℂ) ⊗ₖ cellInvalidProjector (Y := Y)) * compressedCell W =
      W ⊗ₖ cellInvalidProjector (Y := Y) := by
  let F : Matrix (Y × Option Y) (Y × Option Y) ℂ := 1 ⊗ₖ cellCompress Y
  let S : Matrix (Y × Option Y) (Y × Option Y) ℂ := 1 ⊗ₖ Matrix.single none none 1
  have hFF : F * F = 1 := by
    simp only [F, ← mul_kronecker_mul, Matrix.one_mul, cellCompress_mul_self,
      one_kronecker_one]
  have hR : (1 : Matrix Y Y ℂ) ⊗ₖ cellInvalidProjector (Y := Y) = F * S * F := by
    simp only [F, S, cellInvalidProjector, ← mul_kronecker_mul, Matrix.one_mul]
  rw [hR]
  change (F * S * F) * (F * decompressedCell W * F) = _
  calc
    _ = F * S * (F * F) * decompressedCell W * F := by simp only [Matrix.mul_assoc]
    _ = F * (S * decompressedCell W) * F := by rw [hFF]; simp only [Matrix.mul_one,
      Matrix.mul_assoc]
    _ = _ := by
      rw [empty_mul_decompressedCell]
      simp only [F, cellInvalidProjector, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- Every empty-sector extension agrees on the valid sector `ker (1 ⊗ R)`. -/
theorem compressedCell_mulVec_eq_of_valid (W V : Matrix Y Y ℂ)
    (ψ : Y × Option Y → ℂ) (hψ : ((1 : Matrix Y Y ℂ) ⊗ₖ cellInvalidProjector (Y := Y)) *ᵥ ψ = 0) :
    compressedCell W *ᵥ ψ = compressedCell V *ᵥ ψ := by
  apply sub_eq_zero.mp
  rw [← Matrix.sub_mulVec, compressedCell_sub]
  have h : (W - V) ⊗ₖ cellInvalidProjector (Y := Y) =
      ((W - V) ⊗ₖ (1 : Matrix (Option Y) (Option Y) ℂ)) *
        ((1 : Matrix Y Y ℂ) ⊗ₖ cellInvalidProjector (Y := Y)) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [h, ← Matrix.mulVec_mulVec, hψ, Matrix.mulVec_zero]

/-- A query preserves validity even if its empty-sector matrix is not assumed unitary. -/
theorem compressedCell_preserves_valid (W : Matrix Y Y ℂ) (ψ : Y × Option Y → ℂ)
    (hψ : ((1 : Matrix Y Y ℂ) ⊗ₖ cellInvalidProjector (Y := Y)) *ᵥ ψ = 0) :
    ((1 : Matrix Y Y ℂ) ⊗ₖ cellInvalidProjector (Y := Y)) *ᵥ (compressedCell W *ᵥ ψ) = 0 := by
  rw [Matrix.mulVec_mulVec, invalid_mul_compressedCell, ← compressedCell_mul_invalid,
    ← Matrix.mulVec_mulVec, hψ, Matrix.mulVec_zero]

end cell

/-! ## Query and database controls -/

section table

variable {X Y T : Type*}

/-- Move the response to the first factor and retain the input and database as controls. -/
@[expose]
def responseControlSplit : (X × Y) × T ≃ Y × (X × T) where
  toFun p := (p.1.2, p.1.1, p.2)
  invFun p := ((p.2.1, p.1), p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable [DecidableEq X] [DecidableEq Y] [DecidableEq T] [AddCommGroup Y]

/-- A decompressed table oracle with an explicit empty-sector response. The input and table
are controls; each filled value translates the response. -/
@[expose]
def extendedTableOracle (W : Matrix Y Y ℂ) (read : T → X → Option Y) :
    Matrix ((X × Y) × T) ((X × Y) × T) ℂ :=
  (blockDiagonal fun p : X × T ↦ emptyExtensionBlock W (read p.2 p.1)).submatrix
    responseControlSplit responseControlSplit

/-- The entries of the decompressed table extension. -/
theorem extendedTableOracle_apply (W : Matrix Y Y ℂ) (read : T → X → Option Y)
    (p q : (X × Y) × T) :
    extendedTableOracle W read p q =
      if (p.1.1, p.2) = (q.1.1, q.2) then
        emptyExtensionBlock W (read p.2 p.1.1) p.1.2 q.1.2 else 0 := rfl

/-- The identity empty-sector extension is the totalized table oracle. -/
theorem extendedTableOracle_one (read : T → X → Option Y) :
    extendedTableOracle 1 read = tableOracle (fun d x ↦ (read d x).getD 0) := by
  ext ⟨⟨x, r⟩, d⟩ ⟨⟨z, s⟩, e⟩
  by_cases hx : x = z
  · subst z
    by_cases hd : d = e
    · subst e
      cases h : read d x with
      | none => simp [extendedTableOracle_apply, emptyExtensionBlock, h, tableOracle_apply,
          tableOracleEquiv_apply, oracleEquiv_apply, Matrix.one_apply]
      | some y => simp [extendedTableOracle_apply, emptyExtensionBlock, h, tableOracle_apply,
          tableOracleEquiv_apply, oracleEquiv_apply]
    · simp [extendedTableOracle_apply, hd, tableOracle_apply, tableOracleEquiv_apply,
        oracleEquiv_apply]
  · simp [extendedTableOracle_apply, hx, tableOracle_apply, tableOracleEquiv_apply,
      oracleEquiv_apply]

variable [Fintype X] [Fintype Y] [Fintype T]

/-- The table extension is unitary for any unitary empty-sector response. -/
theorem extendedTableOracle_mem_unitaryGroup {W : Matrix Y Y ℂ}
    (hW : W ∈ unitaryGroup Y ℂ) (read : T → X → Option Y) :
    extendedTableOracle W read ∈ unitaryGroup ((X × Y) × T) ℂ :=
  reindex_mem_unitaryGroup responseControlSplit.symm
    (responseBlocks_mem_unitaryGroup fun _ ↦ emptyExtensionBlock_mem_unitaryGroup hW _)

/-- The table extension is an involution for exponent-two answers and involutive `W`. -/
theorem extendedTableOracle_mul_self (hY : ∀ y : Y, y + y = 0)
    {W : Matrix Y Y ℂ} (hW : W * W = 1) (read : T → X → Option Y) :
    extendedTableOracle W read * extendedTableOracle W read = 1 := by
  rw [extendedTableOracle, submatrix_mul_equiv, ← blockDiagonal_mul]
  have h : (fun p : X × T ↦ emptyExtensionBlock W (read p.2 p.1) *
      emptyExtensionBlock W (read p.2 p.1)) = 1 := by
    funext p
    cases read p.2 p.1 with
    | none => exact hW
    | some y => exact xorShift_mul_self_of_add_self hY y
  rw [h, blockDiagonal_one, submatrix_one_equiv]

end table

/-! ## The VC oracle -/

section vc

variable (k : ℕ) (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- The port `i` of the empty-sector extension, conjugated by compression of all databases.
Only the addressed cell is read by the decompressed operation. -/
@[expose]
noncomputable def extendedVCPort (W : Matrix Y Y ℂ) (i : Fin k) :
    Matrix ((X × Y) × (Fin k → Database X Y)) ((X × Y) × (Fin k → Database X Y)) ℂ :=
  (1 ⊗ₖ compressDatabases k X Y) *
    extendedTableOracle W (fun d x ↦ d i x) * (1 ⊗ₖ compressDatabases k X Y)

/-- Compression of all databases is unitary. -/
theorem compressDatabases_mem_unitaryGroup :
    compressDatabases k X Y ∈ unitaryGroup (Fin k → Database X Y) ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_compressDatabases,
    compressDatabases_mul_self]

/-- Every extended VC port is unitary. -/
theorem extendedVCPort_mem_unitaryGroup {W : Matrix Y Y ℂ}
    (hW : W ∈ unitaryGroup Y ℂ) (i : Fin k) :
    extendedVCPort k X Y W i ∈ unitaryGroup ((X × Y) × (Fin k → Database X Y)) ℂ := by
  have hF := kronecker_mem_unitary (one_mem (unitaryGroup (X × Y) ℂ))
    (compressDatabases_mem_unitaryGroup k X Y)
  exact mul_mem (mul_mem hF (extendedTableOracle_mem_unitaryGroup hW _)) hF

/-- The empty-sector emulation witness: one independently initialized empty database per
oracle index. A flat zero column of `W` gives the accepting amplitudes of the Hadamard witness. -/
@[expose]
noncomputable def extendedVCOracle (W : Matrix Y Y ℂ) (hW : W ∈ unitaryGroup Y ℂ) :
    VCOracle k X Y where
  S := QReg.of (Fin k → Database X Y)
  init := SubState.basis fun _ ↦ Database.empty
  U := extendedVCPort k X Y W
  unitary := extendedVCPort_mem_unitaryGroup k X Y hW

/-- The witness starts with every database empty. -/
theorem extendedVCOracle_init (W : Matrix Y Y ℂ) (hW : W ∈ unitaryGroup Y ℂ) :
    (extendedVCOracle k X Y W hW).init = SubState.basis fun _ ↦ Database.empty := rfl

/-- The public oracle port is the explicitly conjugated extended port. -/
theorem extendedVCOracle_U (W : Matrix Y Y ℂ) (hW : W ∈ unitaryGroup Y ℂ) (i : Fin k) :
    (extendedVCOracle k X Y W hW).U i = extendedVCPort k X Y W i := rfl

/-- With identity response on an empty cell, the extended port is the existing compressed
VC port. All results about that existing witness retain their scope. -/
theorem extendedVCPort_one (i : Fin k) :
    extendedVCPort k X Y 1 i = (compressedVCOracle k X Y).U i := by
  rw [extendedVCPort, extendedTableOracle_one, compressedVCOracle_U_eq_conj]
  rfl

/-- Each extended VC port is an involution when the response blocks are involutions. -/
theorem extendedVCPort_mul_self (hY : ∀ y : Y, y + y = 0)
    {W : Matrix Y Y ℂ} (hW : W * W = 1) (i : Fin k) :
    extendedVCPort k X Y W i * extendedVCPort k X Y W i = 1 := by
  let F : Matrix ((X × Y) × (Fin k → Database X Y))
      ((X × Y) × (Fin k → Database X Y)) ℂ := 1 ⊗ₖ compressDatabases k X Y
  let C := extendedTableOracle W (fun d : Fin k → Database X Y ↦ d i)
  have hF : F * F = 1 := by
    simp only [F, one_kronecker_mul_one_kronecker, compressDatabases_mul_self,
      one_kronecker_one]
  have hC : C * C = 1 := extendedTableOracle_mul_self hY hW _
  change (F * C * F) * (F * C * F) = 1
  calc
    _ = F * C * (F * F) * C * F := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [hF, Matrix.mul_one, Matrix.mul_assoc F C C, hC, Matrix.mul_one, hF]

end vc

end Quantum
