/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldResponse
import all VCVio.Quantum.VC.Tuples

/-!
# Concrete response factors for the old Merkle checker

The full tuple uses complementary before/after component sets. The remaining response
factor is its database-independent length code. Reference registers are preserved.
-/

public section

open Matrix
open scoped Kronecker
namespace Quantum.MatrixMap

variable {S Z B : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] [Fintype B] [DecidableEq B]

/-- A constant response translation commutes with every database operator. -/
theorem responseTranslation_const_commute (z : Z) (M : Matrix S S ℂ) :
    Commute (responseTranslation (fun _ : S ↦ z)) (M ⊗ₖ (1 : Matrix Z Z ℂ)) := by
  change ((1 : Matrix S S ℂ) ⊗ₖ xorShift Z z) * (M ⊗ₖ 1) =
    (M ⊗ₖ 1) * ((1 : Matrix S S ℂ) ⊗ₖ xorShift Z z)
  rw [← mul_kronecker_mul, ← mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]

/-- A reference-amplified database operator commutes with a response translation whenever
its nonzero matrix entries preserve the controlling label. -/
theorem reference_responseTranslation_commute (β : S → Z) (M : Matrix S S ℂ)
    (hM : ∀ a b, M a b ≠ 0 → β a = β b) :
    Commute (responseTranslation (fun a : B × S ↦ β a.2))
      (((1 : Matrix B B ℂ) ⊗ₖ M) ⊗ₖ (1 : Matrix Z Z ℂ)) := by
  unfold responseTranslation
  apply response_commute_of_support (fun a : B × S ↦ β a.2) (xorShift Z)
    ((1 : Matrix B B ℂ) ⊗ₖ M)
  intro a b h
  exact hM a.2 b.2 (right_ne_zero_of_mul (by simpa only [kroneckerMap_apply] using h))

omit [AddCommGroup Z] in
/-- Conjugated diagonal database operators commute, also with a reference and response. -/
theorem reference_conjugated_diagonals_commute
    (C : Matrix S S ℂ) (hC : C * C = 1) (p q : S → ℂ) :
    Commute (((1 : Matrix B B ℂ) ⊗ₖ (C * diagonal p * C)) ⊗ₖ (1 : Matrix Z Z ℂ))
      (((1 : Matrix B B ℂ) ⊗ₖ (C * diagonal q * C)) ⊗ₖ (1 : Matrix Z Z ℂ)) := by
  change _ * _ = _ * _
  simp only [← mul_kronecker_mul, Matrix.one_mul,
    CompressedReplay.conjugate_mul C hC]
  rw [(commute_diagonal p q).eq]

end Quantum.MatrixMap

namespace Quantum.SaltedMerkle
open _root_.SaltedMerkle
open MatrixMap

variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Nonempty Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  (enc : Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)

/-- Component response locality yields commutation after adjoining an arbitrary reference.
The hypothesis is disjointness of position sets; duplicate-index tuples are constant blocks. -/
theorem batchResponse_reference_commute (hk : 1 ≤ k) (idx : Fin k → Fin k)
    (cm : Fin k → Y) (W I : Finset (Fin k)) (hWI : Disjoint W I) (B : QReg)
    (p : Fin k → Database X Y → Prop) [∀ i D, Decidable (p i D)] :
    let Z := TpDCode.ConcatReg k (DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)))
    let β := TpDCode.partResponse (multiExtract enc d) I (TpIC.full hk idx cm)
    let K := compressDatabases k X Y * diagonal
      (fun D : Fin k → Database X Y ↦ if ∀ i ∈ W, p i (D (idx i)) then (1 : ℂ) else 0) *
        compressDatabases k X Y
    Commute (responseTranslation (fun a : B × (Fin k → Database X Y) ↦ β a.2))
      (((1 : Matrix B B ℂ) ⊗ₖ K) ⊗ₖ (1 : Matrix Z Z ℂ)) := by
  classical
  dsimp only
  apply reference_responseTranslation_commute
  intro D D' hK
  by_cases hi : Function.Injective idx
  · apply partResponse_full_eq enc d
    intro i hiI
    have hs := conjugated_batch_support p idx W (compressAll X Y)
      (compressAll_mul_self X Y) D D'
    refine hs ?_ (idx i) ?_
    · convert hK using 1
      simp only [compressDatabases, Matrix.mul_apply, diagonal_apply]
      congr! 6
    · intro hj
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hj
      exact Finset.disjoint_left.mp hWI ((hi he) ▸ hj) hiI
  · exact partResponse_full_eq_of_not_injective enc d hk idx cm I D D' hi

/-- The disjoint-batch identity for the concrete concatenated Merkle response, with an
arbitrary reference register. Both checker predicates may be instantiated independently. -/
theorem full_response_reference_factor (hk : 1 ≤ k) (idx : Fin k → Fin k)
    (cm : Fin k → Y) (W : Finset (Fin k)) (B : QReg)
    (p q : Fin k → Database X Y → Prop) [∀ i D, Decidable (p i D)]
    [∀ i D, Decidable (q i D)] :
    let Z := TpDCode.ConcatReg k (DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)))
    let tic := TpIC.full hk idx cm
    let A := fun W ↦
      (((1 : Matrix B B ℂ) ⊗ₖ (compressDatabases k X Y * diagonal
        (fun D : Fin k → Database X Y ↦ if ∀ i ∈ W, p i (D (idx i)) then (1 : ℂ) else 0) *
          compressDatabases k X Y)) ⊗ₖ (1 : Matrix Z Z ℂ))
    let Q := fun W ↦
      (((1 : Matrix B B ℂ) ⊗ₖ (compressDatabases k X Y * diagonal
        (fun D : Fin k → Database X Y ↦ if ∀ i ∈ W, q i (D (idx i)) then (1 : ℂ) else 0) *
          compressDatabases k X Y)) ⊗ₖ (1 : Matrix Z Z ℂ))
    let V := fun I ↦ responseTranslation (fun a : B × (Fin k → Database X Y) ↦
      TpDCode.partResponse (multiExtract enc d) I tic a.2)
    let L := responseTranslation (fun _ : B × (Fin k → Database X Y) ↦
      (((k : ZMod (k + 1)), 0) : Z))
    let U := responseTranslation (fun a : B × (Fin k → Database X Y) ↦
      (TpDCode.concat (Dm := DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)))).enc
        ⟨tic.1, (multiExtract enc d).extract tic a.2⟩)
    A Wᶜ * U * A W - Q Wᶜ * U * Q W =
      L * V W * (A W * A Wᶜ - Q W * Q Wᶜ) * V Wᶜ := by
  classical
  dsimp only
  let Z := TpDCode.ConcatReg k (DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)))
  let tic := TpIC.full hk idx cm
  have he (a : B × (Fin k → Database X Y)) :
      (TpDCode.concat (Dm := DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)))).enc
        ⟨tic.1, (multiExtract enc d).extract tic a.2⟩ =
      (((k : ZMod (k + 1)), 0) : Z) +
        (TpDCode.partResponse (multiExtract enc d) W tic a.2 +
          TpDCode.partResponse (multiExtract enc d) Wᶜ tic a.2) := by
    rw [TpDCode.concat_response]
    rw [← TpDCode.partResponse_union (multiExtract enc d) W Wᶜ
      (disjoint_compl_right), Finset.union_compl]
    rfl
  have hf : (fun a : B × (Fin k → Database X Y) ↦
      (TpDCode.concat (Dm := DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)))).enc
        ⟨tic.1, (multiExtract enc d).extract tic a.2⟩) =
      (fun a : B × (Fin k → Database X Y) ↦ (((k : ZMod (k + 1)), 0) : Z) +
        (TpDCode.partResponse (multiExtract enc d) W tic a.2 +
          TpDCode.partResponse (multiExtract enc d) Wᶜ tic a.2)) := funext he
  rw [hf, responseTranslation_add, responseTranslation_add]
  rw [← Matrix.mul_assoc
    (responseTranslation (fun _ : B × (Fin k → Database X Y) ↦ (((k : ZMod (k + 1)), 0) : Z)))]
  apply checker_batches_factor
  · exact (responseTranslation_const_commute _ _).symm
  · exact (responseTranslation_const_commute _ _).symm
  · exact (batchResponse_reference_commute enc d hk idx cm Wᶜ W
      disjoint_compl_left B p).symm
  · exact (batchResponse_reference_commute enc d hk idx cm Wᶜ W
      disjoint_compl_left B q).symm
  · exact batchResponse_reference_commute enc d hk idx cm W Wᶜ
      disjoint_compl_right B p
  · exact batchResponse_reference_commute enc d hk idx cm W Wᶜ
      disjoint_compl_right B q
  · exact reference_conjugated_diagonals_commute _ (compressDatabases_mul_self k X Y) _ _
  · exact reference_conjugated_diagonals_commute _ (compressDatabases_mul_self k X Y) _ _

end Quantum.SaltedMerkle
