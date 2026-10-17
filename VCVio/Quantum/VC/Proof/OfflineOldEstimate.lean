/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldTransport
import all VCVio.Quantum.VC.Proof.CheckerComparison

/-!
# Original-state actual-to-filled checker estimate

The response dilation identifies the retained branch weights. Its disjoint component
factorization moves the checker discrepancy next to one component translation of the original
state, where the homogeneous invalid-norm increment applies.
-/

public section

open Matrix
open scoped ComplexOrder Kronecker ENNReal
namespace Quantum.MatrixMap

/-- A Gram domination bounds the conjugation weight by a sum of observable weights. -/
theorem conj_weight_le_sum_of_gram {A C : Type*} [Fintype A] [Fintype C]
    (K : Matrix A A ℂ) (R : C → Matrix A A ℂ)
    (h : ((∑ c, (R c)ᴴ * R c) - Kᴴ * K).PosSemidef)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ENNReal.ofReal (conj K ρ).trace.re ≤
      ∑' c, ENNReal.ofReal (conj (R c) ρ).trace.re := by
  have hh := h.trace_mul_re_nonneg hρ
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re,
    Finset.sum_mul, Matrix.trace_sum, Complex.re_sum] at hh
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg
    (fun c _ ↦ ((isCP_conj _).posSemidef hρ).trace_re_nonneg)]
  simp only [trace_conj_apply]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Response translations preserve the trace of every joint matrix. -/
theorem trace_conj_responseTranslation {A Z : Type*} [Fintype A] [DecidableEq A]
    [Fintype Z] [DecidableEq Z] [AddGroup Z] (β : A → Z)
    (ρ : Matrix (A × Z) (A × Z) ℂ) : (conj (responseTranslation β) ρ).trace = ρ.trace :=
  isTP_conj (mem_unitaryGroup_iff'.mp (responseTranslation_unitary β)) ρ

end Quantum.MatrixMap
namespace Quantum
open MatrixMap

variable {k : ℕ} {X Y Msg Cm : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (io : ∀ i, (VC i).CheckIOForm)

/-- The full checker discrepancy is dominated by the invalid cells with both a reference
and a response register. Malformed claims are included. -/
theorem response_batch_difference_le_invalid (c : OpeningClaim k Cm Msg ℓ Pf)
    {B Z : Type*} [Fintype B] [DecidableEq B] [Fintype Z] [DecidableEq Z]
    {ρ : Matrix ((B × (Fin k → Database X Y)) × Z) _ ℂ} (hρ : ρ.PosSemidef) :
    ENNReal.ofReal (conj
      (((1 : Matrix B B ℂ) ⊗ₖ
        (actualBatch io Finset.univ c - filledBatch io Finset.univ c)) ⊗ₖ
          (1 : Matrix Z Z ℂ)) ρ).trace.re ≤
      ∑' x : Fin k × X, ENNReal.ofReal (conj
        (((1 : Matrix B B ℂ) ⊗ₖ CompressedReplay.invalid x) ⊗ₖ
          (1 : Matrix Z Z ℂ)) ρ).trace.re := by
  apply conj_weight_le_sum_of_gram _ _ _ hρ
  have hg := ((PosSemidef.one (n := B)).kronecker
    (actualBatch_sub_filledBatch_gram_le io c)).kronecker (PosSemidef.one (n := Z))
  rw [CompressedReplay.invalidStack_gram] at hg
  convert hg using 1
  simp only [conjTranspose_kronecker, conjTranspose_one,
    CompressedReplay.invalid_hermitian, ← mul_kronecker_mul, Matrix.one_mul,
    CompressedReplay.invalid_idempotent]
  ext a b
  simp only [Matrix.sub_apply, Matrix.sum_apply, kroneckerMap_apply,
    Finset.sum_mul, Finset.mul_sum, sub_mul, mul_sub]

end Quantum

namespace Quantum.SaltedMerkle
open _root_.SaltedMerkle MatrixMap

variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt] [AddCommGroup Y]
  (enc : Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ) {Pf : Fin k → Type}
  {VC : ∀ i, VectorCommitment X Y Msg Y (Td Y Salt (d i)) (Pf i) (2 ^ d i)}
  (io : ∀ i, (VC i).CheckIOForm)

/-- The actual and filled checker batches factor around the concrete full Merkle response,
including malformed claims and rejected duplicate indices. -/
theorem checker_response_factor (hk : 1 ≤ k)
    (c : OpeningClaim k Y Msg (fun i ↦ 2 ^ d i) Pf) (B : QReg) :
    let Z := TpDCode.ConcatReg k (DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)))
    let tic := TpIC.full hk c.idx c.cm
    let A := fun W ↦ ((1 : Matrix B B ℂ) ⊗ₖ actualBatch io W c) ⊗ₖ (1 : Matrix Z Z ℂ)
    let Q := fun W ↦ ((1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c) ⊗ₖ (1 : Matrix Z Z ℂ)
    let V := fun I ↦ responseTranslation (fun a : B × (Fin k → Database X Y) ↦
      TpDCode.partResponse (multiExtract enc d) I tic a.2)
    let L := responseTranslation (fun _ : B × (Fin k → Database X Y) ↦
      (((k : ZMod (k + 1)), 0) : Z))
    let U := responseTranslation (fun a : B × (Fin k → Database X Y) ↦
      (TpDCode.concat (Dm := DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)))).enc
        ⟨tic.1, (multiExtract enc d).extract tic a.2⟩)
    A c.Wᶜ * U * A c.W - Q c.Wᶜ * U * Q c.W =
      L * V c.W * (((1 : Matrix B B ℂ) ⊗ₖ
        (actualBatch io Finset.univ c - filledBatch io Finset.univ c)) ⊗ₖ
          (1 : Matrix Z Z ℂ)) * V c.Wᶜ := by
  classical
  have hh := full_response_reference_factor enc d hk c.idx c.cm c.W B
    (fun i D ↦ (io i).checkOn (fun x ↦ some (D.lookup x)) (c.cm i) (c.ans i) (c.pf i))
    (fun i D ↦ (io i).checkOn D (c.cm i) (c.ans i) (c.pf i))
  change _ = _ * _ * (_ * _ - _ * _) * _ at hh
  change _ = _
  refine hh.trans ?_
  congr 2
  change
    (((1 : Matrix B B ℂ) ⊗ₖ actualBatch io c.W c) ⊗ₖ _) *
        ((1 ⊗ₖ actualBatch io c.Wᶜ c) ⊗ₖ _) -
      ((1 ⊗ₖ filledBatch io c.W c) ⊗ₖ _) * ((1 ⊗ₖ filledBatch io c.Wᶜ c) ⊗ₖ _) = _
  simp only [← mul_kronecker_mul, Matrix.one_mul, actualBatch_mul_compl,
    filledBatch_mul_compl]
  ext a b
  simp only [Matrix.sub_apply, kroneckerMap_apply, sub_mul, mul_sub]

/-- The coherent two-batch discrepancy is bounded by the invalid weight after translating
only the after-batch response component. The input remains the original state. -/
theorem response_difference_le_invalid (hk : 1 ≤ k)
    (c : OpeningClaim k Y Msg (fun i ↦ 2 ^ d i) Pf) (B : QReg)
    (ρ : Matrix ((B × (Fin k → Database X Y)) ×
      TpDCode.ConcatReg k (DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)))) _ ℂ)
    (hρ : ρ.PosSemidef) :
    let Z := TpDCode.ConcatReg k (DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)))
    let tic := TpIC.full hk c.idx c.cm
    let A := fun W ↦ ((1 : Matrix B B ℂ) ⊗ₖ actualBatch io W c) ⊗ₖ (1 : Matrix Z Z ℂ)
    let Q := fun W ↦ ((1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c) ⊗ₖ (1 : Matrix Z Z ℂ)
    let V := responseTranslation (fun a : B × (Fin k → Database X Y) ↦
      TpDCode.partResponse (multiExtract enc d) c.Wᶜ tic a.2)
    let U := responseTranslation (fun a : B × (Fin k → Database X Y) ↦
      (TpDCode.concat (Dm := DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)))).enc
        ⟨tic.1, (multiExtract enc d).extract tic a.2⟩)
    ENNReal.ofReal (conj (A c.Wᶜ * U * A c.W - Q c.Wᶜ * U * Q c.W) ρ).trace.re ≤
      ∑' x : Fin k × X, ENNReal.ofReal (conj
        (((1 : Matrix B B ℂ) ⊗ₖ CompressedReplay.invalid x) ⊗ₖ
          (1 : Matrix Z Z ℂ)) (conj V ρ)).trace.re := by
  classical
  dsimp only
  rw [checker_response_factor enc d io hk c B]
  rw [Matrix.mul_assoc _ _ (responseTranslation _), MatrixMap.conj_mul, LinearMap.comp_apply]
  rw [MatrixMap.conj_mul, LinearMap.comp_apply, trace_conj_responseTranslation,
    trace_conj_responseTranslation, MatrixMap.conj_mul, LinearMap.comp_apply]
  exact response_batch_difference_le_invalid io c ((isCP_conj _).posSemidef hρ)

variable [∀ i, DecidableEq (DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)) i)]

/-- The retained actual-to-filled difference is bounded on the original population-supported
state by its invalid amplitude plus the trace-weighted component increment, as in FIX (26b).
No population assumption is made on a state after a checker. -/
theorem measured_actual_filled_le_invalid (hk : 1 ≤ k)
    (c : OpeningClaim k Y Msg (fun i ↦ 2 ^ d i) Pf) (B : QReg) (s : ℕ)
    {ρ : Matrix (B × (Fin k → Database X Y)) _ ℂ} (hρ : ρ.PosSemidef)
    (hpop : diagonal (fun a : B × (Fin k → Database X Y) ↦
      if databasePopulation a.2 ≤ s then (1 : ℂ) else 0) * ρ = ρ) :
    (∑' tdm, ENNReal.ofReal (conj ((1 : Matrix B B ℂ) ⊗ₖ
      (actualBatch io c.Wᶜ c * extractProj (multiExtract enc d)
          (TpIC.full hk c.idx c.cm) tdm * actualBatch io c.W c -
        filledBatch io c.Wᶜ c * extractProj (multiExtract enc d)
          (TpIC.full hk c.idx c.cm) tdm * filledBatch io c.W c)) ρ).trace.re) ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.potential (CompressedReplay.invalidStack (k := k) (X := X) (Y := Y)) ρ) ^
          (2⁻¹ : ℝ) +
        (ENNReal.ofReal (4 * s * oldChangingFraction (Fintype.card Y) s) *
          ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
  classical
  let Dm := DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i))
  let Z := TpDCode.ConcatReg k Dm
  let tic := TpIC.full hk c.idx c.cm
  let β := fun a : B × (Fin k → Database X Y) ↦ (multiExtract enc d).extract tic a.2
  let ec := fun tdm : TpDLen k Dm tic.1 ↦ (TpDCode.concat (Dm := Dm)).enc ⟨tic.1, tdm⟩
  have hec : Function.Injective ec := by
    intro a b h
    have hh := (TpDCode.concat (Dm := Dm)).enc_injective h
    exact (Sigma.mk.inj_iff.mp hh).2.eq
  let A := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ actualBatch io W c
  let Q := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c
  let J := responseInclusion (A := B × (Fin k → Database X Y)) (0 : Z)
  let σ := conj J ρ
  have hσ : σ.PosSemidef := (isCP_conj J).posSemidef hρ
  have hd := encoded_checked_difference_eq_response β ec hec
    (A c.W) (A c.Wᶜ) (Q c.W) (Q c.Wᶜ) hρ
  have hp (tdm) : labelProjector β tdm = (1 : Matrix B B ℂ) ⊗ₖ
      extractProj (multiExtract enc d) tic tdm := by
    simp only [labelProjector, extractProj, ← diagonal_one, diagonal_kronecker_diagonal,
      one_mul]
    rfl
  have hm (tdm) : A c.Wᶜ * labelProjector β tdm * A c.W -
      Q c.Wᶜ * labelProjector β tdm * Q c.W = (1 : Matrix B B ℂ) ⊗ₖ
        (actualBatch io c.Wᶜ c * extractProj (multiExtract enc d) tic tdm *
            actualBatch io c.W c - filledBatch io c.Wᶜ c *
              extractProj (multiExtract enc d) tic tdm * filledBatch io c.W c) := by
    rw [hp]
    simp only [A, Q, ← mul_kronecker_mul, Matrix.one_mul]
    ext a b
    simp only [Matrix.sub_apply, kroneckerMap_apply, mul_sub]
  simp_rw [hm] at hd
  rw [hd]
  have hb := response_difference_le_invalid enc d io hk c B σ hσ
  have hf := partResponse_zero_invalid_increment enc d tic c.Wᶜ B s hρ hpop
  exact (ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 2⁻¹)).trans hf

end Quantum.SaltedMerkle
