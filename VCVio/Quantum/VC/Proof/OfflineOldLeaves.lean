/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldComparison

/-!
# Homogeneous invalid-norm increments for adaptive leaves

The terminal component increment retains the input trace. This is necessary when summing
over adversary leaves: replacing each substate's trace by one before the sum would charge
one constant per leaf. All quantities remain in extended nonnegative reals.
-/

public section

open Matrix
open scoped ComplexOrder Kronecker ENNReal
namespace Quantum

variable {C Y Z κ : Type*} [Fintype C] [DecidableEq C] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

/-- The homogeneous component increment on arbitrary positive inputs. The additive amplitude
contains the input trace, so it can be summed over arbitrary dependent adversary leaves. -/
theorem databaseControl_invalid_increment_weighted [Nonempty Y] [DecidableEq κ]
    (β : Database C Y → κ) (U : κ → Matrix Z Z ℂ)
    (hU : ∀ a, U a ∈ unitaryGroup Z ℂ) (s : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hβ : ∀ D : Database C Y, D.size ≤ s → ∀ c, (D c).isSome →
      changingFraction β c (fun i ↦ D i.1) ≤ a)
    {ρ : Matrix (Database C Y × Z) (Database C Y × Z) ℂ} (hρ : ρ.PosSemidef)
    (hpop : populationCut s * ρ = ρ) :
    let V := databaseControl β U
    let R := fun c : C ↦ databaseInvalidCell (Y := Y) (Z := Z) c
    (∑' c, ENNReal.ofReal (MatrixMap.conj (R c) (MatrixMap.conj V ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' c, ENNReal.ofReal (MatrixMap.conj (R c) ρ).trace.re) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (4 * s * a) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
  dsimp only
  let V := databaseControl β U
  let R := fun c : C ↦ databaseInvalidCell (Y := Y) (Z := Z) c
  have hV : Vᴴ * V = 1 := mem_unitaryGroup_iff'.mp (databaseControl_unitary β U hU)
  have htriangle := MatrixMap.rpow_inv_two_tsum_conj_unitary_le R V hV hρ
  refine htriangle.trans (add_le_add le_rfl ?_)
  have he (c : C) : MatrixMap.conj (R c * V - V * R c) ρ =
      MatrixMap.conj (V * R c - R c * V) ρ := by
    have hneg : R c * V - V * R c = -(V * R c - R c * V) := by abel
    rw [hneg]
    simp only [MatrixMap.conj_apply, conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg,
      neg_neg]
  simp only [he]
  exact ENNReal.rpow_le_rpow
    (databaseControl_leakage_trace_le β U hU s ha hβ hρ hpop) (by norm_num)

omit [Fintype Z] [DecidableEq Z] in
/-- Homogeneous component increments sum over arbitrary leaf types with changing registers.
The error is charged to the total leaf mass, rather than once per leaf. -/
theorem databaseControl_invalid_leaf_sum_le [Nonempty Y] {L : Type*}
    (Z κ : L → Type*) [∀ l, Fintype (Z l)] [∀ l, DecidableEq (Z l)]
    [∀ l, DecidableEq (κ l)] (β : ∀ l, Database C Y → κ l)
    (U : ∀ l, κ l → Matrix (Z l) (Z l) ℂ)
    (hU : ∀ l a, U l a ∈ unitaryGroup (Z l) ℂ) (s : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hβ : ∀ l (D : Database C Y), D.size ≤ s → ∀ c, (D c).isSome →
      changingFraction (β l) c (fun i ↦ D i.1) ≤ a)
    (ρ : ∀ l, Matrix (Database C Y × Z l) (Database C Y × Z l) ℂ)
    (hρ : ∀ l, (ρ l).PosSemidef) (hpop : ∀ l, populationCut s * ρ l = ρ l) :
    let V := fun l ↦ databaseControl (β l) (U l)
    let R := fun l c ↦ databaseInvalidCell (Y := Y) (Z := Z l) c
    (∑' l, ∑' c, ENNReal.ofReal
      (MatrixMap.conj (R l c) (MatrixMap.conj (V l) (ρ l))).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' l, ∑' c, ENNReal.ofReal (MatrixMap.conj (R l c) (ρ l)).trace.re) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (4 * s * a) * ∑' l, ENNReal.ofReal (ρ l).trace.re) ^ (2⁻¹ : ℝ) := by
  have hh := rpow_inv_two_tsum_le_of_le_add (fun l ↦
    databaseControl_invalid_increment_weighted (β l) (U l) (hU l) s ha
      (hβ l) (hρ l) (hpop l))
  simpa only [ENNReal.tsum_mul_left] using hh

end Quantum

namespace Quantum.SaltedMerkle

variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Nonempty Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]

/-- The Merkle component increment with its substate weight retained. Any function of the
extraction output is allowed, including component selections and rejected duplicate-index blocks. -/
theorem extraction_invalid_increment_weighted
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (tic : TpIC k Y) {κ Z : Type*} [Fintype Z] [DecidableEq Z]
    (f : TpDLen k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))) tic.1 → κ)
    (U : κ → Matrix Z Z ℂ) (hU : ∀ a, U a ∈ unitaryGroup Z ℂ) (s : ℕ)
    {ρ : Matrix (Database (Fin k × X) Y × Z) (Database (Fin k × X) Y × Z) ℂ}
    (hρ : ρ.PosSemidef) (hpop : populationCut s * ρ = ρ) :
    let V := databaseControl
      (fun D ↦ f ((_root_.SaltedMerkle.multiExtract enc d).extract tic (Function.curry D))) U
    let R := fun c : Fin k × X ↦ databaseInvalidCell (Y := Y) (Z := Z) c
    (∑' c, ENNReal.ofReal (MatrixMap.conj (R c) (MatrixMap.conj V ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' c, ENNReal.ofReal (MatrixMap.conj (R c) ρ).trace.re) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (4 * s * oldChangingFraction (Fintype.card Y) s) *
          ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
  classical
  exact databaseControl_invalid_increment_weighted _ U hU s
    (le_min (by norm_num) (by positivity))
    (fun D hD c hc ↦ extraction_changingFraction_le enc d tic f D s hD c hc) hρ hpop

end Quantum.SaltedMerkle
