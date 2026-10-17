/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldFactor

/-!
# Register transport for the original-state checker estimate

Database flattening and reference/response reassociation preserve traces, invalid-cell weights,
and population support. The component increment therefore applies before any checker acts.
-/

public section

open Matrix
open scoped ComplexOrder Kronecker ENNReal
namespace Quantum.MatrixMap

/-- Inclusion into an initialized response basis state, with separate component instances. -/
@[expose]
def responseInclusion {A Z : Type*} [DecidableEq A] [DecidableEq Z] (z : Z) :
    Matrix (A × Z) A ℂ := basisMatrix (fun a ↦ (a, z))

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Relabelling both indices by an equivalence preserves the trace. -/
theorem trace_submatrix_equiv (e : A ≃ B) (ρ : Matrix B B ℂ) :
    (ρ.submatrix e e).trace = ρ.trace := by
  exact e.sum_comp (fun b ↦ ρ b b)

/-- Conjugation commutes with bijective changes of basis. -/
theorem conj_submatrix_equiv (e : A ≃ B) (K ρ : Matrix B B ℂ) :
    conj (K.submatrix e e) (ρ.submatrix e e) = (conj K ρ).submatrix e e := by
  simp only [conj_apply, conjTranspose_submatrix, submatrix_mul_equiv]

/-- Conjugation weights are unchanged by bijective reindexing of the joint register. -/
theorem trace_conj_submatrix_equiv (e : A ≃ B) (K ρ : Matrix B B ℂ) :
    (conj (K.submatrix e e) (ρ.submatrix e e)).trace = (conj K ρ).trace := by
  rw [conj_submatrix_equiv, trace_submatrix_equiv]

/-- Inserting a zero response preserves every original observable's conjugation weight. -/
theorem trace_conj_zero_response [DecidableEq A] [DecidableEq B] [AddGroup B]
    (K ρ : Matrix A A ℂ) :
    (conj (K ⊗ₖ (1 : Matrix B B ℂ))
      (conj (basisMatrix (fun a : A ↦ (a, (0 : B)))) ρ)).trace = (conj K ρ).trace := by
  let J := basisMatrix (fun a : A ↦ (a, (0 : B)))
  have hJ : Jᴴ * J = 1 := conjTranspose_basisMatrix_mul_self
    (fun _ _ h ↦ congrArg Prod.fst h)
  rw [← LinearMap.comp_apply, ← conj_mul, zero_response_intertwines,
    conj_mul, LinearMap.comp_apply]
  exact isTP_conj hJ _

/-- Adjoining a fresh zero response preserves the support equation for every original operator. -/
theorem supported_zero_response [DecidableEq A] [DecidableEq B] [AddGroup B]
    (P ρ : Matrix A A ℂ) (h : P * ρ = ρ) :
    (P ⊗ₖ (1 : Matrix B B ℂ)) *
        conj (basisMatrix (fun a : A ↦ (a, (0 : B)))) ρ =
      conj (basisMatrix (fun a : A ↦ (a, (0 : B)))) ρ := by
  rw [conj_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, zero_response_intertwines,
    Matrix.mul_assoc _ P, h]

/-- A fixed response basis state intertwines every operator on the original register. -/
theorem response_inclusion_intertwines [DecidableEq A] [DecidableEq B]
    (z : B) (K : Matrix A A ℂ) :
    (K ⊗ₖ (1 : Matrix B B ℂ)) * basisMatrix (fun a : A ↦ (a, z)) =
      basisMatrix (fun a : A ↦ (a, z)) * K := by
  ext ⟨a, b⟩ a'
  simp only [Matrix.mul_apply, basisMatrix_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, kroneckerMap_apply, one_apply,
    Prod.mk.injEq]
  by_cases h : b = z <;> simp [h]

/-- Inserting any fixed response basis state preserves the original conjugation weight. -/
theorem trace_conj_response_inclusion [DecidableEq A] [DecidableEq B]
    (z : B) (K ρ : Matrix A A ℂ) :
    (conj (K ⊗ₖ (1 : Matrix B B ℂ))
      (conj (basisMatrix (fun a : A ↦ (a, z))) ρ)).trace = (conj K ρ).trace := by
  rw [← LinearMap.comp_apply, ← conj_mul, response_inclusion_intertwines,
    conj_mul, LinearMap.comp_apply]
  exact isTP_conj (conjTranspose_basisMatrix_mul_self
    (fun _ _ h ↦ congrArg Prod.fst h)) _

/-- Inserting any fixed response basis state preserves original support equations. -/
theorem supported_response_inclusion [DecidableEq A] [DecidableEq B]
    (z : B) (P ρ : Matrix A A ℂ) (h : P * ρ = ρ) :
    (P ⊗ₖ (1 : Matrix B B ℂ)) * conj (basisMatrix (fun a : A ↦ (a, z))) ρ =
      conj (basisMatrix (fun a : A ↦ (a, z))) ρ := by
  rw [conj_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, response_inclusion_intertwines,
    Matrix.mul_assoc _ P, h]

end Quantum.MatrixMap

namespace Quantum
open MatrixMap

variable {k : ℕ} {X Y : Type} {B Z : Type*}

/-- Flatten the database family while grouping the reference and response registers. -/
@[expose]
def responseDatabaseEquiv :
    ((B × (Fin k → Database X Y)) × Z) ≃ (Database (Fin k × X) Y × (B × Z)) where
  toFun a := (Function.uncurry a.1.2, (a.1.1, a.2))
  invFun a := ((a.2.1, Function.curry a.1), a.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype X] [DecidableEq Y]
  [DecidableEq B] [DecidableEq Z]

/-- Database-controlled response translations retain an arbitrary reference under flattening. -/
theorem responseTranslation_flat [AddGroup Z]
    (β : (Fin k → Database X Y) → Z) :
    (databaseControl (fun D ↦ β (Function.curry D))
      (fun z ↦ (1 : Matrix B B ℂ) ⊗ₖ xorShift Z z)).submatrix
        responseDatabaseEquiv responseDatabaseEquiv =
      responseTranslation (fun a : B × (Fin k → Database X Y) ↦ β a.2) := by
  ext ⟨⟨b, D⟩, z⟩ ⟨⟨b', D'⟩, z'⟩
  simp only [databaseControl, responseTranslation, labelControlled_apply,
    submatrix_apply, kroneckerMap_apply, one_apply]
  change (if Function.uncurry D = Function.uncurry D' then (1 : ℂ) else 0) *
      ((if b = b' then 1 else 0) * xorShift Z (β D) z z') =
    (if (b, D) = (b', D') then 1 else 0) * xorShift Z (β D) z z'
  have he : Function.uncurry D = Function.uncurry D' ↔ D = D' :=
    (Equiv.curry (Fin k) X (Option Y)).symm.injective.eq_iff
  simp only [he, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The flattened invalid-cell operator is the original one with identity reference/response. -/
theorem response_invalid_flat [DecidableEq X] [Fintype Y] [Nonempty Y] (c : Fin k × X) :
    (databaseInvalidCell (Y := Y) (Z := B × Z) c).submatrix
        responseDatabaseEquiv responseDatabaseEquiv =
      ((1 : Matrix B B ℂ) ⊗ₖ CompressedReplay.invalid c) ⊗ₖ (1 : Matrix Z Z ℂ) := by
  ext ⟨⟨b, D⟩, z⟩ ⟨⟨b', D'⟩, z'⟩
  have h := congrArg (fun M ↦ M (D, (b, z)) (D', (b', z')))
    (CompressedReplay.databaseInvalidCell_flat (Y := Y) (Z := B × Z) c)
  simp only [submatrix_apply, Equiv.prodCongr_apply, Equiv.curry_symm_apply,
    Equiv.refl_apply, Prod.map_apply, kroneckerMap_apply] at h
  change _ = _
  rw [show (databaseInvalidCell (Y := Y) (Z := B × Z) c).submatrix
      responseDatabaseEquiv responseDatabaseEquiv ((b, D), z) ((b', D'), z') =
        databaseInvalidCell c (Function.uncurry D, (b, z))
          (Function.uncurry D', (b', z')) from rfl, h]
  simp only [kroneckerMap_apply, one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The flattened population cutoff depends only on the original database family. -/
theorem response_population_flat (s : ℕ) :
    (populationCut (C := Fin k × X) (Y := Y) (Z := B × Z) s).submatrix
        responseDatabaseEquiv responseDatabaseEquiv =
      (diagonal (fun a : B × (Fin k → Database X Y) ↦
        if databasePopulation a.2 ≤ s then (1 : ℂ) else 0)) ⊗ₖ (1 : Matrix Z Z ℂ) := by
  rw [populationCut, submatrix_diagonal_equiv]
  rw [← diagonal_one, diagonal_kronecker_diagonal]
  congr 1
  funext a
  change (if Database.size (Function.uncurry a.1.2) ≤ s then (1 : ℂ) else 0) =
    (if databasePopulation a.1.2 ≤ s then 1 else 0) * 1
  rw [database_size_curry, mul_one]
  rfl

end Quantum

namespace Quantum
open MatrixMap

variable {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y] [Fintype Y]
  [Nonempty Y]

/-- The homogeneous component increment in the original database/reference/response order.
Only the original input is population-supported; no checker has acted on it. -/
theorem response_databaseControl_invalid_increment
    {k : ℕ} {B Z : Type*} [Fintype B] [DecidableEq B]
    [Fintype Z] [DecidableEq Z] [AddGroup Z]
    (β : (Fin k → Database X Y) → Z) (s : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hβ : ∀ D : Database (Fin k × X) Y, D.size ≤ s → ∀ c, (D c).isSome →
      changingFraction (fun D ↦ β (Function.curry D)) c (fun i ↦ D i.1) ≤ a)
    {ρ : Matrix ((B × (Fin k → Database X Y)) × Z) _ ℂ} (hρ : ρ.PosSemidef)
    (hpop : ((diagonal (fun a : B × (Fin k → Database X Y) ↦
      if databasePopulation a.2 ≤ s then (1 : ℂ) else 0)) ⊗ₖ (1 : Matrix Z Z ℂ)) * ρ = ρ) :
    let V := responseTranslation (fun a : B × (Fin k → Database X Y) ↦
      β a.2)
    let R := fun c : Fin k × X ↦
      ((1 : Matrix B B ℂ) ⊗ₖ CompressedReplay.invalid c) ⊗ₖ (1 : Matrix Z Z ℂ)
    (∑' c, ENNReal.ofReal (conj (R c) (conj V ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' c, ENNReal.ofReal (conj (R c) ρ).trace.re) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (4 * s * a) *
          ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
  let e := responseDatabaseEquiv (k := k) (X := X) (Y := Y) (B := B) (Z := Z)
  let σ := ρ.submatrix e.symm e.symm
  have hs : σ.submatrix e e = ρ := by
    ext a b
    simp [σ]
  have hp : populationCut s * σ = σ := by
    have hh : (populationCut s * σ).submatrix e e = σ.submatrix e e := by
      rw [← submatrix_mul_equiv _ _ e e e, hs, response_population_flat]
      exact hpop
    ext a b
    simpa only [submatrix_apply, Equiv.apply_symm_apply] using
      congrArg (fun M ↦ M (e.symm a) (e.symm b)) hh
  have hU (z : Z) : (1 : Matrix B B ℂ) ⊗ₖ xorShift Z z ∈ unitaryGroup (B × Z) ℂ := by
    rw [mem_unitaryGroup_iff']
    change ((1 : Matrix B B ℂ) ⊗ₖ xorShift Z z)ᴴ * (1 ⊗ₖ xorShift Z z) = 1
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff'.mp (xorShift_mem_unitaryGroup z),
      one_kronecker_one]
  have hh := databaseControl_invalid_increment_weighted
    (fun D ↦ β (Function.curry D))
    (fun z ↦ (1 : Matrix B B ℂ) ⊗ₖ xorShift Z z) hU s ha hβ (hρ.submatrix e.symm) hp
  let V := databaseControl
    (fun D ↦ β (Function.curry D))
    (fun z ↦ (1 : Matrix B B ℂ) ⊗ₖ xorShift Z z)
  have ht (K : Matrix (Database (Fin k × X) Y × (B × Z)) _ ℂ) :
      (conj K σ).trace = (conj (K.submatrix e e) ρ).trace := by
    rw [← trace_conj_submatrix_equiv e, hs]
  have ht₂ (K : Matrix (Database (Fin k × X) Y × (B × Z)) _ ℂ) :
      (conj K (conj V σ)).trace =
        (conj (K.submatrix e e) (conj (V.submatrix e e) ρ)).trace := by
    rw [← trace_conj_submatrix_equiv e, ← conj_submatrix_equiv, hs]
  have htr : σ.trace = ρ.trace := trace_submatrix_equiv e.symm ρ
  dsimp only at hh ⊢
  change (∑' c, ENNReal.ofReal (conj (databaseInvalidCell c) (conj V σ)).trace.re) ^
      (2⁻¹ : ℝ) ≤
    (∑' c, ENNReal.ofReal (conj (databaseInvalidCell c) σ).trace.re) ^ (2⁻¹ : ℝ) +
      (ENNReal.ofReal (4 * s * a) *
        ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) at hh
  rw [show (∑' c, ENNReal.ofReal (conj (databaseInvalidCell c) (conj V σ)).trace.re) =
      ∑' c, ENNReal.ofReal (conj ((databaseInvalidCell c).submatrix e e)
        (conj (V.submatrix e e) ρ)).trace.re from
      tsum_congr (fun c ↦ congrArg (fun t : ℂ ↦ ENNReal.ofReal t.re) (ht₂ _)),
    show (∑' c, ENNReal.ofReal (conj (databaseInvalidCell c) σ).trace.re) =
      ∑' c, ENNReal.ofReal (conj ((databaseInvalidCell c).submatrix e e) ρ).trace.re from
      tsum_congr (fun c ↦ congrArg (fun t : ℂ ↦ ENNReal.ofReal t.re) (ht _)), htr] at hh
  simpa only [V, e, response_invalid_flat, responseTranslation_flat] using hh

/-- The component increment after inserting a fixed response retains the original potential
and input trace, for any database-dependent response with the given changing-label bound. -/
theorem response_seed_invalid_increment [AddCommGroup Y]
    {k : ℕ} {B Z : Type*} [Fintype B] [DecidableEq B]
    [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
    (β : (Fin k → Database X Y) → Z) (z : Z) (s : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hβ : ∀ D : Database (Fin k × X) Y, D.size ≤ s → ∀ c, (D c).isSome →
      changingFraction (fun D ↦ β (Function.curry D)) c (fun i ↦ D i.1) ≤ a)
    {ρ : Matrix (B × (Fin k → Database X Y)) _ ℂ} (hρ : ρ.PosSemidef)
    (hpop : diagonal (fun a : B × (Fin k → Database X Y) ↦
      if databasePopulation a.2 ≤ s then (1 : ℂ) else 0) * ρ = ρ) :
    let J := responseInclusion (A := B × (Fin k → Database X Y)) z
    let V := responseTranslation (fun a : B × (Fin k → Database X Y) ↦ β a.2)
    (∑' x : Fin k × X, ENNReal.ofReal (conj
      (((1 : Matrix B B ℂ) ⊗ₖ CompressedReplay.invalid x) ⊗ₖ (1 : Matrix Z Z ℂ))
        (conj V (conj J ρ))).trace.re) ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.potential (CompressedReplay.invalidStack (k := k) (X := X) (Y := Y)) ρ) ^
          (2⁻¹ : ℝ) +
        (ENNReal.ofReal (4 * s * a) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
  let J := responseInclusion (A := B × (Fin k → Database X Y)) z
  let σ := conj J ρ
  have hσ : σ.PosSemidef := (isCP_conj J).posSemidef hρ
  have ht : σ.trace = ρ.trace := isTP_conj
    (conjTranspose_basisMatrix_mul_self (fun _ _ h ↦ congrArg Prod.fst h)) ρ
  have hf := response_databaseControl_invalid_increment β s ha hβ hσ
    (supported_response_inclusion z _ ρ hpop)
  have hi (x : Fin k × X) : (conj
      (((1 : Matrix B B ℂ) ⊗ₖ CompressedReplay.invalid x) ⊗ₖ (1 : Matrix Z Z ℂ))
        σ).trace = (conj ((1 : Matrix B B ℂ) ⊗ₖ CompressedReplay.invalid x) ρ).trace :=
    trace_conj_response_inclusion z _ ρ
  dsimp only at hf ⊢
  simp_rw [hi, ht] at hf
  rw [← CompressedReplay.invalidStack_potential_eq hρ] at hf
  exact hf

end Quantum

namespace Quantum.SaltedMerkle
open MatrixMap

variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Nonempty Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]

/-- The homogeneous component increment in the original database/reference/response order.
Only the original input is population-supported; no checker has acted on it. -/
theorem response_extraction_invalid_increment
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (tic : TpIC k Y) {B Z : Type*} [Fintype B] [DecidableEq B]
    [Fintype Z] [DecidableEq Z] [AddGroup Z]
    (f : TpDLen k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))) tic.1 → Z) (s : ℕ)
    {ρ : Matrix ((B × (Fin k → Database X Y)) × Z) _ ℂ} (hρ : ρ.PosSemidef)
    (hpop : ((diagonal (fun a : B × (Fin k → Database X Y) ↦
      if databasePopulation a.2 ≤ s then (1 : ℂ) else 0)) ⊗ₖ (1 : Matrix Z Z ℂ)) * ρ = ρ) :
    let V := responseTranslation (fun a : B × (Fin k → Database X Y) ↦
      f ((_root_.SaltedMerkle.multiExtract enc d).extract tic a.2))
    let R := fun c : Fin k × X ↦
      ((1 : Matrix B B ℂ) ⊗ₖ CompressedReplay.invalid c) ⊗ₖ (1 : Matrix Z Z ℂ)
    (∑' c, ENNReal.ofReal (conj (R c) (conj V ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' c, ENNReal.ofReal (conj (R c) ρ).trace.re) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (4 * s * oldChangingFraction (Fintype.card Y) s) *
          ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
  classical
  have hβ := fun D hD c hc ↦ extraction_changingFraction_le enc d tic f D s hD c hc
  exact response_databaseControl_invalid_increment (k := k) (X := X) (Y := Y)
    (B := B) (Z := Z) (fun D ↦ f ((_root_.SaltedMerkle.multiExtract enc d).extract tic D))
    s (a := oldChangingFraction (Fintype.card Y) s)
    (le_min (by norm_num) (by positivity)) hβ hρ hpop

/-- A selected response component has the original-state invalid-norm bound after adjoining
zero response. Both the reference and the input trace are preserved. -/
theorem partResponse_zero_invalid_increment [AddCommGroup Y]
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (tic : TpIC k Y) (I : Finset (Fin k)) (B : QReg) (s : ℕ)
    {ρ : Matrix (B × (Fin k → Database X Y)) _ ℂ} (hρ : ρ.PosSemidef)
    (hpop : diagonal (fun a : B × (Fin k → Database X Y) ↦
      if databasePopulation a.2 ≤ s then (1 : ℂ) else 0) * ρ = ρ) :
    let Z := TpDCode.ConcatReg k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i)))
    let J := responseInclusion (A := B × (Fin k → Database X Y)) (0 : Z)
    let V := responseTranslation (fun a : B × (Fin k → Database X Y) ↦
      TpDCode.partResponse (_root_.SaltedMerkle.multiExtract enc d) I tic a.2)
    (∑' x : Fin k × X, ENNReal.ofReal (conj
      (((1 : Matrix B B ℂ) ⊗ₖ CompressedReplay.invalid x) ⊗ₖ (1 : Matrix Z Z ℂ))
        (conj V (conj J ρ))).trace.re) ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.potential (CompressedReplay.invalidStack (k := k) (X := X) (Y := Y)) ρ) ^
          (2⁻¹ : ℝ) +
        (ENNReal.ofReal (4 * s * oldChangingFraction (Fintype.card Y) s) *
          ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
  classical
  let Dm := DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))
  let Z := TpDCode.ConcatReg k Dm
  let : DecidableEq Z := inferInstanceAs (DecidableEq (TpDCode.ConcatReg k Dm))
  let : Fintype Z := inferInstanceAs (Fintype (TpDCode.ConcatReg k Dm))
  let : AddCommGroup Z := inferInstanceAs (AddCommGroup (TpDCode.ConcatReg k Dm))
  let f : TpDLen k Dm tic.1 → Z := fun tdm ↦
    (0, fun i ↦ if i ∈ I then TpDCode.concatPayload tic.1 tdm i else 0)
  refine response_seed_invalid_increment (X := X) (Y := Y) (k := k) (B := B) (Z := Z)
    (fun D ↦ TpDCode.partResponse (_root_.SaltedMerkle.multiExtract enc d) I tic D)
    (0 : Z) s (a := oldChangingFraction (Fintype.card Y) s)
    (le_min (by norm_num) (by positivity)) ?_ hρ hpop
  intro D hD c hc
  exact extraction_changingFraction_le enc d tic f D s hD c hc

end Quantum.SaltedMerkle
