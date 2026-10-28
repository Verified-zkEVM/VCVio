/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.MasterBound
import Mathlib.Algebra.Module.Torsion.Free

/-! # Type 1 and Type 2 pairing models

The symbolic models are `symbolic F symmPairingSig ι` and `symbolic F pairingIsoSig ι`.
Their evaluation morphisms transport generic runs by `runGen_map`.
-/

public section

namespace GroupModel

variable {F G G₁ G₂ Gₜ ι : Type}

/-- The source and target carriers of a symmetric pairing. -/
@[expose] def SFam (G Gₜ : Type) : Bool → Type
  | false => G
  | true => Gₜ

/-- The symmetric pairing family inherits addition in each carrier. -/
instance [AddCommMonoid G] [AddCommMonoid Gₜ] : ∀ s, AddCommMonoid (SFam G Gₜ s)
  | false => inferInstanceAs (AddCommMonoid G)
  | true => inferInstanceAs (AddCommMonoid Gₜ)

/-- The symmetric pairing family inherits scalar multiplication in each carrier. -/
instance [CommSemiring F] [AddCommMonoid G] [AddCommMonoid Gₜ]
    [Module F G] [Module F Gₜ] : ∀ s, Module F (SFam G Gₜ s)
  | false => inferInstanceAs (Module F G)
  | true => inferInstanceAs (Module F Gₜ)

/-- A Type 2 model interprets the public source map and the pairing. -/
@[expose] def pairingIsoReal [CommSemiring F] [AddCommMonoid G₁] [AddCommMonoid G₂]
    [AddCommMonoid Gₜ] [Module F G₁] [Module F G₂] [Module F Gₜ]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) :
    Model F pairingIsoSig (PFam G₁ G₂ Gₜ) where
  lin _ := ψ
  bil _ := e

/-- The linear structure map is the supplied source map. -/
@[simp] theorem pairingIsoReal_lin_apply [CommSemiring F] [AddCommMonoid G₁] [AddCommMonoid G₂]
    [AddCommMonoid Gₜ] [Module F G₁] [Module F G₂] [Module F Gₜ]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (o : Unit) (v : G₂) :
    (pairingIsoReal ψ e).lin o v = ψ v := by rfl

/-- The bilinear structure map is the supplied pairing. -/
@[simp] theorem pairingIsoReal_bil_apply [CommSemiring F] [AddCommMonoid G₁] [AddCommMonoid G₂]
    [AddCommMonoid Gₜ] [Module F G₁] [Module F G₂] [Module F Gₜ]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (o : Unit) (v : G₁) (w : G₂) :
    (pairingIsoReal ψ e).bil o v w = e v w := by rfl

/-- A Type 1 model pairs its source carrier with itself. -/
@[expose] def symmPairingReal [CommSemiring F] [AddCommMonoid G] [AddCommMonoid Gₜ]
    [Module F G] [Module F Gₜ]
    (e : G →ₗ[F] G →ₗ[F] Gₜ) : Model F symmPairingSig (SFam G Gₜ) where
  lin o := o.elim
  bil _ := e

/-- The symmetric model's bilinear structure map is the supplied pairing. -/
@[simp] theorem symmPairingReal_bil_apply [CommSemiring F] [AddCommMonoid G] [AddCommMonoid Gₜ]
    [Module F G] [Module F Gₜ]
    (e : G →ₗ[F] G →ₗ[F] Gₜ) (o : Unit) (v w : G) :
    (symmPairingReal e).bil o v w = e v w := by rfl

/-- Polynomial evaluation is a Type 2 morphism when the source map preserves generators. -/
noncomputable def evalHom.pairingIso [Field F] [AddCommGroup G₁] [AddCommGroup G₂]
    [AddCommGroup Gₜ] [Module F G₁] [Module F G₂] [Module F Gₜ]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (x : ι → F) (hψ : ψ g₂ = g₁) :
    (symbolic F pairingIsoSig ι).Hom (pairingIsoReal ψ e) where
  toFun
    | .g₁ => (evalAt g₁ x : MvPolynomial ι F →ₗ[F] G₁)
    | .g₂ => (evalAt g₂ x : MvPolynomial ι F →ₗ[F] G₂)
    | .gₜ => (evalAt (e g₁ g₂) x : MvPolynomial ι F →ₗ[F] Gₜ)
  map_lin _ P := by
    simp only [symbolic_lin_apply]
    change evalAt g₁ x P = ψ (evalAt g₂ x P)
    simp only [evalAt_apply, map_smul, hψ]
  map_bil _ P Q := by
    simp only [symbolic_bil_apply]
    change evalAt (e g₁ g₂) x (P * Q) = e (evalAt g₁ x P) (evalAt g₂ x Q)
    simp only [evalAt_apply, map_mul, mul_smul, map_smul, LinearMap.smul_apply]
    rw [smul_comm]

/-- Evaluation at sort `g₁` scales its chosen generator. -/
@[simp] theorem evalHom.pairingIso_apply_g₁ [Field F] [AddCommGroup G₁] [AddCommGroup G₂]
    [AddCommGroup Gₜ] [Module F G₁] [Module F G₂] [Module F Gₜ]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (x : ι → F) (hψ : ψ g₂ = g₁) (P : MvPolynomial ι F) :
    (evalHom.pairingIso ψ e g₁ g₂ x hψ).toFun .g₁ P = evalAt g₁ x P := by rfl

/-- Evaluation at sort `g₂` scales its chosen generator. -/
@[simp] theorem evalHom.pairingIso_apply_g₂ [Field F] [AddCommGroup G₁] [AddCommGroup G₂]
    [AddCommGroup Gₜ] [Module F G₁] [Module F G₂] [Module F Gₜ]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (x : ι → F) (hψ : ψ g₂ = g₁) (P : MvPolynomial ι F) :
    (evalHom.pairingIso ψ e g₁ g₂ x hψ).toFun .g₂ P = evalAt g₂ x P := by rfl

/-- Evaluation at sort `gₜ` scales its chosen generator. -/
@[simp] theorem evalHom.pairingIso_apply_gₜ [Field F] [AddCommGroup G₁] [AddCommGroup G₂]
    [AddCommGroup Gₜ] [Module F G₁] [Module F G₂] [Module F Gₜ]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (x : ι → F) (hψ : ψ g₂ = g₁) (P : MvPolynomial ι F) :
    (evalHom.pairingIso ψ e g₁ g₂ x hψ).toFun .gₜ P = evalAt (e g₁ g₂) x P := by rfl

/-- Polynomial evaluation is a Type 1 morphism with target generator `e g g`. -/
noncomputable def evalHom.symmPairing [Field F] [AddCommGroup G] [AddCommGroup Gₜ]
    [Module F G] [Module F Gₜ]
    (e : G →ₗ[F] G →ₗ[F] Gₜ) (g : G) (x : ι → F) :
    (symbolic F symmPairingSig ι).Hom (symmPairingReal e) where
  toFun
    | false => (evalAt g x : MvPolynomial ι F →ₗ[F] G)
    | true => (evalAt (e g g) x : MvPolynomial ι F →ₗ[F] Gₜ)
  map_lin o := o.elim
  map_bil _ P Q := by
    simp only [symbolic_bil_apply]
    change evalAt (e g g) x (P * Q) = e (evalAt g x P) (evalAt g x Q)
    simp only [evalAt_apply, map_mul, mul_smul, map_smul, LinearMap.smul_apply]
    rw [smul_comm]

/-- Evaluation at sort `false` scales its chosen generator. -/
@[simp] theorem evalHom.symmPairing_apply_false [Field F] [AddCommGroup G] [AddCommGroup Gₜ]
    [Module F G] [Module F Gₜ]
    (e : G →ₗ[F] G →ₗ[F] Gₜ) (g : G) (x : ι → F) (P : MvPolynomial ι F) :
    (evalHom.symmPairing e g x).toFun false P = evalAt g x P := by rfl

/-- Evaluation at sort `true` scales its chosen generator. -/
@[simp] theorem evalHom.symmPairing_apply_true [Field F] [AddCommGroup G] [AddCommGroup Gₜ]
    [Module F G] [Module F Gₜ]
    (e : G →ₗ[F] G →ₗ[F] Gₜ) (g : G) (x : ι → F) (P : MvPolynomial ι F) :
    (evalHom.symmPairing e g x).toFun true P = evalAt (e g g) x P := by rfl

/-- The least closed Type 2 bounds extend the first source by the second source bound,
then extend the target by the sum of the closed source bounds. -/
theorem degreeClosed_pairingIsoSig (d₁ d₂ dₜ : ℕ) :
    pairingIsoSig.DegreeClosed
      (fun | .g₁ => max d₁ d₂ | .g₂ => d₂ | .gₜ => max dₜ (max d₁ d₂ + d₂)) :=
  ⟨fun _ => Nat.le_max_right _ _, fun _ => Nat.le_max_right _ _⟩

/-- The least closed Type 1 target bound extends the initial bound by twice the source bound. -/
theorem degreeClosed_symmPairingSig (d dₜ : ℕ) :
    symmPairingSig.DegreeClosed (fun | false => d | true => max dₜ (2 * d)) := by
  refine ⟨fun o => o.elim, fun _ => ?_⟩
  exact (by omega : d + d ≤ max dₜ (2 * d))

open OracleComp

/-- Evaluating symbolic tables commutes with a Type 2 run when the source map preserves
the chosen generators and both generators and their pairing are nonzero. -/
theorem runGen_pairingIso_mapTbl_evalHom {α : Type} [Field F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hψ : ψ g₂ = g₁) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0) (x : ι → F)
    (A : OracleComp (genSpec F pairingIsoSig) α)
    (tbl : Tbl (fun _ : PSort => MvPolynomial ι F)) :
    runGen (pairingIsoReal ψ e) (fun _ => id) A
        (mapTbl (fun s => (evalHom.pairingIso ψ e g₁ g₂ x hψ).toFun s) tbl) =
      Prod.map id (mapTbl (fun s => (evalHom.pairingIso ψ e g₁ g₂ x hψ).toFun s)) <$>
        runGen (symbolic F pairingIsoSig ι) (fun _ p => MvPolynomial.eval x p) A tbl := by
  have h := runGen_map (evalHom.pairingIso ψ e g₁ g₂ x hψ) (fun _ => id) A tbl
  simp only [Function.comp_def, id_eq] at h
  rw [← h]
  congr 1
  unfold runGen run
  rw [impl_congr (symbolic F pairingIsoSig ι)
    (fun s p => (evalHom.pairingIso ψ e g₁ g₂ x hψ).toFun s p)
    (fun _ p => MvPolynomial.eval x p) (by
      intro s p r
      cases s
      · change (evalAt g₁ x p = evalAt g₁ x r) ↔ _
        simp only [evalAt_apply]
        exact (smul_left_injective F hg₁).eq_iff
      · change (evalAt g₂ x p = evalAt g₂ x r) ↔ _
        simp only [evalAt_apply]
        exact (smul_left_injective F hg₂).eq_iff
      · change (evalAt (e g₁ g₂) x p = evalAt (e g₁ g₂) x r) ↔ _
        simp only [evalAt_apply]
        exact (smul_left_injective F he).eq_iff) ProbComp]

end GroupModel
