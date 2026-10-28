/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.MasterBound

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

/-- Closed Type 2 source bounds require `d₂ ≤ d₁`; the least target extension is their sum. -/
theorem degreeClosed_pairingIsoSig (d₁ d₂ dₜ : ℕ) (h : d₂ ≤ d₁) :
    pairingIsoSig.DegreeClosed (fun | .g₁ => d₁ | .g₂ => d₂ | .gₜ => max dₜ (d₁ + d₂)) :=
  ⟨fun _ => h, fun _ => Nat.le_max_right _ _⟩

/-- The least closed Type 1 target bound extends the initial bound by twice the source bound. -/
theorem degreeClosed_symmPairingSig (d dₜ : ℕ) :
    symmPairingSig.DegreeClosed (fun | false => d | true => max dₜ (2 * d)) := by
  refine ⟨fun o => o.elim, fun _ => ?_⟩
  exact (by omega : d + d ≤ max dₜ (2 * d))

end GroupModel
