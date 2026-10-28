/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Affine
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Weights
public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Module.Torsion.Field

import Mathlib.Tactic.Ring

/-! # Linear-functional forgery representations

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). A separate coefficient records a public challenge
point in the signature group. Signing occurrences have an arbitrary finite index type;
no global query bound or padding of the signing transcript is required.
-/

public section

namespace GroupModel.LinearFunctional

/-- A weighted forgery over public bases and exactly the supplied signing occurrences. -/
structure Forgery (F M ι Q : Type*) where
  /-- The forged message. -/
  message : M
  /-- The actual signed message at each occurrence. -/
  signed : Q → M
  /-- Coefficient of the generator. -/
  constant : F
  /-- Coefficient of the public challenge point in the signature group. -/
  keyCoeff : F
  /-- Coefficients of the public bases. -/
  hashes : ι → F
  /-- Coefficients of the signing replies. -/
  signatures : Q → F

/-- Evaluate a forgery's representation on its concrete inputs. -/
@[expose] def Forgery.element {F M ι Q G : Type*} [Semiring F] [Fintype ι] [Fintype Q]
    [AddCommMonoid G] [Module F G] (fo : Forgery F M ι Q)
    (g X : G) (H : ι → G) (sign : M → G) : G :=
  fo.constant • g + fo.keyCoeff • X +
    (∑ i, fo.hashes i • H i) + ∑ q, fo.signatures q • sign (fo.signed q)

/-- The affine exponent of a forgery under scalar programming. -/
@[expose] def Forgery.representation {F M ι Q : Type*} [Semiring F] [Fintype ι] [Fintype Q]
    (fo : Forgery F M ι Q) (w : ι → M → F) (ρ : ι → F) : AffineForm F :=
  ⟨fo.constant + ∑ i, fo.hashes i * ρ i,
    fo.keyCoeff + ∑ q, fo.signatures q * targetScalar w ρ (fo.signed q)⟩

/-- Scalar programming realizes the represented element at the signing secret. -/
theorem Forgery.element_eq_eval_smul {F M ι Q G : Type*} [CommSemiring F]
    [Fintype ι] [Fintype Q] [AddCommMonoid G] [Module F G]
    (fo : Forgery F M ι Q) (w : ι → M → F) (g : G) (α : F) (ρ : ι → F) :
    fo.element g (α • g) (fun i => ρ i • g) (simSign w (α • g) ρ) =
      (fo.representation w ρ).eval α • g := by
  simp only [Forgery.element, simSign, Forgery.representation, AffineForm.eval,
    smul_smul, ← Finset.sum_smul, ← add_smul]
  congr 1
  simp only [add_mul, Finset.sum_mul, mul_assoc]
  ring

/-- The verification denominator is a linear functional minus the public-key coefficient. -/
theorem Forgery.targetScalar_sub_lin {F M ι Q : Type*} [CommRing F]
    [Fintype ι] [Fintype Q] (fo : Forgery F M ι Q) (w : ι → M → F) (ρ : ι → F) :
    targetScalar w ρ fo.message - (fo.representation w ρ).lin =
      (∑ i, gapCoeff w fo.message fo.signed fo.signatures i * ρ i) - fo.keyCoeff := by
  rw [← targetScalar_sub_sum]
  simp only [Forgery.representation]
  ring

/-- Nonzero pairing of the generators turns affine verification into a scalar equation. -/
theorem pairing_eq_implies_eval_eq {F G₁ G₂ Gₜ : Type*} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (he : e g₁ g₂ ≠ 0) {α c : F} {σ : G₁} {repr : AffineForm F}
    (hsound : σ = repr.eval α • g₁)
    (hverify : e σ g₂ = e (c • g₁) (α • g₂)) : repr.eval α = c * α := by
  apply smul_left_injective F he
  simpa only [hsound, LinearMap.map_smul, LinearMap.smul_apply, smul_smul] using hverify

end GroupModel.LinearFunctional
