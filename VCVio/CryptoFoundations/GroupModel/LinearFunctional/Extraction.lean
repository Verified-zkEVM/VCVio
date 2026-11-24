/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Affine
public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Module.Torsion.Field


/-! # Scalar extraction from an affine forgery

When the signature is an affine representation `repr.eval α • g₁` and the generators pair to a
nonzero value, the BLS verification equation is the scalar equation `repr.eval α = c * α`
(`eval_eq_of_pairing_eq`).
-/

public section

namespace GroupModel.LinearFunctional

/-- Nonzero pairing of the generators turns affine verification into a scalar equation. -/
theorem eval_eq_of_pairing_eq {F G₁ G₂ Gₜ : Type*} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (he : e g₁ g₂ ≠ 0) {α c : F} {σ : G₁} {repr : AffineForm F}
    (hsound : σ = repr.eval α • g₁)
    (hverify : e σ g₂ = e (c • g₁) (α • g₂)) : repr.eval α = c * α := by
  apply smul_left_injective F he
  simpa only [hsound, LinearMap.map_smul, LinearMap.smul_apply, smul_smul] using hverify

end GroupModel.LinearFunctional
