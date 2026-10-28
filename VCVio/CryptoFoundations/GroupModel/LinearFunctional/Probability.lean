/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Affine
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.ProbabilityBounds

/-! # Extraction and independent affine collision bounds

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). The extraction split applies to adaptive
representations. The collision bound requires a fresh scalar independent of the coefficients.
-/

public section

open OracleComp

namespace GroupModel.LinearFunctional

/-- Successful affine verification either extracts the secret or has zero denominator. -/
theorem prEvent_success_le_extract_add_degenerate {F γ : Type} [Field F]
    (oa : ProbComp γ) (success : γ → Prop) (repr : γ → AffineForm F)
    (target secret : γ → F)
    (hsound : ∀ z ∈ support oa, success z →
      (repr z).eval (secret z) = target z * secret z) :
    Pr{let z ← oa}[success z] ≤
      Pr{let z ← oa}[(repr z).const / (target z - (repr z).lin) = secret z] +
      Pr{let z ← oa}[success z ∧ (repr z).lin = target z] := by
  refine (prEvent_mono_of_support oa _ _ ?_).trans (prEvent_or_le oa _ _)
  intro z hz hsucc
  by_cases hlin : (repr z).lin = target z
  · exact Or.inr ⟨hsucc, hlin⟩
  · exact Or.inl (AffineForm.extract_secret (hsound z hz hsucc) hlin).symm

/-- A fresh uniform scalar satisfies a nonconstant affine equation with probability at most
one over the field size, even when the coefficients depend on an earlier computation. -/
theorem prEvent_affine_uniform_le {F γ : Type} [Field F] [Fintype F] [SampleableType F]
    (oa : ProbComp γ) (a b t : γ → F) (ha : ∀ z ∈ support oa, a z ≠ 0) :
    Pr{let z ← oa; let ρ ← $ᵗ F}[a z * ρ + b z = t z] ≤ 1 / Fintype.card F := by
  have h := prEvent_bind_le_of_forall_le_of_support oa
    (fun z => (fun ρ : F => a z * ρ + b z = t z) <$> ($ᵗ F)) id
    (ε := 1 / Fintype.card F) (fun z hz => by
      simp only [prEvent_norm, id_eq]
      have hi : Function.Injective (fun ρ : F => a z * ρ + b z) := by
        intro x y h
        exact mul_left_cancel₀ (ha z hz) (add_right_cancel h)
      simpa only [Nat.card_eq_fintype_card, one_div] using
        SampleableType.prEvent_uniformSample_apply_eq_le hi (t z))
  simpa only [prEvent_norm, id_eq] using h

end GroupModel.LinearFunctional
