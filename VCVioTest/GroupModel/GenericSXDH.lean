/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericSXDH
public import Mathlib.Algebra.Field.ZMod

/-! # A numerical generic XDH₂ bound

Over the field with 101 elements, a generic adversary pairs the challenge and the
first random share with the first generator, then compares the two target handles.
The per-sort theorem gives the explicit advantage bound `39/101`.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace GroupModel

/-- The second-source real experiment is definitionally DDH with the first generator
passed to the adversary. -/
theorem xdh₂_realExperiment_eq_ddhRealExperiment {F G₁ G₂ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₂] [Module F G₂]
    (g₂ : G₂) (g₁ : G₁) (A : XDH₂.Adversary F G₁ G₂) :
    XDH₂.realExperiment g₂ g₁ A =
      DiffieHellman.ddhRealExperiment (F := F) g₂ (fun g X Y T => A g X Y T g₁) := rfl

/-- The second-source random experiment is definitionally DDH with the first generator
passed to the adversary. -/
theorem xdh₂_randomExperiment_eq_ddhRandomExperiment {F G₁ G₂ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₂] [Module F G₂]
    (g₂ : G₂) (g₁ : G₁) (A : XDH₂.Adversary F G₁ G₂) :
    XDH₂.randomExperiment g₂ g₁ A =
      DiffieHellman.ddhRandomExperiment (F := F) g₂ (fun g X Y T => A g X Y T g₁) := rfl

/-- Two public pairing calls and one target equality query give the generic XDH₂ bound
`39/101` over `ZMod 101`, with multiplication as the bilinear map. -/
theorem xdh₂_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    letI : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
      fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
    let A : OracleComp (genSpec (ZMod 101) pairingSig) Bool := do
      let t ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 0 3))
      let a ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 0 1))
      (genSpec (ZMod 101) pairingSig).query (.inl (.eq .gₜ t a))
    XDH₂.advantage (1 : ZMod 101) 1
      (XDH₂.Adversary.ofGeneric (LinearMap.mul (ZMod 101) (ZMod 101)) A) ≤
        (39 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
    fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
  dsimp only
  apply (XDH₂.advantage_ofGeneric_le
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1 one_ne_zero one_ne_zero
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : ZMod 101) ≠ 0))
    _ 0 0 2 ?_ ?_ ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => ⟨by decide, fun _ =>
      ⟨(by left; intro h; cases h), fun _ => trivial⟩⟩⟩
  · exact ⟨by decide, fun _ => ⟨by decide, fun _ =>
      ⟨(by left; intro h; cases h), fun _ => trivial⟩⟩⟩
  · exact ⟨by decide, fun _ => ⟨by decide, fun _ =>
      ⟨(by left; intro h; cases h), fun _ => trivial⟩⟩⟩

end GroupModel
