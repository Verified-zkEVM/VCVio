/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericXDH
public import Mathlib.Algebra.Field.ZMod

/-! # A numerical generic XDH bound

Over the field with 101 elements, a generic adversary pairs the challenge and the
first random share with the second generator, then compares the two target handles.
The per-sort theorem gives the explicit advantage bound `39/101`.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace GroupModel

/-- Two public pairing calls and one target equality query give the generic XDH bound
`39/101` over `ZMod 101`, with multiplication as the bilinear map. -/
theorem xdh_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    letI : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
      fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
    let A : OracleComp (genSpec (ZMod 101) pairingSig) Bool := do
      let t ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 3 0))
      let a ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 1 0))
      (genSpec (ZMod 101) pairingSig).query (.inl (.eq .gₜ t a))
    XDH.advantage (1 : ZMod 101) 1
      (XDH.Adversary.ofGeneric (LinearMap.mul (ZMod 101) (ZMod 101)) A) ≤
        (39 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
    fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
  dsimp only
  apply (XDH.advantage_ofGeneric_le
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
