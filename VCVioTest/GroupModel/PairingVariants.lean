/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.PairingSeparation
public import Mathlib.Algebra.Field.ZMod

/-! # Numerical Type 1 and Type 2 DDH separations

Multiplication over `ZMod 101`, with generator one and identity source map,
gives DDH distinguishing advantage at least `100/101` in both signatures.
-/

public section

open OracleComp OracleSpec DiffieHellman
open scoped ENNReal

namespace GroupModel

private theorem sub_one_div_101 : (1 : ℝ≥0∞) - 1 / 101 = 100 / 101 := by
  apply ENNReal.sub_eq_of_eq_add' (by norm_num)
  rw [← ENNReal.add_div]
  norm_num
  rw [ENNReal.div_self (by norm_num) (by norm_num)]

/-- The symmetric multiplication pairing over `ZMod 101` breaks DDH with advantage
at least `100/101`, through an ordinary public import of the separation theorem. -/
theorem symmDDHAttack_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    letI : ∀ s, DecidableEq (SFam (ZMod 101) (ZMod 101) s) :=
      fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
    (100 / 101 : ℝ≥0∞) ≤ ddhAdvantage (1 : ZMod 101)
      (symmDDH.ofGeneric (LinearMap.mul (ZMod 101) (ZMod 101)) (symmDDHAttack (ZMod 101))) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let : ∀ s, DecidableEq (SFam (ZMod 101) (ZMod 101) s) :=
    fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
  have h := ddhAdvantage_symmDDHAttack_ge (LinearMap.mul (ZMod 101) (ZMod 101)) 1
    (by simpa only [smul_eq_mul, mul_one, id_eq] using! Function.bijective_id)
    (by simp)
  simpa only [ZMod.card, Nat.cast_ofNat, sub_one_div_101] using! h

/-- The identity source map and multiplication pairing over `ZMod 101` break
second-source DDH with advantage at least `100/101`. -/
theorem isoDDHAttack_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    letI : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
      fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
    (100 / 101 : ℝ≥0∞) ≤ ddhAdvantage (1 : ZMod 101)
      (isoDDH.ofGeneric (LinearMap.id : ZMod 101 →ₗ[ZMod 101] ZMod 101)
        (LinearMap.mul (ZMod 101) (ZMod 101)) (isoDDHAttack (ZMod 101))) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
    fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
  have h := ddhAdvantage_isoDDHAttack_ge (LinearMap.id : ZMod 101 →ₗ[ZMod 101] ZMod 101)
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1
    (by simpa only [smul_eq_mul, mul_one, id_eq] using! Function.bijective_id)
    (by simp)
  simpa only [ZMod.card, Nat.cast_ofNat, sub_one_div_101] using! h

end GroupModel
