/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericDDH
public import Mathlib.Algebra.Field.ZMod

/-! # A generic DDH comparison over the field with five elements

The adversary adds the two challenge handles and compares their sum with the target.
This uses one group operation and one free equality query.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace GroupModel

/-- Comparing the target with the sum of the challenges uses one group operation;
the generic DDH bound at `q = 1` over the field with five elements evaluates to `9`. -/
theorem ddh_generic_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let A : OracleComp (genSpec (ZMod 5) groupSig) Bool := do
      let sum ← (genSpec (ZMod 5) groupSig).query (.inl (.add () 1 2))
      (genSpec (ZMod 5) groupSig).query (.inl (.eq () 3 sum))
    DiffieHellman.ddhAdvantage (1 : ZMod 5) (DDHAdversary.ofGeneric A) ≤ (9 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  dsimp only
  apply (ddhAdvantage_ofGeneric_le (1 : ZMod 5) one_ne_zero _ 1 ?_).trans
  · norm_num [ZMod.card, Nat.choose]
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
    norm_num
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩

end GroupModel
