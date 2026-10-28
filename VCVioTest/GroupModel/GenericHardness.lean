/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericHardness
public import Mathlib.Algebra.Field.ZMod

/-!
Concrete generic adversaries over the field with five elements

The discrete-logarithm adversary uses free comparisons with the generator and the zero default.
The computational Diffie–Hellman adversary adds the two input challenges.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace GroupModel

/-- Comparing the challenge with the generator and zero costs no group operations; the
resulting discrete-logarithm adversary has success probability at most `4/5`. -/
theorem dlog_generic_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let A : OracleComp (genSpec (ZMod 5) groupSig) (ZMod 5) := do
      let one : Bool ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () 1 0))
      let zero : Bool ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () 1 2))
      pure (if one = true then 1 else if zero = true then 0 else 2)
    Pr{let b ← DiffieHellman.dlogExperiment (1 : ZMod 5) (DLogAdversary.ofGeneric A)}[b = true] ≤
      (4 / 5 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  dsimp only
  apply (dlogExperiment_ofGeneric_le (1 : ZMod 5) one_ne_zero _ 0 ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => ⟨by decide, fun _ => trivial⟩⟩

/-- Adding the two challenges costs one group operation; the generic CDH bound evaluates to
`12/5` over the field with five elements. -/
theorem cdh_generic_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let A : OracleComp (genSpec (ZMod 5) groupSig) Handle :=
      (genSpec (ZMod 5) groupSig).query (.inl (.add () 1 2))
    Pr{let b ← DiffieHellman.cdhExperiment (1 : ZMod 5) (CDHAdversary.ofGeneric A)}[b = true] ≤
      (12 / 5 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  dsimp only
  apply (cdhExperiment_ofGeneric_le (1 : ZMod 5) one_ne_zero _ 1 ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => trivial⟩

end GroupModel
