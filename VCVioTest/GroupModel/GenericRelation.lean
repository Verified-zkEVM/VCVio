/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericRelation
public import Mathlib.Algebra.Field.ZMod

/-!
 # Generic discrete-log relation regression test

A free equality query compares the two challenge handles. It returns `![1, -1]` on equality
and the zero vector otherwise, using no group operations.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace GroupModel

/-- Comparing two given elements over `ZMod 101` has relation success probability at most
`4 / 101` by the master bound with two initial table entries and no group operations. -/
theorem relation_generic_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    let A : OracleComp (genSpec (ZMod 101) groupSig) (Fin 2 → ZMod 101) := do
      let eq : Bool ← (genSpec (ZMod 101) groupSig).query (.inl (.eq () 0 1))
      pure (if eq then ![1, -1] else 0)
    Pr{let b ← (_root_.DiscreteLogRelation.plainExperiment (1 : ZMod 101)
      (DiscreteLogRelation.Adversary.ofGeneric A))}[b = true] ≤ (4 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  dsimp only
  apply (experiment_ofGeneric_le (1 : ZMod 101) one_ne_zero _ 0 ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => trivial⟩

end GroupModel
