/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Virtualize
public import VCVio.CryptoFoundations.GroupModel.Instances
public import Mathlib.Data.ZMod.Basic

/-! # Virtualization regression over five elements

A private zero entry follows the two adversary inputs in the outer table. The adversary adds
its two inputs and compares the result with an out-of-range handle.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

/-- Virtualization reads back the direct run on `[1, 3]` and transports its one-operation budget,
even when the adversary compares with handle `7`. -/
theorem virtualize_zmod5 :
    let M : Model (ZMod 5) groupSig (fun _ => ZMod 5) := Model.group (ZMod 5)
    let A : OracleComp (genSpec (ZMod 5) groupSig) Bool := do
      let h ← (genSpec (ZMod 5) groupSig).query (.inl (.add () 0 1))
      let b ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () h 7))
      pure b
    let z : Unit → Handle := fun _ => 2
    let τ : Tbl (fun _ : Unit => Handle) := fun _ => [0, 1]
    let T : Tbl (fun _ : Unit => ZMod 5) := fun _ => [1, 3, 0]
    (fun r => (r.1.1, readBack r.1.2 r.2)) <$>
        runGen M (fun _ => id) ((virtualize z A).run τ) T =
      runGen M (fun _ => id) A (fun _ => [1, 3]) ∧
    IsQueryBoundP A (fun i => isGroupOp i = true) 1 ∧
    IsQueryBoundP ((virtualize z A).run τ) (fun i => isGroupOp i = true) 1 := by
  dsimp only
  let A : OracleComp (genSpec (ZMod 5) groupSig) Bool := do
    let h ← (genSpec (ZMod 5) groupSig).query (.inl (.add () 0 1))
    let b ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () h 7))
    pure b
  have hw : WellFormed (fun _ : Unit => 2) (fun _ => [0, 1])
      (fun _ => ([1, 3, 0] : List (ZMod 5))) := by
    intro s
    simp [lookup]
  have hb : IsQueryBoundP A (fun i => isGroupOp i = true) 1 := by
    refine ⟨?_, fun _ => ⟨?_, fun _ => trivial⟩⟩
    · change (¬ true = true) ∨ 0 < 1
      decide
    · change (¬ false = true) ∨ 0 < 0
      decide
  refine ⟨?_, hb, isQueryBoundP_virtualize _ hb _⟩
  have hrb : readBack (fun _ : Unit => [0, 1])
      (fun _ => ([1, 3, 0] : List (ZMod 5))) = (fun _ => [1, 3]) := rfl
  have hs := runGen_virtualize (Model.group (ZMod 5)) (fun _ => id) A hw
  rw [hrb] at hs
  exact hs.symm

end GroupModel
