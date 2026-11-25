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

The adversary adds its two inputs and compares the sum with handle `3`, which is out of range
for its own table but in range for the surrounding one. The surrounding table is `[1, 3, 0]`,
with the designated zero entry at handle `2`, and the adversary's handles `0, 1` translate to
`0, 1`.

The checks evaluate the virtualized program and its run. The program issues each operation
once and sends handle `3` as the zero handle `2`, so the comparison answers `false`, as the
direct run on `[1, 3]` does. Passing handle `3` through untranslated would compare the sum with
itself in the surrounding table and answer `true`.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

/-- The virtualized program issues the addition and the comparison once each, translates the
out-of-range handle `3` to the zero handle `2`, and records the fresh outer handle. -/
theorem virtualize_program :
    let A : OracleComp (genSpec (ZMod 5) groupSig) Bool := do
      let h ← (genSpec (ZMod 5) groupSig).query (.inl (.add () 0 1))
      let b ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () h 3))
      pure b
    (virtualize (fun _ => 2) A).run (fun _ => [0, 1]) =
      ((do
        let h ← (genSpec (ZMod 5) groupSig).query (.inl (.add () 0 1))
        let b ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () h 2))
        pure (b, append (fun _ : Unit => ([0, 1] : List Handle)) () h)) :
          OracleComp (genSpec (ZMod 5) groupSig) (Bool × Tbl (fun _ : Unit => Handle))) :=
  rfl

/-- The virtualized run on `[1, 3, 0]` answers `false`, extends the translation by the outer
handle `3`, and appends the sum `4`. -/
theorem virtualize_run :
    let A : OracleComp (genSpec (ZMod 5) groupSig) Bool := do
      let h ← (genSpec (ZMod 5) groupSig).query (.inl (.add () 0 1))
      let b ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () h 3))
      pure b
    runGen (Model.group (ZMod 5)) (fun _ => id) ((virtualize (fun _ => 2) A).run (fun _ => [0, 1]))
        (fun _ => [1, 3, 0]) =
      pure ((false, fun _ => [0, 1, 3]), fun _ => [1, 3, 0, 4]) :=
  rfl

/-- The direct run on `[1, 3]` answers `false` with table `[1, 3, 4]`, which is the read-back of
the virtualized run's final translation and table. -/
theorem virtualize_direct_run :
    let A : OracleComp (genSpec (ZMod 5) groupSig) Bool := do
      let h ← (genSpec (ZMod 5) groupSig).query (.inl (.add () 0 1))
      let b ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () h 3))
      pure b
    runGen (Model.group (ZMod 5)) (fun _ => id) A (fun _ => [1, 3]) =
        pure (false, fun _ => [1, 3, 4]) ∧
      readBack (fun _ : Unit => [0, 1, 3]) (fun _ => ([1, 3, 0, 4] : List (ZMod 5))) =
        fun _ => [1, 3, 4] :=
  ⟨rfl, rfl⟩

/-- Without translation, the comparison with handle `3` in the surrounding table answers
`true`. -/
theorem untranslated_run :
    runGen (Model.group (ZMod 5)) (fun _ => id)
        ((do
          let h ← (genSpec (ZMod 5) groupSig).query (.inl (.add () 0 1))
          let b ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () h 3))
          pure b) : OracleComp (genSpec (ZMod 5) groupSig) Bool)
        (fun _ => [1, 3, 0]) =
      pure (true, fun _ => [1, 3, 0, 4]) :=
  rfl

/-- The adversary's one-operation budget transports to the virtualized program, where it is
tight: the virtualized program exceeds a budget of zero. -/
theorem virtualize_budget :
    let A : OracleComp (genSpec (ZMod 5) groupSig) Bool := do
      let h ← (genSpec (ZMod 5) groupSig).query (.inl (.add () 0 1))
      let b ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () h 3))
      pure b
    IsQueryBoundP ((virtualize (fun _ => 2) A).run (fun _ => [0, 1]))
        (fun i => isGroupOp i = true) 1 ∧
      ¬ IsQueryBoundP ((virtualize (fun _ => 2) A).run (fun _ => [0, 1]))
        (fun i => isGroupOp i = true) 0 := by
  intro A
  have hb : IsQueryBoundP A (fun i => isGroupOp i = true) 1 := by
    refine ⟨?_, fun _ => ⟨?_, fun _ => trivial⟩⟩
    · change (¬ true = true) ∨ 0 < 1
      decide
    · change (¬ false = true) ∨ 0 < 0
      decide
  refine ⟨isQueryBoundP_virtualize _ hb _, fun h => ?_⟩
  rw [virtualize_program] at h
  have h₀ : (¬ true = true) ∨ 0 < 0 := h.1
  exact absurd h₀ (by decide)

end GroupModel
