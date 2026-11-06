/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Collision
public import Mathlib.Data.ZMod.Basic

/-!
Collision bounds over the field with seven elements

A constant observation identifies zero and one. A single equality query attains the collision
bound, whereas an addition query has no collision and identical table semantics.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace GroupModel

/-- A single equality query on distinct values has collision probability and total variation one. -/
theorem collision_bound_attained :
    let M : Model (ZMod 7) groupSig (fun _ => ZMod 7) := ⟨Empty.elim, Empty.elim⟩
    let obs : (s : Unit) → ZMod 7 → Unit := fun _ _ => ()
    let tbl : Tbl (fun _ : Unit => ZMod 7) := fun _ => [0, 1]
    let oa : OracleComp (genSpec (ZMod 7) groupSig) Bool :=
      (genSpec (ZMod 7) groupSig).query (.inl (.eq () 0 1))
    let : MeasurableSpace (Bool × Tbl (fun _ : Unit => ZMod 7)) := ⊤
    collisionProbGen M obs oa tbl = 1 ∧
      measureETVDist (runGen M obs oa tbl) (runGen M (fun _ => id) oa tbl) = 1 := by
  dsimp only
  let M : Model (ZMod 7) groupSig (fun _ => ZMod 7) := ⟨Empty.elim, Empty.elim⟩
  let obs : (s : Unit) → ZMod 7 → Unit := fun _ _ => ()
  let tbl : Tbl (fun _ : Unit => ZMod 7) := fun _ => [0, 1]
  let oa : OracleComp (genSpec (ZMod 7) groupSig) Bool :=
    (genSpec (ZMod 7) groupSig).query (.inl (.eq () 0 1))
  let : MeasurableSpace (Bool × Tbl (fun _ : Unit => ZMod 7)) := ⊤
  change collisionProbGen M obs oa tbl = 1 ∧
    measureETVDist (runGen M obs oa tbl) (runGen M (fun _ => id) oa tbl) = 1
  have hc : collisionProbGen M obs oa tbl = 1 := by
    change Pr{let z ← (pure (false, tbl, true) :
      ProbComp (Bool × Tbl (fun _ : Unit => ZMod 7) × Bool))}[z.2.2 = true] = 1
    simp
  have ho : runGen M obs oa tbl = pure (true, tbl) := rfl
  have he : runGen M (fun _ => id) oa tbl = pure (false, tbl) := rfl
  refine ⟨hc, le_antisymm (hc ▸ measureETVDist_runGen_le_collisionProbGen M obs oa tbl) ?_⟩
  have h := prEvent_le_prEvent_add_measureETVDist
    (runGen M obs oa tbl) (runGen M (fun _ => id) oa tbl)
    (fun z => z.1 = true) Measurable.of_discrete
  simpa [ho, he] using h

/-- An addition query raises no collision flag and gives the same output and table in both runs. -/
theorem no_equality_no_collision :
    let M : Model (ZMod 7) groupSig (fun _ => ZMod 7) := ⟨Empty.elim, Empty.elim⟩
    let obs : (s : Unit) → ZMod 7 → Unit := fun _ _ => ()
    let tbl : Tbl (fun _ : Unit => ZMod 7) := fun _ => [0, 1]
    let oa : OracleComp (genSpec (ZMod 7) groupSig) Handle :=
      (genSpec (ZMod 7) groupSig).query (.inl (.add () 0 1))
    collisionProbGen M obs oa tbl = 0 ∧
      runGen M obs oa tbl = runGen M (fun _ => id) oa tbl := by
  dsimp only
  constructor
  · change Pr{let z ← (pure (2, (fun _ : Unit => ([0, 1, 1] : List (ZMod 7))), false) :
        ProbComp (Handle × Tbl (fun _ : Unit => ZMod 7) × Bool))}[z.2.2 = true] = 0
    simp
  · rfl

end GroupModel
