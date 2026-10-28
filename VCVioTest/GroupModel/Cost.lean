/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Cost
public import Mathlib.Data.ZMod.Basic

/-! # Group-operation budget regressions

Concrete runs over seven elements distinguish operation costs from free comparisons.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

/-- Two additions and one scalar multiplication cost three, despite three comparisons,
and append exactly three entries to every initial one-sort table. -/
theorem three_operations (tbl : Tbl (fun _ : Unit => ZMod 7)) :
    let M : Model (ZMod 7) groupSig (fun _ => ZMod 7) := ⟨Empty.elim, Empty.elim⟩
    let oa : OracleComp (genSpec (ZMod 7) groupSig) Unit := do
      let a ← (genSpec (ZMod 7) groupSig).query (.inl (.add () 0 0))
      let _ ← (genSpec (ZMod 7) groupSig).query (.inl (.eq () a 0))
      let b ← (genSpec (ZMod 7) groupSig).query (.inl (.add () a 0))
      let _ ← (genSpec (ZMod 7) groupSig).query (.inl (.eq () a b))
      let c ← (genSpec (ZMod 7) groupSig).query (.inl (.smul () 3 b))
      let _ ← (genSpec (ZMod 7) groupSig).query (.inl (.eq () c 0))
      pure ()
    IsQueryBoundP oa (fun i => isGroupOp i = true) 3 ∧
      ¬ IsQueryBoundP oa (fun i => isGroupOp i = true) 2 ∧
      ∀ z ∈ support (runGen M (fun _ => id) oa tbl),
        (z.2 ()).length = (tbl ()).length + 3 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp [isGroupOp, Query.isOp]
  · intro h
    have bad := ((((h.2 (0 : Handle)).2 false).2 (0 : Handle)).2 false).1
    change (¬ true = true) ∨ 0 < 0 at bad
    simp only [not_true_eq_false, Nat.lt_irrefl, or_self] at bad
  · intro z hz
    simp [runGen, run, impl, push, StateT.run, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet] at hz
    subst z
    simp [append]

/-- Three equality queries preserve the entire table and require no group-operation budget. -/
theorem equality_only (tbl : Tbl (fun _ : Unit => ZMod 7)) :
    let M : Model (ZMod 7) groupSig (fun _ => ZMod 7) := ⟨Empty.elim, Empty.elim⟩
    let oa : OracleComp (genSpec (ZMod 7) groupSig) Bool := do
      let _ ← (genSpec (ZMod 7) groupSig).query (.inl (.eq () 0 1))
      let _ ← (genSpec (ZMod 7) groupSig).query (.inl (.eq () 1 2))
      let b ← (genSpec (ZMod 7) groupSig).query (.inl (.eq () 0 2))
      pure b
    IsQueryBoundP oa (fun i => isGroupOp i = true) 0 ∧
      ∀ z ∈ support (runGen M (fun _ => id) oa tbl), z.2 = tbl := by
  dsimp only
  constructor
  · exact ⟨by decide, fun _ => ⟨by decide, fun _ =>
      ⟨by decide, fun _ => trivial⟩⟩⟩
  · intro z hz
    simpa [runGen, run, impl, StateT.run] using
      congrArg Prod.snd ((mem_support_pure_iff _ _).mp hz)

end GroupModel
