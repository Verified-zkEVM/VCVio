/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.GroupModel.Certificate

/-! # Group certificate regressions

The virtualization certificate preserves arbitrary group-operation budgets, including free
equality and coin queries. The setup and finalization test accounts for both surrounding phases.
-/

public section

open OracleComp OracleSpec GroupModel

namespace VCVioTest.GroupModel.Certificate

/-- The certified transfer gives virtualization's group-operation bound. -/
theorem virtualize_bound {F S : Type} {σ : Sig S} [DecidableEq S]
    (z : S → Handle) {α : Type} {A : OracleComp (genSpec F σ) α} {q : ℕ}
    (hA : IsQueryBoundP A (fun i => isGroupOp i = true) q)
    (s : Tbl (fun _ : S => Handle)) :
    IsQueryBoundP ((virtualize z A).run s) (fun i => isGroupOp i = true) q :=
  (costCertificate_virtualizeImpl z).simulateQ_run
    ((isQueryBoundP_iff_weighted A q).mp hA) s

/-- One setup operation and one final operation add two to the virtualized operation budget. -/
theorem setup_finish_bound :
    let A : OracleComp (genSpec ℕ groupSig) Bool := do
      let a ← (genSpec ℕ groupSig).query (.inl (.add () 0 1))
      let b ← (genSpec ℕ groupSig).query (.inl (.eq () a 0))
      pure b
    let setup : OracleComp (genSpec ℕ groupSig) (Tbl (fun _ : Unit => Handle)) := do
      let a ← (genSpec ℕ groupSig).query (.inl (.add () 0 0))
      pure (fun _ => [a])
    let finish : Bool → Tbl (fun _ : Unit => Handle) →
        OracleComp (genSpec ℕ groupSig) Bool := fun a _ => do
      let _ ← (genSpec ℕ groupSig).query (.inl (.add () 0 0))
      pure a
    IsQueryBoundP (do
      let s ← setup
      let (a, st) ← (simulateQ (virtualizeImpl (fun _ => 0)) A).run s
      finish a st) (fun i => isGroupOp i = true) 3 := by
  dsimp only
  have hc : CostCertificate (virtualizeImpl (F := ℕ) (σ := groupSig) (fun _ => 0))
      (fun t => (fun k : Bool => if k then 1 else 0) (isGroupOp t)) :=
    costCertificate_virtualizeImpl _
  have hb := hc.transfer_per_kind isGroupOp (fun k => if k then 1 else 0) (fun _ => 1)
    (A := do
      let a ← (genSpec ℕ groupSig).query (.inl (.add () 0 1))
      let b ← (genSpec ℕ groupSig).query (.inl (.eq () a 0))
      pure b)
    (by
      intro k
      cases k <;> refine ⟨?_, fun _ => ⟨?_, fun _ => trivial⟩⟩
      all_goals first | exact Or.inr Nat.zero_lt_one | exact Or.inl Bool.false_ne_true)
    (do
      let a ← (genSpec ℕ groupSig).query (.inl (.add () 0 0))
      pure (fun _ => [a]))
    (fun a _ => do
      let _ ← (genSpec ℕ groupSig).query (.inl (.add () 0 0))
      pure a)
    (cSetup := 1) (cFinish := 1) (c₀ := 2)
    (by simp [isGroupOp]) (by intros; simp [isGroupOp]) (by decide)
  simpa [Fintype.sum_bool] using hb

end VCVioTest.GroupModel.Certificate
