/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Game
public import Mathlib.Data.ZMod.Basic

/-!
# Executable handle-game checks

Two sorts exercise group operations, encodings, coins, and replies containing group elements.
A separate game retains hidden state between identical requests.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

open Interaction

/-- Every fixed coin produces the expected encoding, reply handles, and two-sort table. -/
theorem handle_game_fixed_coin (coin : Fin 2) :
    let M : Model (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7) :=
      ⟨Empty.elim, Empty.elim⟩
    let random : QueryImpl unifSpec Id := fun n =>
      pure ⟨coin.val % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    let game : QueryImpl (plainSpec (fun _ : Bool => ZMod 7) Unit (fun _ => Unit)) Id :=
      fun q => pure ⟨(), fun s => q.groups s ++ [if s then 6 else 4]⟩
    let Ω := spec (ZMod 7) (discreteSig Bool) +
      (encSpec (fun _ : Bool => ZMod 7) +
        (unifSpec + handleSpec (S := Bool) Unit (fun _ => Unit)))
    let A : HandleAdversary (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7)
        Unit Unit (fun _ => Unit) (ZMod 7 × Fin 2) := fun input => do
      let h ← Ω.query (.inl (.add false (input.groups false).head! 1))
      let e ← Ω.query (.inr (.inl (false, h)))
      let c ← Ω.query (.inr (.inr (.inl 1)))
      let r ← Ω.query (.inr (.inr (.inr ⟨(), fun s => if s then [0] else [h]⟩)))
      pure ⟨(e, c), r.groups⟩
    let z := A.run M (fun _ => id) random game ⟨(), fun s => if s then [3] else [1, 2]⟩
    z.1.data = (3, coin) ∧ z.1.groups false = [3, 4] ∧ z.1.groups true = [1, 2] ∧
      z.2 false = [1, 2, 3, 3, 4] ∧ z.2 true = [3, 3, 6] := by
  fin_cases coin <;> decide

/-- Identical game requests see persistent hidden state and install different replies. -/
theorem handle_game_hidden_state :
    let M : Model (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7) :=
      ⟨Empty.elim, Empty.elim⟩
    let random : QueryImpl unifSpec (StateT Bool ProbComp) :=
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Bool ProbComp)
    let game : QueryImpl (plainSpec (fun _ : Bool => ZMod 7) Unit (fun _ => Bool))
        (StateT Bool ProbComp) := fun _ => do
      let b ← get
      set (!b)
      pure ⟨b, fun s => [if s then (if b then 6 else 5) else (if b then 4 else 3)]⟩
    let Ω := spec (ZMod 7) (discreteSig Bool) +
      (encSpec (fun _ : Bool => ZMod 7) +
        (unifSpec + handleSpec (S := Bool) Unit (fun _ => Bool)))
    let A : HandleAdversary (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7)
        Unit Unit (fun _ => Bool) (Bool × Bool) := fun _ => do
      let a ← Ω.query (.inr (.inr (.inr ⟨(), fun _ => []⟩)))
      let b ← Ω.query (.inr (.inr (.inr ⟨(), fun _ => []⟩)))
      pure ⟨(a.data, b.data), fun s => a.groups s ++ b.groups s⟩
    (A.run M (fun _ => id) random game ⟨(), fun _ => []⟩).run false =
      pure ((⟨(false, true), fun _ => [0, 1]⟩,
        fun s => if s then [5, 6] else [3, 4]), false) := by
  dsimp only
  simp only [HandleAdversary.run, run, simulateQ_bind, simulateQ_pure,
    simulateQ_spec_query, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_pure]
  change (pure ((⟨(false, true), fun _ => [0, 1]⟩,
    fun s => [if s then 5 else 3, if s then 6 else 4]), false) :
      ProbComp ((Message (Bool × Bool) (fun _ : Bool => Handle) ×
        Tbl (fun _ : Bool => ZMod 7)) × Bool)) = _
  congr 3
  funext s
  cases s <;> rfl

/-- The concrete generic inclusion preserves a group query, coin, and game request. -/
theorem generic_game_inclusion :
    let M : Model (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7) :=
      ⟨Empty.elim, Empty.elim⟩
    let Γ : OracleSpec Unit := fun _ => Unit
    let Ω := spec (ZMod 7) (discreteSig Bool) + (unifSpec + Γ)
    let A : OracleComp Ω (Handle × Fin 2) := do
      let h ← Ω.query (.inl (.add true 0 1))
      let c ← Ω.query (.inr (.inl 1))
      let _ ← Ω.query (.inr (.inr ()))
      pure (h, c)
    let random := QueryImpl.ofLift unifSpec ProbComp
    let game : QueryImpl Γ (StateT (Tbl fun _ : Bool => ZMod 7) ProbComp) :=
      fun _ => pure ()
    run M (fun _ => id) (encImpl (m := ProbComp) (V := fun _ : Bool => ZMod 7) (fun _ => id) +
        (coinImpl (G := fun _ : Bool => ZMod 7) random + game))
        (toAlgebraic A) (fun _ => [1, 2]) =
      run M (fun _ => id) (coinImpl (G := fun _ : Bool => ZMod 7) random + game)
        A (fun _ => [1, 2]) := by
  dsimp only
  exact run_toAlgebraic _ _ _ _ _ _ _

end GroupModel
