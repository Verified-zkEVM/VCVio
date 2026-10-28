/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.RoundTrip
public import Mathlib.Data.ZMod.Basic

/-!
Handle-to-explanation regression tests

The concrete two-sort interaction computes nontrivial combinations, observes an encoding,
samples a private coin, and receives new group inputs before producing its final explanation.
The stateful test keeps the entire ambient game state in the exact run equation.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace GroupModelTest

/-- A two-sort computation preserves values and effects through both translations and has
its expected chronological coefficient vectors after receiving computed game replies. -/
theorem two_sort_explanation :
    ∃ (A : HandleAdversary (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7)
        Unit Unit (fun _ => Unit) (ZMod 7 × Fin 2))
      (input : Message Unit (fun _ : Bool => ZMod 7))
      (random : QueryImpl unifSpec Id)
      (game : QueryImpl (plainSpec (fun _ : Bool => ZMod 7) Unit (fun _ => Unit)) Id),
      let B := toExplained A (fun _ => id)
      let z := B.run (withCoins random game) input
      z.1.coefficients true = [[1, 0, 1]] ∧
      z.1.coefficients false = [[1, 0, 1]] ∧
      z.1.value.groups true = [0] ∧ z.1.value.groups false = [4] ∧
      z.1.value.data = (5, 0) ∧
      (fun z => z.1.value) <$> B.run (withCoins random game) input =
        (fun z => lookupMessage z.2 z.1) <$>
          A.run (Model.discrete _) (fun _ => id) random game input ∧
      (fun z => lookupMessage z.2 z.1) <$>
          (ofExplained B (fun _ => id)).run (Model.discrete _) (fun _ => id) random game input =
        (fun z => lookupMessage z.2 z.1) <$>
          A.run (Model.discrete _) (fun _ => id) random game input := by
  let A : HandleAdversary (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7)
      Unit Unit (fun _ => Unit) (ZMod 7 × Fin 2) := fun input => do
    let a ← (HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Unit (fun _ => Unit)).query
      (.inl (.add true ((input.groups true).getD 0 0) ((input.groups true).getD 1 0)))
    let b ← (HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Unit (fun _ => Unit)).query
      (.inl (.smul true 2 ((input.groups true).getD 0 0)))
    let c ← (HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Unit (fun _ => Unit)).query
      (.inl (.add true a b))
    let d ← (HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Unit (fun _ => Unit)).query
      (.inl (.add false ((input.groups false).getD 0 0) ((input.groups false).getD 1 0)))
    let e ← (HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Unit (fun _ => Unit)).query
      (.inl (.smul false 3 d))
    let encoded ← (HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Unit (fun _ => Unit)).query
      (.inr (.inl (true, c)))
    let coin ← (HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Unit (fun _ => Unit)).query
      (.inr (.inr (.inl 1)))
    let reply ← (HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Unit (fun _ => Unit)).query
      (.inr (.inr (.inr ⟨(), fun s => [if s then c else e]⟩)))
    let f ← (HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Unit (fun _ => Unit)).query
      (.inl (.add true ((reply.groups true).getD 0 0) ((input.groups true).getD 0 0)))
    let g ← (HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Unit (fun _ => Unit)).query
      (.inl (.add false ((reply.groups false).getD 0 0) ((input.groups false).getD 0 0)))
    pure ⟨(encoded, coin), fun s => [if s then f else g]⟩
  let input : Message Unit (fun _ : Bool => ZMod 7) := ⟨(), fun _ => [1, 2]⟩
  let random : QueryImpl unifSpec Id := fun _ => ⟨0, Nat.zero_lt_succ _⟩
  let game : QueryImpl (plainSpec (fun _ : Bool => ZMod 7) Unit (fun _ => Unit)) Id :=
    fun q => ⟨(), fun s => [(q.groups s).getD 0 0 + 1]⟩
  refine ⟨A, input, random, game, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact toExplained_run A (Model.discrete _) (fun _ => id) random game input
  · exact ofExplained_toExplained_run A (Model.discrete _) (fun _ => id)
      (fun _ => id) (fun _ _ => rfl) random game input

/-- A private-coin-only adversary retains its sampled result and has no group explanations. -/
theorem private_coin_explanation :
    ∃ (A : HandleAdversary (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7)
        Unit Empty Empty.elim (Fin 2)),
      let random : QueryImpl unifSpec Id := fun _ => ⟨0, Nat.zero_lt_succ _⟩
      let game : QueryImpl (plainSpec (fun _ : Bool => ZMod 7) Empty Empty.elim) Id :=
        fun q => q.data.elim
      let input : Message Unit (fun _ : Bool => ZMod 7) := ⟨(), fun _ => []⟩
      let z := (toExplained A (fun _ => id)).run (withCoins random game) input
      z.1.value.data = 0 ∧ z.1.coefficients true = [] ∧ z.2 true = [] ∧
      (fun z => z.1.value) <$>
          (toExplained A (fun _ => id)).run (withCoins random game) input =
        (fun z => lookupMessage z.2 z.1) <$>
          A.run (Model.discrete _) (fun _ => id) random game input := by
  let A : HandleAdversary (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7)
      Unit Empty Empty.elim (Fin 2) := fun _ => do
    let coin ← (HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Empty Empty.elim).query
      (.inr (.inr (.inl 1)))
    pure ⟨coin, fun _ => []⟩
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact toExplained_run A (Model.discrete _) (fun _ => id) _ _ _

/-- The general translation equation preserves the state of a probabilistic stateful game. -/
theorem stateful_explanation {GameState Input Query Result : Type} {Reply : Query → Type}
    (A : HandleAdversary (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7)
      Input Query Reply Result)
    (random : QueryImpl unifSpec (StateT GameState ProbComp))
    (game : QueryImpl (plainSpec (fun _ : Bool => ZMod 7) Query Reply)
      (StateT GameState ProbComp))
    (input : Message Input (fun _ : Bool => ZMod 7)) (st : GameState) :
    ((fun z => z.1.value) <$>
      (toExplained A (fun _ => id)).run (withCoins random game) input).run st =
    ((fun z => lookupMessage z.2 z.1) <$>
      A.run (Model.discrete _) (fun _ => id) random game input).run st :=
  congrArg (fun p => p.run st)
    (toExplained_run A (Model.discrete _) (fun _ => id) random game input)

end GroupModelTest
