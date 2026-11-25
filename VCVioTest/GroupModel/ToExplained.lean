/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.RoundTrip
public import Mathlib.Data.ZMod.Basic
import all VCVio.CryptoFoundations.GroupModel.OfExplained

/-!
# Handle-to-explanation regression tests

The concrete two-sort adversary computes combinations whose coefficient vectors are not
palindromes, so the chronological order of the basis is pinned. It asks an equality query on two
handles with equal values and different representations, reads an encoding, samples the largest
coin, and receives new group inputs before producing its final explanation. A private-coin-only
adversary keeps its sample and explains nothing. A stateful game answers two identical requests
`false` and then `true`, and the explained and handle runs end in the same game state. A
certified adversary on linearly dependent inputs keeps its coefficient vectors through the round
trip `toExplained ∘ ofExplained`.

The round trip is evaluated by `decide`, which unfolds `ofExplained` and its private helpers, so
their module is imported with `import all`.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace GroupModelTest

/-! ## A two-sort adversary -/

/-- The oracles of the two-sort adversary. -/
private abbrev TwoSortSpec := HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Unit (fun _ => Unit)

/-- At sort `true`, from inputs `x₀, x₁`, build `c = (x₀ + x₁) + 2 x₀` and `5 x₀` and test them
for equality. At sort `false`, from inputs `y₀, y₁`, build `d = 3 y₁` and `e = d + y₀`. Read the
encoding of `c`, sample a coin in `Fin 2`, send `c` and `e` to the game, and return `r + c` and
`r' + d` for its replies `r, r'`, with the encoding, the coin and the equality answer as data. -/
private def twoSortAdversary : HandleAdversary (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7)
    Unit Unit (fun _ => Unit) (ZMod 7 × Fin 2 × Bool) := fun input => do
  let a ← TwoSortSpec.query
    (.inl (.add true ((input.groups true).getD 0 0) ((input.groups true).getD 1 0)))
  let b ← TwoSortSpec.query (.inl (.smul true 2 ((input.groups true).getD 0 0)))
  let c ← TwoSortSpec.query (.inl (.add true a b))
  let five ← TwoSortSpec.query (.inl (.smul true 5 ((input.groups true).getD 0 0)))
  let same ← TwoSortSpec.query (.inl (.eq true c five))
  let d ← TwoSortSpec.query (.inl (.smul false 3 ((input.groups false).getD 1 0)))
  let e ← TwoSortSpec.query (.inl (.add false d ((input.groups false).getD 0 0)))
  let encoded ← TwoSortSpec.query (.inr (.inl (true, c)))
  let coin ← TwoSortSpec.query (.inr (.inr (.inl 1)))
  let reply ← TwoSortSpec.query (.inr (.inr (.inr ⟨(), fun s => [if s then c else e]⟩)))
  let f ← TwoSortSpec.query (.inl (.add true ((reply.groups true).getD 0 0) c))
  let g ← TwoSortSpec.query (.inl (.add false ((reply.groups false).getD 0 0) d))
  pure ⟨(encoded, coin, same), fun s => [if s then f else g]⟩

/-- Inputs `x₀, x₁ = 1, 2` at sort `true` and `y₀, y₁ = 3, 5` at sort `false`. -/
private def twoSortInput : Message Unit (fun _ : Bool => ZMod 7) :=
  ⟨(), fun s => if s then [1, 2] else [3, 5]⟩

/-- Coins answer each request with the largest value. -/
private def lastCoin : QueryImpl unifSpec Id := fun n => Fin.last n

/-- The game replies at each sort with one more than the first element it receives there. -/
private def succGame : QueryImpl (plainSpec (fun _ : Bool => ZMod 7) Unit (fun _ => Unit)) Id :=
  fun q => ⟨(), fun s => [(q.groups s).getD 0 0 + 1]⟩

/-- The explained run of the two-sort adversary. The game replies `6` to `c = 5` and `5` to
`e = 4`. The output `r + c = r + 3 x₀ + x₁` at sort `true` has coefficients `[3, 1, 1]` over
`x₀, x₁, r`, and `r' + d = r' + 3 y₁` at sort `false` has `[0, 3, 1]` over `y₀, y₁, r'`. The
equality test answers `true` from the values of `c` and `5 x₀`, whose coefficients differ. -/
private theorem twoSort_explained :
    let z := (toExplained twoSortAdversary (fun _ => id)).run
      (withCoins lastCoin succGame) twoSortInput
    z.1.coefficients true = [[3, 1, 1]] ∧ z.1.coefficients false = [[0, 3, 1]] ∧
      z.1.value.groups true = [4] ∧ z.1.value.groups false = [6] ∧
      z.1.value.data = (5, 1, true) := by
  decide +kernel

/-- The handle run of the two-sort adversary reads back to the same values. -/
private theorem twoSort_handles :
    let z := twoSortAdversary.run (Model.discrete _) (fun _ => id) lastCoin succGame twoSortInput
    (lookupMessage z.2 z.1).groups true = [4] ∧ (lookupMessage z.2 z.1).groups false = [6] ∧
      (lookupMessage z.2 z.1).data = (5, 1, true) := by
  decide +kernel

/-- Both translations apply to the two-sort adversary at these instances. -/
private theorem twoSort_run :
    (fun z => z.1.value) <$>
        (toExplained twoSortAdversary (fun _ => id)).run (withCoins lastCoin succGame)
          twoSortInput =
      (fun z => lookupMessage z.2 z.1) <$>
        twoSortAdversary.run (Model.discrete _) (fun _ => id) lastCoin succGame twoSortInput ∧
    (fun z => lookupMessage z.2 z.1) <$>
        (ofExplained (toExplained twoSortAdversary (fun _ => id)) (fun _ => id)).run
          (Model.discrete _) (fun _ => id) lastCoin succGame twoSortInput =
      (fun z => lookupMessage z.2 z.1) <$>
        twoSortAdversary.run (Model.discrete _) (fun _ => id) lastCoin succGame twoSortInput :=
  ⟨toExplained_run twoSortAdversary (Model.discrete _) (fun _ => id) lastCoin succGame
      twoSortInput,
    ofExplained_toExplained_run twoSortAdversary (Model.discrete _) (fun _ => id) (fun _ => id)
      (fun _ _ => rfl) lastCoin succGame twoSortInput⟩

/-! ## Private coins only -/

/-- Sample a coin in `Fin 2` and return it with no group elements. -/
private def coinAdversary : HandleAdversary (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7)
    Unit Empty Empty.elim (Fin 2) := fun _ => do
  let coin ← (HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Empty Empty.elim).query
    (.inr (.inr (.inl 1)))
  pure ⟨coin, fun _ => []⟩

/-- The game has no requests. -/
private def emptyGame : QueryImpl (plainSpec (fun _ : Bool => ZMod 7) Empty Empty.elim) Id :=
  fun q => q.data.elim

/-- A private-coin-only adversary keeps its sample and has no group explanations. -/
private theorem private_coin_explanation :
    let z := (toExplained coinAdversary (fun _ => id)).run (withCoins lastCoin emptyGame)
      ⟨(), fun _ => []⟩
    z.1.value.data = 1 ∧ z.1.coefficients true = [] ∧ z.2 true = [] ∧
      (fun z => z.1.value) <$>
          (toExplained coinAdversary (fun _ => id)).run (withCoins lastCoin emptyGame)
            ⟨(), fun _ => []⟩ =
        (fun z => lookupMessage z.2 z.1) <$>
          coinAdversary.run (Model.discrete _) (fun _ => id) lastCoin emptyGame
            ⟨(), fun _ => []⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact toExplained_run coinAdversary (Model.discrete _) (fun _ => id) _ _ _

/-! ## A stateful game -/

/-- A game that counts its requests answers two identical requests with no group elements `false`
and then `true`. The explained run and the handle run both read these answers and the largest coin
`2` between them, and both leave the game in state `2`. -/
theorem repeat_game_state :
    let Ω := HandleSpec (ZMod 7) Bool (fun _ => ZMod 7) Unit (fun _ => Bool)
    let A : HandleAdversary (ZMod 7) (discreteSig Bool) (fun _ => ZMod 7)
        Unit Unit (fun _ => Bool) (Bool × Fin 3 × Bool) := fun _ => do
      let first ← Ω.query (.inr (.inr (.inr ⟨(), fun _ => []⟩)))
      let coin ← Ω.query (.inr (.inr (.inl 2)))
      let second ← Ω.query (.inr (.inr (.inr ⟨(), fun _ => []⟩)))
      pure ⟨(first.data, coin, second.data), fun _ => []⟩
    let game : QueryImpl (plainSpec (fun _ : Bool => ZMod 7) Unit (fun _ => Bool)) (StateM ℕ) :=
      fun _ => modifyGet fun n => (⟨decide (0 < n), fun _ => []⟩, n + 1)
    let random : QueryImpl unifSpec (StateM ℕ) := fun n => pure (Fin.last n)
    let explained :=
      ((toExplained A (fun _ => id)).run (withCoins random game) ⟨(), fun _ => []⟩).run 0
    let handles := (A.run (Model.discrete _) (fun _ => id) random game ⟨(), fun _ => []⟩).run 0
    explained.1.1.value.data = (false, 2, true) ∧ explained.2 = 2 ∧
      (lookupMessage handles.1.2 handles.1.1).data = (false, 2, true) ∧ handles.2 = 2 := by
  decide +kernel

/-! ## The round trip through handles -/

/-- On two inputs `x₀, x₁` at each sort, output `2 x₀ + 3 x₁` at both sorts. -/
private def combineAdversary : Interaction.Adversary (ZMod 7) (fun _ : Bool => ZMod 7) Unit
    (CoinQuery Empty) (CoinReply (Empty.elim : Empty → Type)) Unit where
  main input := pure (Explained.ofVectors input.groups ()
    (fun _ => [fun i => if i.val = 0 then 2 else 3]))
  algebraic input := Explained.valid_ofVectors input.groups () _

/-- Inputs `1, 1` at sort `true`, which are linearly dependent, and `1, 2` at sort `false`. -/
private def combineInput : Message Unit (fun _ : Bool => ZMod 7) :=
  ⟨(), fun s => if s then [1, 1] else [1, 2]⟩

/-- The round trip of `combineAdversary` keeps its values, as `toExplained_ofExplained_run`
states, and also its coefficient vectors `[2, 3]`, although at sort `true` the vector `[5, 0]`
explains the same output `5`. -/
private theorem combine_roundTrip :
    let z := (toExplained (ofExplained combineAdversary (fun _ => id)) (fun _ => id)).run
      (withCoins lastCoin emptyGame) combineInput
    z.1.coefficients true = [[2, 3]] ∧ z.1.coefficients false = [[2, 3]] ∧
      z.1.value.groups true = [5] ∧ z.1.value.groups false = [1] ∧
      (fun z => z.1.value) <$>
          (toExplained (ofExplained combineAdversary (fun _ => id)) (fun _ => id)).run
            (withCoins lastCoin emptyGame) combineInput =
        (fun z => z.1.value) <$> combineAdversary.run (withCoins lastCoin emptyGame)
          combineInput := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact toExplained_ofExplained_run _ _ _ (fun _ _ => rfl) _ _ _

end GroupModelTest
