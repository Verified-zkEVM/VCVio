/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.OfExplained
public import Mathlib.Data.ZMod.Basic

/-!
Certified explanations realized over two sorts

The mixed interaction samples a private coin, sends two-term combinations at both sorts,
receives group replies, and includes those replies in its final combinations.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

open Interaction

/-- A two-sort certified interaction reads back to the same concrete result after compilation. -/
theorem ofExplained_two_sorts :
    let G := fun _ : Bool => ZMod 7
    let Ω := explainedSpec (ZMod 7) G (CoinQuery Unit) (CoinReply (fun _ => Unit))
    let program : Message Unit G → OracleComp Ω (Explained (ZMod 7) (Fin 2) G) :=
      fun input => do
        let coin ← Ω.query (Explained.ofVectors input.groups (.inr 1) (fun _ => []))
        let basis := extend input.groups coin.groups
        let reply ← Ω.query (Explained.ofVectors basis (.inl ()) (fun _ =>
          [fun i => if i.val = 0 then 2 else if i.val = 1 then 3 else 0]))
        pure (Explained.ofVectors (extend basis reply.groups) coin.data (fun s =>
          [fun i => if i.val = 0 then 1 else if i.val = (basis s).length then 4 else 0]))
    ∃ cert : ∀ input, IsAlgebraic input.groups (program input),
      let B : Adversary (ZMod 7) G Unit (CoinQuery Unit) (CoinReply (fun _ => Unit)) (Fin 2) :=
        ⟨program, cert⟩
      let M : Model (ZMod 7) (discreteSig Bool) G := ⟨(fun o => nomatch o), (fun o => nomatch o)⟩
      let random : QueryImpl unifSpec Id := fun n => pure ⟨1 % (n + 1), Nat.mod_lt _ (by omega)⟩
      let game : QueryImpl (plainSpec G Unit (fun _ => Unit)) Id :=
        fun q => pure ⟨(), fun s => [(q.groups s).headD 0 + 1]⟩
      let input : Message Unit G := ⟨(), fun s => if s then [3, 4] else [1, 2]⟩
      (fun z => lookupMessage z.2 z.1) <$>
          (ofExplained B (fun _ => id)).run M (fun _ => id) random game input =
        (fun z => z.1.value) <$> B.run (withCoins random game) input ∧
      lookupMessage ((ofExplained B (fun _ => id)).run M (fun _ => id) random game input).2
          ((ofExplained B (fun _ => id)).run M (fun _ => id) random game input).1 =
        ⟨1, fun _ => [2]⟩ := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro input
    rw [isAlgebraic_query]
    refine ⟨Explained.valid_ofVectors _ _ _, fun coin => ?_⟩
    rw [isAlgebraic_query]
    exact ⟨Explained.valid_ofVectors _ _ _, fun reply => Explained.valid_ofVectors _ _ _⟩
  · constructor
    · exact ofExplained_run _ _ _ _ _ _ (by intros; rfl) _
    · change (fun z => lookupMessage z.2 z.1) <$>
        (ofExplained (F := ZMod 7) (G := fun _ : Bool => ZMod 7) _ _).run
          (G := fun _ : Bool => ZMod 7) (N := Id) _ _ _ _ _ = _
      rw [ofExplained_run _ _ _ _ _ _ (by intros; rfl)]
      apply (show ∀ a b : Message (Fin 2) (fun _ : Bool => ZMod 7),
          a.data = b.data → a.groups = b.groups → a = b from by
        intro a b hd hg
        cases a
        cases b
        cases hd
        cases hg
        rfl)
      · decide
      · funext s
        cases s <;> decide

/-- Private-coin-only interactions use the same shared randomness and return no group values. -/
theorem ofExplained_private_coin :
    let G := fun _ : Bool => ZMod 7
    let Ω := explainedSpec (ZMod 7) G (CoinQuery Empty) (CoinReply Empty.elim)
    let program : Message Unit G → OracleComp Ω (Explained (ZMod 7) (Fin 2) G) :=
      fun input => do
        let coin ← Ω.query (Explained.ofVectors input.groups (.inr 1) (fun _ => []))
        pure (Explained.ofVectors (extend input.groups coin.groups) coin.data (fun _ => []))
    ∃ cert : ∀ input, IsAlgebraic input.groups (program input),
      let B : Adversary (ZMod 7) G Unit (CoinQuery Empty) (CoinReply Empty.elim) (Fin 2) :=
        ⟨program, cert⟩
      let M : Model (ZMod 7) (discreteSig Bool) G := ⟨(fun o => nomatch o), (fun o => nomatch o)⟩
      let random : QueryImpl unifSpec Id := fun _ => pure 0
      let game : QueryImpl (plainSpec G Empty Empty.elim) Id := fun q => q.data.elim
      lookupMessage ((ofExplained B (fun _ => id)).run M (fun _ => id) random game
          ⟨(), fun _ => []⟩).2
        ((ofExplained B (fun _ => id)).run M (fun _ => id) random game
          ⟨(), fun _ => []⟩).1 = ⟨0, fun _ => []⟩ := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro input
    rw [isAlgebraic_query]
    exact ⟨Explained.valid_ofVectors _ _ _, fun coin => Explained.valid_ofVectors _ _ _⟩
  · change (fun z => lookupMessage z.2 z.1) <$>
        (ofExplained (F := ZMod 7) (G := fun _ : Bool => ZMod 7) _ _).run
          (G := fun _ : Bool => ZMod 7) (N := Id) _ _ _ _ _ = _
    rw [ofExplained_run _ _ _ _ _ _ (by intros; rfl)]
    rfl

end GroupModel
