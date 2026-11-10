/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.OfExplained
public import Mathlib.Data.ZMod.Basic
public import ToMathlib.Data.FinEnum
import all VCVio.CryptoFoundations.GroupModel.OfExplained

/-!
# Certified explanations realized as handle adversaries

The mixed interaction samples a private coin, sends two-term combinations at both sorts,
receives group replies, and includes those replies in its final combinations. A one-sort
adversary outputs three vectors over two received elements: one with a single nonzero
coefficient, an all-zero vector, and one with two nonzero coefficients. Its table pins the group
operations of the compilation: one `smul` per nonzero coefficient, one `add` joining two
partial sums, and one `smul` by zero for the all-zero vector.

The compiled handle runs are evaluated by `decide`, which unfolds `ofExplained` and its private
helpers, so their module is imported with `import all`. `ofExplained_run` is applied separately
at the same instances.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

open Interaction

/-- Messages over `Bool` sorts agree when their data and both sorts' group lists agree. -/
private theorem message_eq {Data : Type} {G : Bool → Type} {a b : Message Data G}
    (hd : a.data = b.data) (hg : ∀ s, a.groups s = b.groups s) : a = b := by
  cases a
  cases b
  cases hd
  cases funext hg
  rfl

/-- A two-sort certified interaction: `ofExplained_run` applies at these instances, and the
compiled run, evaluated directly, reads back to the concrete result. -/
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
    · exact message_eq (by decide +kernel) fun s => by cases s <;> decide +kernel

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
  · exact message_eq (by decide) fun s => by cases s <;> decide

/-- The compiled run of a one-sort adversary with three output vectors over the received
elements `3, 5`: `[2, 0]` is one `smul`, `[0, 0]` one `smul` by zero, and `[1, 4]` two `smul`
and one `add`. The run returns the handles of those entries, the table holds exactly these five
operations after the input, and the handles read back to the evaluated vectors. -/
theorem ofExplained_zero_coefficients :
    let G := fun _ : Unit => ZMod 7
    let Ω := explainedSpec (ZMod 7) G (CoinQuery Empty) (CoinReply Empty.elim)
    let program : Message Unit G → OracleComp Ω (Explained (ZMod 7) Unit G) :=
      fun input => pure (Explained.ofVectors input.groups () fun _ =>
        [fun i => if i.val = 0 then 2 else 0, fun _ => 0,
          fun i => if i.val = 0 then 1 else 4])
    ∃ cert : ∀ input, IsAlgebraic input.groups (program input),
      let B : Adversary (ZMod 7) G Unit (CoinQuery Empty) (CoinReply Empty.elim) Unit :=
        ⟨program, cert⟩
      let M : Model (ZMod 7) (discreteSig Unit) G := ⟨(fun o => nomatch o), (fun o => nomatch o)⟩
      let random : QueryImpl unifSpec Id := fun _ => pure 0
      let game : QueryImpl (plainSpec G Empty Empty.elim) Id := fun q => q.data.elim
      let z := (ofExplained B (fun _ => id)).run M (fun _ => id) random game ⟨(), fun _ => [3, 5]⟩
      z.1.groups () = [2, 3, 6] ∧ z.2 () = [3, 5, 6, 0, 3, 6, 2] ∧
        (lookupMessage z.2 z.1).groups () = [6, 0, 2] := by
  dsimp only
  exact ⟨fun _ => Explained.valid_ofVectors _ _ _, by decide +kernel⟩

end GroupModel
