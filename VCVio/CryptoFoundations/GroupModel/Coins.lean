/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Game

/-!
Private coins in explained interactions

Coin requests share the explicit randomness handler with handle computations. Their replies
contain no group elements, so they leave the chronological received basis unchanged.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

open Interaction

/-- Ordinary requests together with finite uniform sampling requests. -/
abbrev CoinQuery (Query : Type) := Query ⊕ ℕ

/-- Ordinary replies and the finite answer type of the uniform sampling oracle. -/
@[expose] def CoinReply {Query : Type} (Reply : Query → Type) : CoinQuery Query → Type :=
  Sum.elim Reply (fun n => Fin (n + 1))

/-- Add private coins to an element-valued game, ignoring the coin request's group arguments. -/
@[expose] def withCoins {S Query : Type} {G : S → Type} {Reply : Query → Type}
    {N : Type → Type} [Monad N] (random : QueryImpl unifSpec N)
    (impl : QueryImpl (plainSpec G Query Reply) N) :
    QueryImpl (plainSpec G (CoinQuery Query) (CoinReply Reply)) N
  | ⟨.inl q, groups⟩ => impl ⟨q, groups⟩
  | ⟨.inr n, _⟩ => do
      let answer ← random n
      pure ⟨answer, fun _ => []⟩

/-- Ordinary requests are forwarded with their group arguments. -/
@[simp] theorem withCoins_apply_inl {S Query : Type} {G : S → Type} {Reply : Query → Type}
    {N : Type → Type} [Monad N] (random : QueryImpl unifSpec N)
    (impl : QueryImpl (plainSpec G Query Reply) N) (q : Query) (groups : Groups G) :
    withCoins random impl ⟨.inl q, groups⟩ = impl ⟨q, groups⟩ := rfl

/-- Coin requests return no group elements. -/
@[simp] theorem withCoins_apply_inr {S Query : Type} {G : S → Type} {Reply : Query → Type}
    {N : Type → Type} [Monad N] (random : QueryImpl unifSpec N)
    (impl : QueryImpl (plainSpec G Query Reply) N) (n : ℕ) (groups : Groups G) :
    withCoins random impl ⟨.inr n, groups⟩ =
      (do let answer ← random n; pure ⟨answer, fun _ => []⟩) := rfl

end GroupModel
