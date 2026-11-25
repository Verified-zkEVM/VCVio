/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.GroupModel.PairingExplained

/-! # Pairing execution retaining chronological explanations

Unfolding equations for the explanation program of a pairing handle adversary: a returned
message reads its chronological source explanation, and each handle query is executed against
the source tracker before the program continues.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.Pairing

open Interaction

variable {F T Query Result : Type} {G : Bool → Type} {Reply : Query → Type}

attribute [local implicit_reducible] spec handleSpec

/-- Translation of a returned handle message reads its chronological source explanation. -/
theorem explainProgram_pure [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    (out : Message Result (fun _ : PSort => Handle)) (st : Tracked F G T) :
    explainProgram (Query := Query) (Reply := Reply) e (pure out) st =
      pure (explain st.1 (sourceMessage out)) := rfl

/-- Translation executes one handle query and continues with the updated source tracker. -/
theorem explainProgram_query_bind [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    (q : (HandleSpec F Query Reply).Domain)
    (next : (HandleSpec F Query Reply).Range q →
      OracleComp (HandleSpec F Query Reply) (Message Result (fun _ : PSort => Handle)))
    (st : Tracked F G T) :
    explainProgram e (liftM ((HandleSpec F Query Reply).query q) >>= next) st =
      (match q, next with
      | .inl q, next => explainProgram e (next (step e q st).1) (step e q st).2
      | .inr (.inl _), next => explainProgram e (next ()) st
      | .inr (.inr (.inl n)), next => do
          let reply ← (explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
            ⟨⟨.inr n, fun _ => []⟩, fun _ => []⟩
          explainProgram e (next reply.data) (receive st.1 reply.groups, st.2)
      | .inr (.inr (.inr q)), next => do
          let reply ← (explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
            (explain st.1 (sourceMessage ⟨.inl q.data, q.groups⟩))
          explainProgram e (next ⟨reply.data, fun
            | .g₁ => List.range' (st.1.2 false).length (reply.groups false).length
            | .g₂ => List.range' (st.1.2 true).length (reply.groups true).length
            | .gₜ => []⟩) (receive st.1 reply.groups, st.2)) := by
  cases q with
  | inl q => rfl
  | inr q => rcases q with q | n | q <;> rfl

end GroupModel.Pairing
