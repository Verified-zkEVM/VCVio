/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.GroupModel.PairingExplained

/-! # Pairing execution retaining chronological explanations

A stateful interpretation retains the representation table throughout execution. Its final
explanation equals the translated adversary's entire output, including coefficient lists.
This equality supports reductions which extract scalars from those coefficients.
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

/-- Interpret pairing handles while retaining the full source representation tables. -/
@[expose] def trackedImpl [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    {N : Type → Type} [Monad N]
    (e : G false →ₗ[F] G true →ₗ[F] T) (random : QueryImpl unifSpec N)
    (handler : QueryImpl (plainSpec G Query Reply) N) :
    QueryImpl (HandleSpec F Query Reply) (StateT (Tracked F G T) N)
  | .inl q => fun st => pure (step e q st)
  | .inr (.inl _) => fun st => pure ((), st)
  | .inr (.inr (.inl n)) => fun st => do
      let answer ← random n
      return (answer, st)
  | .inr (.inr (.inr q)) => fun st => do
      let reply ← handler (explain st.1 (sourceMessage q)).value
      return (⟨reply.data, fun
        | .g₁ => List.range' (st.1.2 false).length (reply.groups false).length
        | .g₂ => List.range' (st.1.2 true).length (reply.groups true).length
        | .gₜ => []⟩, (receive st.1 reply.groups, st.2))

/-- Real tracked execution preserves the entire explained output, including its coefficients. -/
theorem explainProgram_run_tracked [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    {N : Type → Type} [Monad N] [LawfulMonad N]
    (e : G false →ₗ[F] G true →ₗ[F] T) (random : QueryImpl unifSpec N)
    (handler : QueryImpl (plainSpec G Query Reply) N)
    (program : OracleComp (HandleSpec F Query Reply)
      (Message Result (fun _ : PSort => Handle))) (st : Tracked F G T) :
    simulateQ (fun q => withCoins random handler q.value) (explainProgram e program st) =
      (fun z => explain z.2.1 (sourceMessage z.1)) <$>
        (simulateQ (trackedImpl e random handler) program).run st := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure msg =>
      change simulateQ _ (pure (explain st.1 (sourceMessage msg))) = _
      simp
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rcases q with q | q | n | q
      · change simulateQ _
          (explainProgram e (next (step e q st).1) (step e q st).2) = _
        simp only [trackedImpl, StateT.run, pure_bind]
        exact ih _ _
      · change simulateQ _ (explainProgram e (next ()) st) = _
        simp only [trackedImpl, StateT.run, pure_bind]
        exact ih _ st
      · change simulateQ _ (liftM
          ((explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
            ⟨⟨.inr n, fun _ => []⟩, fun _ => []⟩) >>= fun reply =>
          explainProgram e (next reply.data) (receive st.1 reply.groups, st.2)) = _
        simp only [simulateQ_bind, simulateQ_spec_query, withCoins_apply_inr,
          trackedImpl, StateT.run, bind_assoc, pure_bind, receive_empty]
        apply bind_congr
        intro coin
        exact ih coin st
      · change simulateQ _ (liftM
          ((explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
            (explain st.1 (sourceMessage ⟨.inl q.data, q.groups⟩))) >>= fun reply =>
          explainProgram e
            (next ⟨reply.data, fun
              | .g₁ => List.range' (st.1.2 false).length (reply.groups false).length
              | .g₂ => List.range' (st.1.2 true).length (reply.groups true).length
              | .gₜ => []⟩) (receive st.1 reply.groups, st.2)) = _
        simp only [simulateQ_bind, simulateQ_spec_query, explain, sourceMessage,
          trackedImpl, StateT.run, bind_assoc, pure_bind, withCoins_apply_inl]
        apply bind_congr
        intro reply
        exact ih _ (receive st.1 reply.groups, st.2)

end GroupModel.Pairing
