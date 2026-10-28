/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.GroupModel.ToExplained
import all VCVio.CryptoFoundations.GroupModel.Instances

/-! # Chronological source explanations for Type 3 pairing programs

The two source tables carry linear representations over received source elements. The target
table contains real values only. A pairing appends a target value without changing either
source basis. The interaction exchanges source elements and returns source explanations.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.Pairing

open Interaction

attribute [local implicit_reducible] PFam

variable {F T Input Query Result : Type} {G : Bool → Type} {Reply : Query → Type}

/-- A source tracking state and the real target table of a Type 3 computation. -/
abbrev Tracked (F : Type) (G : Bool → Type) (T : Type) := GroupModel.Tracked F G × List T

/-- Project a pairing handle message to its two source lists. -/
@[expose] def sourceMessage {Data : Type} (msg : Message Data (fun _ : PSort => Handle)) :
    Message Data (fun _ : Bool => Handle) :=
  ⟨msg.data, fun | false => msg.groups .g₁ | true => msg.groups .g₂⟩

/-- Embed source lists as a pairing message with an empty target list. -/
@[expose] def pairingMessage {Data : Type} (msg : Message Data G) :
    Message Data (PFam (G false) (G true) T) :=
  ⟨msg.data, fun | .g₁ => msg.groups false | .g₂ => msg.groups true | .gₜ => []⟩

/-- Source explanations and a real target table implement all Type 3 group operations. -/
@[expose] def step [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    (q : GroupModel.Query F pairingSig) (st : Tracked F G T) :
    (spec F pairingSig).Range q × Tracked F G T :=
  match q with
  | .add .g₁ a b =>
      let r := groupStep (.add false a b) st.1.2
      (r.1, (st.1.1, r.2), st.2)
  | .add .g₂ a b =>
      let r := groupStep (.add true a b) st.1.2
      (r.1, (st.1.1, r.2), st.2)
  | .smul .g₁ c a =>
      let r := groupStep (.smul false c a) st.1.2
      (r.1, (st.1.1, r.2), st.2)
  | .smul .g₂ c a =>
      let r := groupStep (.smul true c a) st.1.2
      (r.1, (st.1.1, r.2), st.2)
  | .eq .g₁ a b => (decide ((lookup st.1.2 false a).2 = (lookup st.1.2 false b).2), st)
  | .eq .g₂ a b => (decide ((lookup st.1.2 true a).2 = (lookup st.1.2 true b).2), st)
  | .add .gₜ a b => (st.2.length, st.1, st.2 ++ [st.2.getD a 0 + st.2.getD b 0])
  | .smul .gₜ c a => (st.2.length, st.1, st.2 ++ [c • st.2.getD a 0])
  | .eq .gₜ a b => (decide (st.2.getD a 0 = st.2.getD b 0), st)
  | .lin o _ => o.elim
  | .bil _ a b =>
      (st.2.length, st.1, st.2 ++ [e (lookup st.1.2 false a).2 (lookup st.1.2 true b).2])

/-- Every pairing group step preserves the source representation invariant. -/
theorem step_explains [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    (e : G false →ₗ[F] G true →ₗ[F] T) (q : GroupModel.Query F pairingSig)
    (st : Tracked F G T) (ht : Explains st.1.1 st.1.2) :
    Explains (step e q st).2.1.1 (step e q st).2.1.2 := by
  cases q with
  | add s a b => cases s with
    | g₁ => exact groupStep_inv (.add false a b) st.1 ht
    | g₂ => exact groupStep_inv (.add true a b) st.1 ht
    | gₜ => exact ht
  | smul s c a => cases s with
    | g₁ => exact groupStep_inv (.smul false c a) st.1 ht
    | g₂ => exact groupStep_inv (.smul true c a) st.1 ht
    | gₜ => exact ht
  | eq s a b => cases s <;> exact ht
  | lin o a => exact o.elim
  | bil o a b => exact ht

/-- Group operations do not change the chronological source basis. -/
theorem step_basis [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    (e : G false →ₗ[F] G true →ₗ[F] T) (q : GroupModel.Query F pairingSig)
    (st : Tracked F G T) (ht : Explains st.1.1 st.1.2) :
    basis (step e q st).2.1 = basis st.1 := by
  cases q with
  | add s a b => cases s with
    | g₁ => exact groupStep_basis (.add false a b) st.1 ht
    | g₂ => exact groupStep_basis (.add true a b) st.1 ht
    | gₜ => rfl
  | smul s c a => cases s with
    | g₁ => exact groupStep_basis (.smul false c a) st.1 ht
    | g₂ => exact groupStep_basis (.smul true c a) st.1 ht
    | gₜ => rfl
  | eq s a b => cases s <;> rfl
  | lin o a => exact o.elim
  | bil o a b => rfl

/-- The Type 3 handle signature with private coins and source-valued game replies. -/
abbrev HandleSpec (F Query : Type) (Reply : Query → Type) :=
  spec F pairingSig + (encSpec (fun _ : PSort => Unit) +
    (unifSpec + handleSpec (S := PSort) Query Reply))

/-- Translate a pairing handle computation into chronological source explanations.
Target handles affect equality and pairing computations but are absent from the explanations. -/
@[expose] def explainProgram [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    (program : OracleComp (HandleSpec F Query Reply) (Message Result (fun _ : PSort => Handle))) :
    Tracked F G T → OracleComp (explainedSpec F G (CoinQuery Query) (CoinReply Reply))
      (Explained F Result G) :=
  OracleComp.recOn program (fun msg st => pure (explain st.1 (sourceMessage msg)))
    (fun q _ next st => match q with
      | .inl q => next (step e q st).1 (step e q st).2
      | .inr (.inl _) => next () st
      | .inr (.inr (.inl n)) => do
          let reply ← (explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
            ⟨⟨.inr n, fun _ => []⟩, fun _ => []⟩
          next reply.data (receive st.1 reply.groups, st.2)
      | .inr (.inr (.inr q)) => do
          let reply ← (explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
            (explain st.1 (sourceMessage ⟨.inl q.data, q.groups⟩))
          next ⟨reply.data, fun
            | .g₁ => List.range' (st.1.2 false).length (reply.groups false).length
            | .g₂ => List.range' (st.1.2 true).length (reply.groups true).length
            | .gₜ => []⟩ (receive st.1 reply.groups, st.2))

/-- Every outgoing source element is explained on every reply path of the translated program. -/
theorem explainProgram_isAlgebraic [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    (program : OracleComp (HandleSpec F Query Reply) (Message Result (fun _ : PSort => Handle)))
    (st : Tracked F G T) (ht : Explains st.1.1 st.1.2) :
    IsAlgebraic (basis st.1) (explainProgram e program st) := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure msg => exact explain_valid ht _
  | query_bind q next ih =>
      rcases q with q | q | n | q
      · change IsAlgebraic (basis st.1)
          (explainProgram e (next (step e q st).1) (step e q st).2)
        rw [← step_basis e q st ht]
        exact ih _ _ (step_explains e q st ht)
      · exact ih () st ht
      · change IsAlgebraic (basis st.1) (liftM ((explainedSpec F G
          (CoinQuery Query) (CoinReply Reply)).query
            ⟨⟨.inr n, fun _ => []⟩, fun _ => []⟩) >>= _)
        apply (isAlgebraic_query _ _ _).mpr
        refine ⟨fun _ => .nil, ?_⟩
        intro reply
        rw [← receive_basis st.1 reply.groups ht]
        exact ih _ _ (receive_inv st.1 reply.groups ht)
      · change IsAlgebraic (basis st.1) (liftM ((explainedSpec F G
          (CoinQuery Query) (CoinReply Reply)).query
            (explain st.1 (sourceMessage ⟨.inl q.data, q.groups⟩))) >>= _)
        apply (isAlgebraic_query _ _ _).mpr
        refine ⟨explain_valid ht _, ?_⟩
        intro reply
        rw [← receive_basis st.1 reply.groups ht]
        exact ih _ _ (receive_inv st.1 reply.groups ht)

/-- Certify a Type 3 handle adversary using only its two chronological source bases. -/
@[expose] def toExplained [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    (A : HandleAdversary F pairingSig (fun _ => Unit) Input Query Reply Result) :
    Interaction.Adversary F G Input (CoinQuery Query) (CoinReply Reply) Result where
  main input := explainProgram e
    (A ⟨input.data, fun
      | .g₁ => List.range (input.groups false).length
      | .g₂ => List.range (input.groups true).length
      | .gₜ => []⟩)
    ((fun b => List.range (input.groups b).length, trackInputs input.groups), [])
  algebraic input := by
    simpa only [basis_initial] using explainProgram_isAlgebraic e _
      ((fun b => List.range (input.groups b).length, trackInputs input.groups), [])
      (explains_trackInputs input.groups)

/-! ## Exact real execution -/

/-- Forget representations while retaining the real target table. -/
@[expose] def table (st : Tracked F G T) : Tbl (PFam (G false) (G true) T)
  | .g₁ => (st.1.2 false).map Prod.snd
  | .g₂ => (st.1.2 true).map Prod.snd
  | .gₜ => st.2

/-- Read the source lists of a real pairing message. -/
@[expose] def sourceValue {Data : Type} (msg : Message Data (PFam (G false) (G true) T)) :
    Message Data G :=
  ⟨msg.data, fun | false => msg.groups .g₁ | true => msg.groups .g₂⟩

/-- Lift a source-valued game to the pairing interface with no target-group replies. -/
@[expose] def game {N : Type → Type} [Monad N]
    (impl : QueryImpl (plainSpec G Query Reply) N) :
    QueryImpl (plainSpec (PFam (G false) (G true) T) Query Reply) N :=
  fun q => pairingMessage <$> impl (sourceValue q)

/-- Receiving source elements appends precisely their real values to the pairing table. -/
theorem table_receive [Zero F] [One F]
    (st : Tracked F G T) (xs : Groups G) :
    table (receive st.1 xs, st.2) =
      (pushGroups (pairingMessage (T := T) ⟨(), xs⟩).groups (table st)).2 := by
  have h := receive_projection st.1 xs
  funext s
  cases s with
  | g₁ => exact congrFun h false
  | g₂ => exact congrFun h true
  | gₜ => simp only [table, pushGroups, pairingMessage, List.append_nil]

attribute [local implicit_reducible] spec handleSpec

/-- A real group query is the value projection of the full tracked pairing step. -/
theorem step_projection [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    {N : Type → Type} [Monad N] [LawfulMonad N]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    (q : GroupModel.Query F pairingSig) (st : Tracked F G T) :
    (impl (pairingReal e) (fun _ => id) N q).run (table st) =
      pure ((step e q st).1, table (step e q st).2) := by
  cases q with
  | lin o a => exact o.elim
  | add s a b =>
      cases s with
      | g₁ =>
          change (pure (((st.1.2 false).map Prod.snd).length,
            append (table st) .g₁ (lookup (mapTbl (fun _ => Prod.snd) st.1.2) false a +
              lookup (mapTbl (fun _ => Prod.snd) st.1.2) false b)) : N _) =
            pure ((st.1.2 false).length,
              table ((st.1.1, append st.1.2 false
                (lookup st.1.2 false a + lookup st.1.2 false b)), st.2))
          simp only [List.length_map, lookup_snd]
          congr 1
          apply Prod.ext
          · rfl
          · funext t
            cases t <;> simp [table, append, List.map_append]
      | g₂ =>
          change (pure (((st.1.2 true).map Prod.snd).length,
            append (table st) .g₂ (lookup (mapTbl (fun _ => Prod.snd) st.1.2) true a +
              lookup (mapTbl (fun _ => Prod.snd) st.1.2) true b)) : N _) =
            pure ((st.1.2 true).length,
              table ((st.1.1, append st.1.2 true
                (lookup st.1.2 true a + lookup st.1.2 true b)), st.2))
          simp only [List.length_map, lookup_snd]
          congr 1
          apply Prod.ext
          · rfl
          · funext t
            cases t <;> simp [table, append, List.map_append]
      | gₜ =>
          change (pure (st.2.length, append (table st) .gₜ (st.2.getD a 0 + st.2.getD b 0)) : N _) =
            pure (st.2.length, table (st.1, st.2 ++ [st.2.getD a 0 + st.2.getD b 0]))
          congr 1
          apply Prod.ext
          · rfl
          · funext t
            cases t <;> simp [table, append]
  | smul s c a =>
      cases s with
      | g₁ =>
          change (pure (((st.1.2 false).map Prod.snd).length,
            append (table st) .g₁
              (c • lookup (mapTbl (fun _ => Prod.snd) st.1.2) false a)) : N _) =
            pure ((st.1.2 false).length,
              table ((st.1.1, append st.1.2 false (c • (lookup st.1.2 false a))), st.2))
          simp only [List.length_map, lookup_snd]
          congr 1
          apply Prod.ext
          · rfl
          · funext t
            cases t <;> simp [table, append, List.map_append]
      | g₂ =>
          change (pure (((st.1.2 true).map Prod.snd).length,
            append (table st) .g₂
              (c • lookup (mapTbl (fun _ => Prod.snd) st.1.2) true a)) : N _) =
            pure ((st.1.2 true).length,
              table ((st.1.1, append st.1.2 true (c • (lookup st.1.2 true a))), st.2))
          simp only [List.length_map, lookup_snd]
          congr 1
          apply Prod.ext
          · rfl
          · funext t
            cases t <;> simp [table, append, List.map_append]
      | gₜ =>
          change (pure (st.2.length, append (table st) .gₜ (c • st.2.getD a 0)) : N _) =
            pure (st.2.length, table (st.1, st.2 ++ [c • st.2.getD a 0]))
          congr 1
          apply Prod.ext
          · rfl
          · funext t
            cases t <;> simp [table, append]
  | eq s a b =>
      simp only [impl, StateT.run_bind, StateT.run_get, pure_bind]
      cases s with
      | g₁ =>
          simp only [StateT.run_pure, step, id_eq]
          congr 1
          apply Prod.ext
          · apply decide_eq_decide.mpr
            change (lookup (mapTbl (fun _ => Prod.snd) st.1.2) false a =
              lookup (mapTbl (fun _ => Prod.snd) st.1.2) false b) ↔ _
            rw [lookup_snd, lookup_snd]
          · rfl
      | g₂ =>
          simp only [StateT.run_pure, step, id_eq]
          congr 1
          apply Prod.ext
          · apply decide_eq_decide.mpr
            change (lookup (mapTbl (fun _ => Prod.snd) st.1.2) true a =
              lookup (mapTbl (fun _ => Prod.snd) st.1.2) true b) ↔ _
            rw [lookup_snd, lookup_snd]
          · rfl
      | gₜ =>
          simp only [StateT.run_pure, step, id_eq]
          congr 1
          apply Prod.ext
          · exact decide_eq_decide.mpr Iff.rfl
          · rfl
  | bil o a b =>
      change (pure (st.2.length, append (table st) .gₜ
        (e (lookup (mapTbl (fun _ => Prod.snd) st.1.2) false a)
          (lookup (mapTbl (fun _ => Prod.snd) st.1.2) true b))) : N _) =
        pure (st.2.length, table (st.1,
          st.2 ++ [e (lookup st.1.2 false a).2 (lookup st.1.2 true b).2]))
      simp only [lookup_snd]
      congr 1
      apply Prod.ext
      · rfl
      · funext t
        cases t <;> simp [table, append]

private theorem explain_sourceValue [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [AddCommMonoid T]
    {Data : Type} (st : Tracked F G T) (msg : Message Data (fun _ : PSort => Handle)) :
    (explain st.1 (sourceMessage msg)).value = sourceValue (lookupMessage (table st) msg) := by
  rw [explain_value]
  dsimp only [lookupMessage, sourceMessage, sourceValue]
  congr 1
  funext b
  cases b <;> rfl

attribute [local implicit_reducible] sourceValue pairingMessage lookupMessage CoinReply

/-- Forgetting source explanations agrees exactly with running the handle computation in the
real pairing model, for arbitrary lawful randomness and source-game handlers. -/
theorem explainProgram_run [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    {N : Type → Type} [Monad N] [LawfulMonad N]
    (e : G false →ₗ[F] G true →ₗ[F] T) (random : QueryImpl unifSpec N)
    (handler : QueryImpl (plainSpec G Query Reply) N)
    (p : OracleComp (HandleSpec F Query Reply) (Message Result (fun _ : PSort => Handle)))
    (st : Tracked F G T) :
    Explained.value <$> simulateQ (fun q => withCoins random handler q.value)
      (explainProgram e p st) =
    (fun z => sourceValue (lookupMessage z.2 z.1)) <$>
      (simulateQ (impl (pairingReal e) (fun _ => id) N +
        (encImpl (V := PFam (G false) (G true) T)
          (m := N) (fun _ _ => ()) +
          (coinImpl (G := PFam (G false) (G true) T) random +
            liftGame (game (T := T) handler)))) p).run
          (table st) := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure msg =>
      change Explained.value <$> simulateQ _ (pure (explain st.1 (sourceMessage msg))) = _
      simp [explain_sourceValue]
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rcases q with q | q | n | q
      · change Explained.value <$> simulateQ _
          (explainProgram e (next (step e q st).1) (step e q st).2) = _
        rw [QueryImpl.add_apply_inl, step_projection, pure_bind]
        exact ih _ _
      · change Explained.value <$> simulateQ _ (explainProgram e (next ()) st) = _
        simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, encImpl, StateT.run,
          pure_bind]
        exact ih _ st
      · change Explained.value <$> simulateQ _ (liftM
          ((explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
            ⟨⟨.inr n, fun _ => []⟩, fun _ => []⟩) >>= fun reply =>
          explainProgram e (next reply.data) (receive st.1 reply.groups, st.2)) = _
        simp only [simulateQ_bind, simulateQ_spec_query, withCoins_apply_inr,
          QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
          map_bind, bind_assoc, pure_bind, receive_empty]
        rw [coinImpl_apply random n]
        simp only [bind_map_left]
        apply bind_congr
        intro coin
        exact ih coin st
      · change Explained.value <$> simulateQ _ (liftM
          ((explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
            (explain st.1 (sourceMessage ⟨.inl q.data, q.groups⟩))) >>= fun reply =>
          explainProgram e
            (next ⟨reply.data, fun
              | .g₁ => List.range' (st.1.2 false).length (reply.groups false).length
              | .g₂ => List.range' (st.1.2 true).length (reply.groups true).length
              | .gₜ => []⟩) (receive st.1 reply.groups, st.2)) = _
        simp only [simulateQ_bind, simulateQ_spec_query, explain, sourceMessage,
          QueryImpl.add_apply_inr, liftGame, StateT.run, game,
          bind_assoc, pure_bind, map_bind]
        simp only [withCoins_apply_inl]
        change (handler
          ⟨q.data, fun b => (sourceMessage q).groups b |>.map
            (fun h => (lookup st.1.2 b h).2)⟩ >>= fun reply : Message (Reply q.data) G =>
          Explained.value <$> simulateQ (fun q => withCoins random handler q.value)
            (explainProgram e
              (next ⟨reply.data, fun
                | .g₁ => List.range' (st.1.2 false).length (reply.groups false).length
                | .g₂ => List.range' (st.1.2 true).length (reply.groups true).length
                | .gₜ => []⟩) (receive st.1 reply.groups, st.2))) = _
        have hg : (sourceValue (lookupMessage (table st) q)).groups =
            (fun b => (sourceMessage q).groups b |>.map (fun h => (lookup st.1.2 b h).2)) := by
          funext b
          cases b <;> exact List.map_congr_left (fun h _ => lookup_snd st.1.2 _ h)
        simp only [bind_map_left]
        change _ = (handler ⟨q.data, (sourceValue (lookupMessage (table st) q)).groups⟩ >>= _)
        rw [hg]
        apply bind_congr
        intro reply
        have hh : (pushGroups (pairingMessage (T := T) reply).groups (table st)).1 =
            (fun | .g₁ => List.range' (st.1.2 false).length (reply.groups false).length
                 | .g₂ => List.range' (st.1.2 true).length (reply.groups true).length
                 | .gₜ => []) := by
          funext s
          cases s <;> simp [pushGroups, pairingMessage, table]
        dsimp only [pairingMessage] at hh
        simpa only [table_receive, StateT.run, pairingMessage, hh] using
          ih ⟨reply.data, fun
            | .g₁ => List.range' (st.1.2 false).length (reply.groups false).length
            | .g₂ => List.range' (st.1.2 true).length (reply.groups true).length
            | .gₜ => []⟩ (receive st.1 reply.groups, st.2)

/-- The certified source adversary has exactly the real pairing handle execution after
forgetting its explanations and chronological basis. -/
theorem toExplained_run [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    {N : Type → Type} [Monad N] [LawfulMonad N]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    (A : HandleAdversary F pairingSig (fun _ => Unit) Input Query Reply Result)
    (random : QueryImpl unifSpec N) (handler : QueryImpl (plainSpec G Query Reply) N)
    (input : Message Input G) :
    (fun z => z.1.value) <$> (toExplained e A).run (withCoins random handler) input =
      (fun z => sourceValue (lookupMessage z.2 z.1)) <$>
        A.run (pairingReal e) (fun _ _ => ()) random (game handler) (pairingMessage input) := by
  unfold Interaction.Adversary.run
  rw [run_value]
  change Explained.value <$> simulateQ _ (explainProgram e _ _) = _
  rw [explainProgram_run]
  have ht : table ((fun b => List.range (input.groups b).length,
      trackInputs (F := F) input.groups), ([] : List T)) =
      (pairingMessage (T := T) input).groups := by
    have hp := initial_projection (F := F) input.groups
    funext s
    cases s with
    | g₁ => exact congrFun hp false
    | g₂ => exact congrFun hp true
    | gₜ => rfl
  rw [ht]
  have hi : (⟨(pairingMessage (T := T) input).data,
      fun s => List.range ((pairingMessage (T := T) input).groups s).length⟩ :
      Message Input (fun _ : PSort => Handle)) =
      ⟨input.data, fun
        | .g₁ => List.range (input.groups false).length
        | .g₂ => List.range (input.groups true).length
        | .gₜ => []⟩ := by
    congr 1
    funext s
    cases s <;> rfl
  simp only [HandleAdversary.run, GroupModel.run, hi]

end GroupModel.Pairing
