/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Tracking
public import VCVio.CryptoFoundations.GroupModel.Coins

/-! # Certified explanations of handle computations

Tracking records coefficients over chronological receipts independently at each sort.
Private randomness is forwarded through the coin-bearing interaction interface.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

open Interaction

variable {S F Input Query Result : Type} {G E : S → Type} {Reply : Query → Type}

/-- The chronological received handles together with the representation table. -/
abbrev Tracked (F : Type) (G : S → Type) :=
  (S → List Handle) × Tbl (fun s => Repr F × G s)

/-- Read the chronological basis from a tracking state. -/
@[expose] def basis [Zero F] [∀ s, Zero (G s)] (st : Tracked F G) : Groups G :=
  fun s => (st.1 s).map fun h => (lookup st.2 s h).2

/-- Explain a message by restricting each representation to received handles. -/
@[expose] def explain [Zero F] [∀ s, Zero (G s)] {Data : Type}
    (st : Tracked F G) (msg : Message Data (fun _ : S => Handle)) : Explained F Data G :=
  ⟨⟨msg.data, fun s => (msg.groups s).map fun h => (lookup st.2 s h).2⟩,
    fun s => (msg.groups s).map fun h => (st.1 s).map (lookup st.2 s h).1⟩

private theorem evaluate_maps [CommSemiring F] {V : Type} [AddCommMonoid V] [Module F V]
    (hs : List Handle) (r : Handle → F) (v : Handle → V) :
    evaluate (hs.map r) (hs.map v) = (hs.map fun h => r h • v h).sum := by
  unfold evaluate
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < hs.length := by simpa using hj
    simp [hi']

/-- An explained message reconstructs from the chronological received basis. -/
theorem explain_valid [CommSemiring F]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    {st : Tracked F G} (ht : Explains st.1 st.2) {Data : Type}
    (msg : Message Data (fun _ : S => Handle)) : (explain st msg).Valid (basis st) := by
  intro s
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp [explain], ?_⟩
  intro i hi hj
  simp only [explain, List.get_eq_getElem, List.getElem_map, List.length_map, basis]
  refine ⟨trivial, ?_⟩
  rw [evaluate_maps]
  exact (ht.lookup_eq_sum_given s _).symm

/-- Install one sort's receipts in order, each at its fresh basis handle. -/
@[expose] def receiveAt [DecidableEq S] [Zero F] [One F]
    (s : S) (xs : List (G s)) (st : Tracked F G) : Tracked F G :=
  xs.foldl (fun st g =>
    (Function.update st.1 s (st.1 s ++ [(st.2 s).length]),
      append st.2 s (Pi.single (st.2 s).length 1, g))) st

private theorem receiveAt_inv [CommSemiring F] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    (s : S) (xs : List (G s)) (st : Tracked F G) (ht : Explains st.1 st.2) :
    Explains (receiveAt s xs st).1 (receiveAt s xs st).2 := by
  induction xs generalizing st with
  | nil => exact ht
  | cons g xs ih => exact ih _ (ht.pushGiven s g)

/-- Install all reply groups independently at their respective sorts. -/
@[expose] def receive [DecidableEq S] [Zero F] [One F]
    (st : Tracked F G) (xs : Groups G) : Tracked F G :=
  (fun s => (receiveAt s (xs s) st).1 s, fun s => (receiveAt s (xs s) st).2 s)

/-- Installing replies preserves the representation invariant. -/
theorem receive_inv [CommSemiring F] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    (st : Tracked F G) (xs : Groups G) (ht : Explains st.1 st.2) :
    Explains (receive st xs).1 (receive st xs).2 := by
  have hinv s := receiveAt_inv s (xs s) st ht
  constructor
  · intro s h hh
    exact (hinv s).given_lt s h hh
  · intro s h hh
    exact (hinv s).repr_given s h hh
  · intro s e he j hj
    exact (hinv s).support_subset s e he j hj
  · intro s e he
    exact (hinv s).eq_eval s e he
  · intro s
    exact (hinv s).given_nodup s

private theorem receiveAt_tables [Zero F] [One F] [DecidableEq S]
    (s : S) (xs : List (G s)) (st : Tracked F G) :
    (receiveAt s xs st).1 s = st.1 s ++ List.range' (st.2 s).length xs.length ∧
    (receiveAt s xs st).2 s = st.2 s ++
      xs.mapIdx (fun i g => (Pi.single ((st.2 s).length + i) 1, g)) := by
  induction xs using List.reverseRecOn with
  | nil => simp [receiveAt]
  | append_singleton xs g ih =>
      simp only [receiveAt, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Function.update_self, append] at *
      rw [ih.1, ih.2]
      simp [List.mapIdx_concat, List.range'_concat, List.append_assoc]

private theorem receive_tables [Zero F] [One F] [DecidableEq S]
    (st : Tracked F G) (xs : Groups G) :
    (receive st xs).1 = fun s => st.1 s ++ List.range' (st.2 s).length (xs s).length := by
  funext s
  exact (receiveAt_tables s (xs s) st).1

/-- Forgetting received representations installs the same real group replies. -/
theorem receive_projection [Zero F] [One F] [DecidableEq S]
    (st : Tracked F G) (xs : Groups G) :
    mapTbl (fun _ => Prod.snd) (receive st xs).2 =
      (pushGroups xs (mapTbl (fun _ => Prod.snd) st.2)).2 := by
  funext s
  change ((receiveAt s (xs s) st).2 s).map Prod.snd = _
  rw [(receiveAt_tables s (xs s) st).2]
  simp only [List.map_append, pushGroups, mapTbl]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Installing replies appends them to the chronological received basis. -/
theorem receive_basis [CommSemiring F] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    (st : Tracked F G) (xs : Groups G) (ht : Explains st.1 st.2) :
    basis (receive st xs) = extend (basis st) xs := by
  funext s
  simp only [basis, receive_tables, List.map_append, extend]
  have hp := congrFun (receive_projection st xs) s
  have hl (h : Handle) : (lookup (receive st xs).2 s h).2 =
      lookup (pushGroups xs (mapTbl (fun _ => Prod.snd) st.2)).2 s h := by
    change ((receive st xs).2 s |>.getD h 0).2 = _
    exact (List.getD_map (l := (receive st xs).2 s) (f := Prod.snd)
      (n := h) (d := 0)).symm.trans (congrArg (fun l => l.getD h 0) hp)
  simp only [hl]
  congr 1
  · apply List.map_congr_left
    intro h hh
    have hb := ht.given_lt s h hh
    simp only [pushGroups, mapTbl, lookup]
    rw [List.getD_append _ _ _ _ (by simpa using hb)]
    exact (List.getD_map (l := st.2 s) (f := Prod.snd) (n := h) (d := 0))
  · simpa [pushGroups, mapTbl] using
      lookup_pushGroups xs (mapTbl (fun _ => Prod.snd) st.2) s


/-- The four oracle components available to a handle computation. -/
abbrev HandleSpec (F S : Type) (E : S → Type) (Query : Type)
    (Reply : Query → Type) :=
  spec F (discreteSig S) + (encSpec E + (unifSpec + handleSpec (S := S) Query Reply))

/-- Answer a group query in the tracking model, observing equality on real values. -/
@[expose] def groupStep [CommSemiring F] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)] [∀ s, DecidableEq (G s)]
    (q : GroupModel.Query F (discreteSig S)) (tbl : Tbl (fun s => Repr F × G s)) :
    (spec F (discreteSig S)).Range q × Tbl (fun s => Repr F × G s) :=
  match q with
  | .add s a b => ((tbl s).length, append tbl s (lookup tbl s a + lookup tbl s b))
  | .smul s c a => ((tbl s).length, append tbl s (c • lookup tbl s a))
  | .eq s a b => (decide ((lookup tbl s a).2 = (lookup tbl s b).2), tbl)
  | .lin o _ => o.elim
  | .bil o _ _ => o.elim

/-- A discrete group step preserves the representation invariant. -/
theorem groupStep_inv [CommSemiring F] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)] [∀ s, DecidableEq (G s)]
    (q : GroupModel.Query F (discreteSig S)) (st : Tracked F G)
    (ht : Explains st.1 st.2) : Explains st.1 (groupStep q st.2).2 := by
  apply impl_tracking_preservesInv st.1 q st.2 ht (groupStep q st.2)
  cases q with
  | add s a b =>
      change (_, _) ∈ support (pure (_, _) : ProbComp _)
      simp only [support_pure, Set.mem_singleton_iff]
  | smul s c a =>
      change (_, _) ∈ support (pure (_, _) : ProbComp _)
      simp only [support_pure, Set.mem_singleton_iff]
  | eq s a b =>
      change (decide ((lookup st.2 s a).2 = (lookup st.2 s b).2), st.2) ∈
        support (pure (decide ((lookup st.2 s a).2 = (lookup st.2 s b).2), st.2) : ProbComp _)
      simp
  | lin o a => exact o.elim
  | bil o a b => exact o.elim

private theorem basis_append [CommSemiring F] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    (st : Tracked F G) (ht : Explains st.1 st.2) (s : S) (e : Repr F × G s) :
    basis (st.1, append st.2 s e) = basis st := by
  funext t
  apply List.map_congr_left
  intro h hh
  exact congrArg Prod.snd (lookup_append_old st.2 s e t h (ht.given_lt t h hh))

/-- A discrete group step leaves the chronological received basis unchanged. -/
theorem groupStep_basis [CommSemiring F] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)] [∀ s, DecidableEq (G s)]
    (q : GroupModel.Query F (discreteSig S)) (st : Tracked F G)
    (ht : Explains st.1 st.2) : basis (st.1, (groupStep q st.2).2) = basis st := by
  cases q with
  | add s a b => exact basis_append st ht s _
  | smul s c a => exact basis_append st ht s _
  | eq s a b => rfl
  | lin o a => exact o.elim
  | bil o a b => exact o.elim

/-- Simulate a handle computation while recording explanations over the received handles. -/
@[expose] def explainProgram [CommSemiring F] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)] [∀ s, DecidableEq (G s)]
    (enc : (s : S) → G s → E s)
    (program : OracleComp (HandleSpec F S E Query Reply)
      (Message Result (fun _ : S => Handle))) :
    (S → List Handle) × Tbl (fun s => Repr F × G s) →
      OracleComp (explainedSpec F G (CoinQuery Query) (CoinReply Reply))
        (Explained F Result G) :=
  OracleComp.recOn program (fun msg st => pure (explain st msg))
    (fun q _ next st => match q with
      | .inl q => next (groupStep q st.2).1 (st.1, (groupStep q st.2).2)
      | .inr (.inl q) => next (enc q.1 (lookup st.2 q.1 q.2).2) st
      | .inr (.inr (.inl n)) => do
          let reply ← (explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
            ⟨⟨.inr n, fun _ => []⟩, fun _ => []⟩
          next reply.data (receive st reply.groups)
      | .inr (.inr (.inr q)) => do
          let reply ← (explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
            (explain st ⟨.inl q.data, q.groups⟩)
          next ⟨reply.data, fun s => List.range' (st.2 s).length (reply.groups s).length⟩
            (receive st reply.groups))

/-- The tracking invariant certifies every outgoing request and final result along every path. -/
theorem explainProgram_isAlgebraic [CommSemiring F] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)] [∀ s, DecidableEq (G s)]
    (enc : (s : S) → G s → E s)
    (program : OracleComp (HandleSpec F S E Query Reply)
      (Message Result (fun _ : S => Handle)))
    (st : (S → List Handle) × Tbl (fun s => Repr F × G s))
    (ht : Explains st.1 st.2) :
    IsAlgebraic (fun s => (st.1 s).map fun h => (lookup st.2 s h).2)
      (explainProgram enc program st) := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure msg => exact explain_valid ht msg
  | query_bind q next ih =>
      rcases q with q | q | n | q
      · change IsAlgebraic (basis st)
          (explainProgram enc (next (groupStep q st.2).1) (st.1, (groupStep q st.2).2))
        rw [← groupStep_basis q st ht]
        exact ih _ _ (groupStep_inv q st ht)
      · exact ih _ st ht
      · change IsAlgebraic (basis st) (liftM ((explainedSpec F G
          (CoinQuery Query) (CoinReply Reply)).query
            ⟨⟨.inr n, fun _ => []⟩, fun _ => []⟩) >>= _)
        apply (isAlgebraic_query _ _ _).mpr
        refine ⟨fun _ => .nil, ?_⟩
        intro reply
        rw [← receive_basis st reply.groups ht]
        exact ih _ _ (receive_inv st reply.groups ht)
      · change IsAlgebraic (basis st) (liftM ((explainedSpec F G
          (CoinQuery Query) (CoinReply Reply)).query
            (explain st ⟨.inl q.data, q.groups⟩)) >>= _)
        apply (isAlgebraic_query _ _ _).mpr
        refine ⟨explain_valid ht _, ?_⟩
        intro reply
        rw [← receive_basis st reply.groups ht]
        exact ih _ _ (receive_inv st reply.groups ht)

/-- The initial chronological basis is exactly the supplied input lists. -/
theorem basis_initial [Zero F] [One F] [∀ s, Zero (G s)] (xs : Groups G) :
    basis (fun s => List.range (xs s).length, trackInputs (F := F) xs) = xs := by
  funext s
  apply List.ext_getElem
  · simp [basis]
  · intro i hi hj
    simp [basis, trackInputs, lookup, List.getD, hj]

/-- Turn a handle adversary into a certified adversary with chronological explanations. -/
@[expose] def toExplained [CommSemiring F] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)] [∀ s, DecidableEq (G s)]
    (A : HandleAdversary F (discreteSig S) E Input Query Reply Result)
    (enc : (s : S) → G s → E s) :
    Interaction.Adversary F G Input (CoinQuery Query) (CoinReply Reply) Result where
  main input := explainProgram enc
    (A ⟨input.data, fun s => List.range (input.groups s).length⟩)
    (fun s => List.range (input.groups s).length, trackInputs input.groups)
  algebraic input := by
    have h := explainProgram_isAlgebraic enc
      (A ⟨input.data, fun s => List.range (input.groups s).length⟩)
      (fun s => List.range (input.groups s).length, trackInputs input.groups)
      (explains_trackInputs input.groups)
    rwa [show (fun s => (List.range (input.groups s).length).map
      fun h => (lookup (trackInputs (F := F) input.groups) s h).2) = input.groups from
      basis_initial input.groups] at h


/-! ## Exact execution -/

/-- Looking up a projected table reads the real component of the tracked entry. -/
theorem lookup_snd [CommSemiring F]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    (tbl : Tbl (fun s => Repr F × G s)) (s : S) (h : Handle) :
    lookup (mapTbl (fun _ => Prod.snd) tbl) s h = (lookup tbl s h).2 :=
  lookup_mapTbl (fun s => LinearMap.snd F (Repr F) (G s)) tbl s h

/-- Forgetting a message explanation resolves its handles in the projected table. -/
theorem explain_value [CommSemiring F]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    (st : Tracked F G) {Data : Type} (msg : Message Data (fun _ : S => Handle)) :
    (explain st msg).value = lookupMessage (mapTbl (fun _ => Prod.snd) st.2) msg := by
  dsimp only [explain, lookupMessage]
  congr 1
  funext s
  exact List.map_congr_left (fun h _ => (lookup_snd st.2 s h).symm)

/-- Forgetting the initial representations recovers the input tables. -/
theorem initial_projection [Zero F] [One F] (xs : Groups G) :
    mapTbl (fun _ => Prod.snd) (trackInputs (F := F) xs) = xs := by
  funext s
  apply List.ext_getElem
  · simp [mapTbl, trackInputs]
  · intro i hi hj
    simp [mapTbl, trackInputs]

/-- Receiving empty lists at every sort leaves the tracking state unchanged. -/
theorem receive_empty [Zero F] [One F] [DecidableEq S] (st : Tracked F G) :
    receive st (fun _ => []) = st := rfl

/-- Forgetting explanations and the received basis commutes with the shared interaction run. -/
theorem run_value {N : Type → Type} [Monad N] [LawfulMonad N]
    (game : QueryImpl (plainSpec G Query Reply) N)
    (p : OracleComp (explainedSpec F G Query Reply) (Explained F Result G))
    (b : Groups G) :
    (fun z => z.1.value) <$> (simulateQ (fun q => StateT.mk fun basis => do
      let reply ← game q.value
      pure (reply, extend basis reply.groups)) p).run b =
      Explained.value <$> simulateQ (fun q => game q.value) p := by
  induction p using OracleComp.inductionOn generalizing b with
  | pure out => simp
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_mk,
        map_bind, bind_assoc, pure_bind]
      apply bind_congr
      intro reply
      exact ih reply _

private def valueHandler {N : Type → Type} [Monad N] (random : QueryImpl unifSpec N)
    (game : QueryImpl (plainSpec G Query Reply) N) :
    QueryImpl (explainedSpec F G (CoinQuery Query) (CoinReply Reply)) N :=
  fun q => withCoins random game q.value

private theorem valueHandler_coin {N : Type → Type} [Monad N] (random : QueryImpl unifSpec N)
    (game : QueryImpl (plainSpec G Query Reply) N) (n : ℕ)
    (groups : Groups G) (cs : S → List (List F)) :
    valueHandler random game ⟨⟨.inr n, groups⟩, cs⟩ =
      (do let coin ← random n; pure ⟨coin, fun _ => []⟩) := rfl

private theorem valueHandler_game {N : Type → Type} [Monad N] (random : QueryImpl unifSpec N)
    (game : QueryImpl (plainSpec G Query Reply) N) (q : Query)
    (groups : Groups G) (cs : S → List (List F)) :
    valueHandler random game ⟨⟨.inl q, groups⟩, cs⟩ = game ⟨q, groups⟩ := rfl

section Execution

variable [CommSemiring F] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)] [∀ s, DecidableEq (G s)]
    {N : Type → Type} [Monad N] [LawfulMonad N]

private theorem groupStep_projection (M : Model F (discreteSig S) G)
    (q : GroupModel.Query F (discreteSig S)) (tbl : Tbl (fun s => Repr F × G s)) :
    (impl M (fun _ => id) N q).run (mapTbl (fun _ => Prod.snd) tbl) =
      pure ((groupStep q tbl).1, mapTbl (fun _ => Prod.snd) (groupStep q tbl).2) := by
  cases q with
  | add s a b =>
      simp [groupStep, impl, push, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        StateT.run, mapTbl_append, lookup_snd, mapTbl]
      rfl
  | smul s c a =>
      simp [groupStep, impl, push, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        StateT.run, mapTbl_append, lookup_snd, mapTbl]
      rfl
  | eq s a b =>
      simp only [impl, StateT.run_bind, StateT.run_get, pure_bind, lookup_snd,
        groupStep, id_eq]
      rfl
  | lin o a => exact o.elim
  | bil o a b => exact o.elim

private theorem explainProgram_run (M : Model F (discreteSig S) G)
    (enc : (s : S) → G s → E s) (random : QueryImpl unifSpec N)
    (game : QueryImpl (plainSpec G Query Reply) N)
    (p : OracleComp (HandleSpec F S E Query Reply) (Message Result (fun _ : S => Handle)))
    (st : Tracked F G) :
    Explained.value <$> simulateQ (valueHandler random game)
      (explainProgram enc p st) =
    (fun z => lookupMessage z.2 z.1) <$>
      (simulateQ (impl M (fun _ => id) N +
        (encImpl (m := N) enc + (coinImpl (G := G) random + liftGame game))) p).run
          (mapTbl (fun _ => Prod.snd) st.2) := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure msg =>
      change Explained.value <$> simulateQ _ (pure (explain st msg)) = _
      simp [explain_value]
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rcases q with q | q | n | q
      · change Explained.value <$> simulateQ _
          (explainProgram enc (next (groupStep q st.2).1) (st.1, (groupStep q st.2).2)) = _
        rw [QueryImpl.add_apply_inl, groupStep_projection M, pure_bind]
        exact ih _ _
      · change Explained.value <$> simulateQ _
          (explainProgram enc (next (enc q.1 (lookup st.2 q.1 q.2).2)) st) = _
        simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, encImpl, StateT.run,
          lookup_snd, pure_bind]
        exact ih _ st
      · change Explained.value <$> simulateQ _ (liftM
          ((explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
            ⟨⟨.inr n, fun _ => []⟩, fun _ => []⟩) >>= fun reply =>
          explainProgram enc (next reply.data) (receive st reply.groups)) = _
        simp only [simulateQ_bind, simulateQ_spec_query, valueHandler_coin,
          QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
          map_bind, bind_assoc, pure_bind, receive_empty]
        rw [coinImpl_apply random n]
        simp only [bind_map_left]
        apply bind_congr
        intro coin
        exact ih coin st
      · change Message (Reply q.data) (fun _ : S => Handle) →
          OracleComp (HandleSpec F S E Query Reply) (Message Result (fun _ : S => Handle)) at next
        change Explained.value <$> simulateQ _ (liftM
          ((explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
            (explain st ⟨.inl q.data, q.groups⟩)) >>= fun reply =>
          explainProgram enc
            (next ⟨reply.data, fun s => List.range' (st.2 s).length (reply.groups s).length⟩)
            (receive st reply.groups)) = _
        simp only [simulateQ_bind, simulateQ_spec_query, explain, lookupMessage,
          valueHandler_game, QueryImpl.add_apply_inr, liftGame, StateT.run,
          bind_assoc, pure_bind]
        change (Explained.value <$> (game
          ⟨q.data, fun s => (q.groups s).map (fun h => (lookup st.2 s h).2)⟩ >>=
          fun reply : Message (Reply q.data) G =>
            simulateQ (valueHandler random game)
              (explainProgram enc
                (next ⟨reply.data, fun s => List.range' (st.2 s).length (reply.groups s).length⟩)
                (receive st reply.groups)))) = _
        simp only [map_bind]
        have hg : (fun s => (q.groups s).map (lookup (mapTbl (fun _ => Prod.snd) st.2) s)) =
            (fun s => (q.groups s).map (fun h => (lookup st.2 s h).2)) := by
          funext s
          exact List.map_congr_left (fun h _ => lookup_snd st.2 s h)
        rw [hg]
        apply bind_congr
        intro reply
        simpa only [receive_projection, pushGroups, mapTbl, List.length_map, lookupMessage,
          StateT.run] using
          ih ⟨reply.data, fun s => List.range' (st.2 s).length (reply.groups s).length⟩
            (receive st reply.groups)

/-- Forgetting explanations gives exactly the handle run read back through its final table,
including the effects of the shared random and game handlers in any lawful monad. -/
theorem toExplained_run
    (A : HandleAdversary F (discreteSig S) E Input Query Reply Result)
    (M : Model F (discreteSig S) G) (enc : (s : S) → G s → E s)
    (random : QueryImpl unifSpec N) (game : QueryImpl (plainSpec G Query Reply) N)
    (input : Message Input G) :
    (fun z => z.1.value) <$> (toExplained A enc).run (withCoins random game) input =
      (fun z => lookupMessage z.2 z.1) <$> A.run M enc random game input := by
  unfold Adversary.run
  rw [run_value]
  change Explained.value <$> simulateQ (valueHandler random game) (explainProgram enc _ _) = _
  rw [explainProgram_run M]
  simp only [initial_projection, HandleAdversary.run, GroupModel.run]

end Execution

end GroupModel
