/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Coins

/-!
Realizing certified explanations with handles

The received-handle invariant includes bounds as well as read-back equality. Bounds ensure
that appending to a table preserves the meaning of every received handle.

Sortwise computations use `Finset.univ.toList` from the supplied `Fintype` instance. This fixed
finite enumeration sequences encoding and group queries, including for dependent group types.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

open Interaction


variable {S F Input Query Result : Type} {G E : S → Type} {Reply : Query → Type}

/-- Every received handle is in range and reads back to the corresponding chronological input. -/
@[expose] def Received [∀ s, Zero (G s)] (tbl : Tbl G)
    (handles : Groups (fun _ : S => Handle)) (basis : Groups G) : Prop :=
  ∀ s, List.Forall₂ (fun h g => h < (tbl s).length ∧ lookup tbl s h = g)
    (handles s) (basis s)

/-- The received-handle invariant identifies the entire read-back basis. -/
theorem Received.readback [∀ s, Zero (G s)] {tbl : Tbl G}
    {handles : Groups (fun _ : S => Handle)} {basis : Groups G}
    (h : Received tbl handles basis) :
    (fun s => (handles s).map (lookup tbl s)) = basis := by
  funext s
  have hh := h s
  generalize handles s = hs at hh ⊢
  generalize basis s = gs at hh ⊢
  induction hh with
  | nil => rfl
  | cons _ _ ih => simp_all

/-- The initial range handles satisfy the received-handle invariant. -/
theorem received_initial [∀ s, Zero (G s)] (basis : Groups G) :
    Received basis (fun s => List.range (basis s).length) basis := by
  intro s
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp, ?_⟩
  intro i hi hj
  simp [lookup, List.getD, hj]

private def Extends (tbl tbl' : Tbl G) : Prop := ∀ s, (tbl s).IsPrefix (tbl' s)

private theorem extends_refl (tbl : Tbl G) : Extends tbl tbl := fun _ => ⟨[], by simp⟩

private theorem extends_trans {a b c : Tbl G} (hab : Extends a b) (hbc : Extends b c) :
    Extends a c := fun s => (hab s).trans (hbc s)

private theorem lookup_extends [∀ s, Zero (G s)] {tbl tbl' : Tbl G}
    (he : Extends tbl tbl') (s : S) (h : Handle) (hh : h < (tbl s).length) :
    h < (tbl' s).length ∧ lookup tbl' s h = lookup tbl s h := by
  obtain ⟨tail, ht⟩ := he s
  constructor
  · exact lt_of_lt_of_le hh (he s).length_le
  · simp [lookup, ← ht, List.getD_eq_getElem?_getD, List.getElem?_append_left hh]

private theorem received_extends [∀ s, Zero (G s)] {tbl tbl' : Tbl G}
    {handles : Groups (fun _ : S => Handle)} {basis : Groups G}
    (h : Received tbl handles basis) (he : Extends tbl tbl') : Received tbl' handles basis := by
  intro s
  exact (h s).imp fun _ _ hh =>
    ⟨(lookup_extends he s _ hh.1).1, (lookup_extends he s _ hh.1).2.trans hh.2⟩

/-- Installing a game reply extends the received basis and preserves all previous receipts. -/
theorem received_pushGroups [∀ s, Zero (G s)] {tbl : Tbl G}
    {handles : Groups (fun _ : S => Handle)} {basis : Groups G}
    (h : Received tbl handles basis) (reply : Groups G) :
    Received (pushGroups reply tbl).2 (extend handles (pushGroups reply tbl).1)
      (extend basis reply) := by
  have he : Extends tbl (pushGroups reply tbl).2 := fun s => ⟨reply s, rfl⟩
  intro s
  apply List.rel_append (received_extends h he s)
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp [pushGroups], ?_⟩
  intro i hi hj
  simp [pushGroups, lookup, List.getD, hj]

private theorem extends_append [DecidableEq S] (tbl : Tbl G) (s : S) (g : G s) :
    Extends tbl (append tbl s g) := by
  intro t
  by_cases ht : t = s
  · subst t
    exact ⟨[g], by simp [append]⟩
  · exact ⟨[], by simp [append, Function.update_of_ne ht]⟩

private theorem lookup_append_self [DecidableEq S] [∀ s, Zero (G s)]
    (tbl : Tbl G) (s : S) (g : G s) :
    (tbl s).length < (append tbl s g s).length ∧
      lookup (append tbl s g) s (tbl s).length = g := by
  simp [append, lookup, List.getD]

/-! ## Compilation -/

private abbrev Target (F : Type) (S : Type) (E : S → Type) (Query : Type)
    (Reply : Query → Type) :=
  spec F (discreteSig S) + (encSpec E + (unifSpec + handleSpec (S := S) Query Reply))

private def smulQ (s : S) (c : F) (h : Handle) :
    OracleComp (Target F S E Query Reply) Handle :=
  (Target F S E Query Reply).query (.inl (.smul s c h))

private def addQ (s : S) (a b : Handle) : OracleComp (Target F S E Query Reply) Handle :=
  (Target F S E Query Reply).query (.inl (.add s a b))

private def encodingQ (s : S) (h : Handle) : OracleComp (Target F S E Query Reply) (E s) :=
  (Target F S E Query Reply).query (.inr (.inl (s, h)))

private def coinQ (n : ℕ) : OracleComp (Target F S E Query Reply) (Fin (n + 1)) :=
  (Target F S E Query Reply).query (.inr (.inr (.inl n)))

private def gameQ (q : Message Query (fun _ : S => Handle)) :
    OracleComp (Target F S E Query Reply) (Message (Reply q.data) (fun _ : S => Handle)) :=
  (Target F S E Query Reply).query (.inr (.inr (.inr q)))

private def sortMap [DecidableEq S] {m : Type → Type} [Monad m] {A : S → Type}
    (f : (s : S) → m (List (A s))) : List S → m ((s : S) → List (A s))
  | [] => pure (fun _ => [])
  | s :: ss => do
      let xs ← f s
      let rest ← sortMap f ss
      pure (Function.update rest s xs)

private noncomputable def decodeGroups [Fintype S] [DecidableEq S] (dec : (s : S) → E s → G s)
    (handles : Groups (fun _ : S => Handle)) : OracleComp (Target F S E Query Reply) (Groups G) :=
  sortMap (fun s => (handles s).mapM fun h => do
    let e ← encodingQ s h
    pure (dec s e)) Finset.univ.toList

private noncomputable def buildVectorAux [Zero F] (s : S) : List F → List Handle →
    OracleComp (Target F S E Query Reply) (Option Handle) := by
  classical
  exact fun cs hs => match cs, hs with
    | c :: cs, h :: hs =>
        if c = 0 then buildVectorAux s cs hs else do
          let a ← smulQ s c h
          let rest ← buildVectorAux s cs hs
          match rest with
          | none => pure (some a)
          | some b => do
              let sum ← addQ s a b
              pure (some sum)
    | _, _ => pure none

private noncomputable def buildVector [Zero F] (s : S) (cs : List F) (hs : List Handle) :
    OracleComp (Target F S E Query Reply) Handle := do
  let result ← buildVectorAux s cs hs
  match result with
  | some h => pure h
  | none => smulQ s 0 0

private noncomputable def buildMessage [Zero F] [Fintype S] [DecidableEq S] {Data : Type}
    (handles : Groups (fun _ : S => Handle)) (out : Explained F Data G) :
    OracleComp (Target F S E Query Reply) (Message Data (fun _ : S => Handle)) := do
  let groups ← sortMap (fun s => (out.coefficients s).mapM fun cs =>
    buildVector s cs (handles s)) Finset.univ.toList
  pure ⟨out.value.data, groups⟩

private noncomputable def compile [Zero F] [Fintype S] [DecidableEq S]
    (dec : (s : S) → E s → G s)
    (program : OracleComp (explainedSpec F G (CoinQuery Query) (CoinReply Reply))
      (Explained F Result G)) :
    Groups (fun _ : S => Handle) →
      OracleComp (Target F S E Query Reply) (Message Result (fun _ : S => Handle)) :=
  OracleComp.recOn program (fun out handles => buildMessage handles out)
    (fun q _ next handles =>
      Sum.rec (motive := fun data =>
          (Message (CoinReply Reply data) G → Groups (fun _ : S => Handle) →
            OracleComp (Target F S E Query Reply) (Message Result (fun _ : S => Handle))) →
          OracleComp (Target F S E Query Reply) (Message Result (fun _ : S => Handle)))
        (fun query next => do
          let outgoing ← buildMessage handles q
          let reply ← gameQ ⟨query, outgoing.groups⟩
          let groups ← decodeGroups dec reply.groups
          next ⟨reply.data, groups⟩ (extend handles reply.groups))
        (fun n next => do
          let coin ← coinQ n
          next ⟨coin, fun _ => []⟩ handles)
        q.value.data next)

private theorem compile_pure [Zero F] [Fintype S] [DecidableEq S]
    (dec : (s : S) → E s → G s) (out : Explained F Result G)
    (hs : Groups (fun _ : S => Handle)) :
    compile (Query := Query) (Reply := Reply) dec (pure out) hs = buildMessage hs out := rfl

private theorem compile_coin [Zero F] [Fintype S] [DecidableEq S]
    (dec : (s : S) → E s → G s) (n : ℕ) (groups : Groups G)
    (coefficients : S → List (List F))
    (next : Message (Fin (n + 1)) G → OracleComp
      (explainedSpec F G (CoinQuery Query) (CoinReply Reply)) (Explained F Result G))
    (hs : Groups (fun _ : S => Handle)) :
    compile dec (liftM ((explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
      ⟨⟨.inr n, groups⟩, coefficients⟩) >>= next) hs = (do
        let coin ← coinQ n
        compile dec (next ⟨coin, fun _ => []⟩) hs) := rfl

private theorem compile_request [Zero F] [Fintype S] [DecidableEq S]
    (dec : (s : S) → E s → G s) (q : Query) (groups : Groups G)
    (coefficients : S → List (List F))
    (next : Message (Reply q) G → OracleComp
      (explainedSpec F G (CoinQuery Query) (CoinReply Reply)) (Explained F Result G))
    (hs : Groups (fun _ : S => Handle)) :
    compile dec (liftM ((explainedSpec F G (CoinQuery Query) (CoinReply Reply)).query
      ⟨⟨.inl q, groups⟩, coefficients⟩) >>= next) hs = (do
        let outgoing ← buildMessage hs (⟨⟨.inl q, groups⟩, coefficients⟩ :
          Explained F (CoinQuery Query) G)
        let reply ← gameQ ⟨q, outgoing.groups⟩
        let groups ← decodeGroups dec reply.groups
        compile dec (next ⟨reply.data, groups⟩) (extend hs reply.groups)) := rfl

/-- Realize certified explanations with module operations on received handles.

Encoding queries recover received values, private coins use `unifSpec`, and each nonzero
coefficient uses one scalar multiplication and at most one addition. An all-zero vector uses
one multiplication by zero. The sort order is the supplied `Fintype` enumeration. -/
noncomputable def ofExplained [Zero F] [∀ s, AddMonoid (G s)]
    [∀ s, SMul F (G s)] [Fintype S] [DecidableEq S]
    (B : Interaction.Adversary F G Input (CoinQuery Query) (CoinReply Reply) Result)
    (dec : (s : S) → E s → G s) :
    HandleAdversary F (discreteSig S) E Input Query Reply Result := fun input => do
  let groups ← decodeGroups dec input.groups
  compile dec (B.main ⟨input.data, groups⟩) input.groups

/-! ## Table semantics of compilation -/

private theorem evaluate_cons {s : S} [CommSemiring F]
    [AddCommMonoid (G s)] [Module F (G s)] (c : F) (cs : List F) (g : G s) (gs : List (G s)) :
    evaluate (c :: cs) (g :: gs) = c • g + evaluate cs gs := by
  simp [evaluate]

private theorem list_received_extends [∀ s, Zero (G s)] {tbl tbl' : Tbl G}
    (he : Extends tbl tbl') (s : S) {hs : List Handle} {gs : List (G s)}
    (h : List.Forall₂ (fun h g => h < (tbl s).length ∧ lookup tbl s h = g) hs gs) :
    List.Forall₂ (fun h g => h < (tbl' s).length ∧ lookup tbl' s h = g) hs gs :=
  h.imp fun _ _ hh =>
    ⟨(lookup_extends he s _ hh.1).1, (lookup_extends he s _ hh.1).2.trans hh.2⟩

private abbrev certifiedHandler {N : Type → Type} [Monad N]
    (random : QueryImpl unifSpec N) (game : QueryImpl (plainSpec G Query Reply) N) :
    QueryImpl (explainedSpec F G (CoinQuery Query) (CoinReply Reply)) (StateT (Groups G) N) :=
  fun q basis => do
    let reply ← withCoins random game q.value
    pure (reply, extend basis reply.groups)

private theorem run_certified {N : Type → Type} [Monad N]
    (random : QueryImpl unifSpec N) (game : QueryImpl (plainSpec G Query Reply) N)
    (q : Explained F (CoinQuery Query) G) (basis : Groups G) :
    (certifiedHandler random game q).run basis = (do
      let reply ← withCoins random game q.value
      pure (reply, extend basis reply.groups)) := rfl

section Semantics

variable [CommSemiring F] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)] [∀ s, DecidableEq (G s)]
    {N : Type → Type} [Monad N] [LawfulMonad N]
    (M : Model F (discreteSig S) G) (enc : (s : S) → G s → E s)
    (random : QueryImpl unifSpec N) (game : QueryImpl (plainSpec G Query Reply) N)

private abbrev handler : QueryImpl (Target F S E Query Reply) (StateT (Tbl G) N) :=
  impl M (fun _ => id) N + (encImpl (m := N) enc + (coinImpl (G := G) random + liftGame game))

private theorem run_smul (s : S) (c : F) (h : Handle) (tbl : Tbl G) :
    (simulateQ (handler M enc random game)
      (smulQ s c h)).run tbl =
      pure ((tbl s).length, append tbl s (c • lookup tbl s h)) := by
  exact congrArg (fun st : StateT (Tbl G) N Handle => st.run tbl)
    (simulateQ_spec_query (handler M enc random game) (.inl (.smul s c h)))

private theorem run_add (s : S) (a b : Handle) (tbl : Tbl G) :
    (simulateQ (handler M enc random game)
      (addQ s a b)).run tbl =
      pure ((tbl s).length, append tbl s (lookup tbl s a + lookup tbl s b)) := by
  exact congrArg (fun st : StateT (Tbl G) N Handle => st.run tbl)
    (simulateQ_spec_query (handler M enc random game) (.inl (.add s a b)))

private theorem run_coin (n : ℕ) (tbl : Tbl G) :
    (simulateQ (handler M enc random game) (coinQ n)).run tbl =
      (fun x => (x, tbl)) <$> random n := by
  unfold coinQ
  rw [simulateQ_spec_query]
  exact coinImpl_apply random n tbl

private theorem run_game (q : Message Query (fun _ : S => Handle)) (tbl : Tbl G) :
    (simulateQ (handler M enc random game) (gameQ q)).run tbl = (do
      let reply ← game (lookupMessage tbl q)
      pure (⟨reply.data, (pushGroups reply.groups tbl).1⟩,
        (pushGroups reply.groups tbl).2)) := by
  exact congrArg (fun st : StateT (Tbl G) N (Message (Reply q.data) (fun _ : S => Handle)) =>
    st.run tbl) (simulateQ_spec_query (handler M enc random game) (.inr (.inr (.inr q))))

private theorem run_buildVectorAux (s : S) (cs : List F) (hs : List Handle)
    (gs : List (G s)) (tbl : Tbl G)
    (hr : List.Forall₂ (fun h g => h < (tbl s).length ∧ lookup tbl s h = g) hs gs)
    (hlen : cs.length = gs.length) :
    ∃ opt tbl',
      (simulateQ (handler M enc random game) (buildVectorAux s cs hs)).run tbl =
        pure (opt, tbl') ∧ Extends tbl tbl' ∧
      match opt with
      | none => evaluate cs gs = 0
      | some h => h < (tbl' s).length ∧ lookup tbl' s h = evaluate cs gs := by
  induction cs generalizing hs gs tbl with
  | nil =>
      have hg : gs = [] := List.length_eq_zero_iff.mp hlen.symm
      subst gs
      cases hr
      exact ⟨none, tbl, by simp [buildVectorAux], extends_refl tbl, by simp [evaluate]⟩
  | cons c cs ih =>
      cases hr with
      | nil => simp at hlen
      | @cons h g hs gs hh ht =>
          have hl : cs.length = gs.length := Nat.succ.inj hlen
          by_cases hc : c = 0
          · obtain ⟨opt, tbl', hrun, he, hv⟩ := ih hs gs tbl ht hl
            refine ⟨opt, tbl', ?_, he, ?_⟩
            · simpa [buildVectorAux, hc] using hrun
            · simpa [evaluate_cons, hc] using hv
          · let tbl₁ := append tbl s (c • lookup tbl s h)
            have he₁ : Extends tbl tbl₁ := extends_append tbl s _
            obtain ⟨opt, tbl₂, hrun, he₂, hv⟩ :=
              ih hs gs tbl₁ (list_received_extends he₁ s ht) hl
            have ha := lookup_append_self tbl s (c • lookup tbl s h)
            have ha₂ := lookup_extends he₂ s (tbl s).length ha.1
            cases opt with
            | none =>
                refine ⟨some (tbl s).length, tbl₂, ?_, extends_trans he₁ he₂, ?_⟩
                · simp only [buildVectorAux, ite_eq_right hc, simulateQ_bind, StateT.run_bind,
                    run_smul, pure_bind]
                  rw [hrun]
                  simp
                · exact ⟨ha₂.1, by simpa [evaluate_cons, hv, hh.2] using ha₂.2.trans ha.2⟩
            | some b =>
                let tbl₃ := append tbl₂ s (lookup tbl₂ s (tbl s).length + lookup tbl₂ s b)
                refine ⟨some (tbl₂ s).length, tbl₃, ?_,
                  extends_trans (extends_trans he₁ he₂) (extends_append tbl₂ s _), ?_⟩
                · simp only [buildVectorAux, ite_eq_right hc, simulateQ_bind, StateT.run_bind,
                    run_smul, pure_bind]
                  rw [hrun]
                  simp [run_add, tbl₃]
                · have hf := lookup_append_self tbl₂ s
                    (lookup tbl₂ s (tbl s).length + lookup tbl₂ s b)
                  exact ⟨hf.1, by
                    exact hf.2.trans (by rw [ha₂.2, ha.2, hh.2, hv.2, evaluate_cons])⟩

private theorem run_buildVector (s : S) (cs : List F) (hs : List Handle)
    (gs : List (G s)) (tbl : Tbl G)
    (hr : List.Forall₂ (fun h g => h < (tbl s).length ∧ lookup tbl s h = g) hs gs)
    (hlen : cs.length = gs.length) :
    ∃ h tbl',
      (simulateQ (handler M enc random game) (buildVector s cs hs)).run tbl =
        pure (h, tbl') ∧ Extends tbl tbl' ∧
      h < (tbl' s).length ∧ lookup tbl' s h = evaluate cs gs := by
  obtain ⟨opt, tbl', hrun, he, hv⟩ := run_buildVectorAux M enc random game s cs hs gs tbl hr hlen
  cases opt with
  | none =>
      refine ⟨(tbl' s).length, append tbl' s 0, ?_,
        extends_trans he (extends_append tbl' s 0), ?_⟩
      · simp [buildVector, simulateQ_bind, StateT.run_bind, hrun, run_smul]
      · simpa [hv] using lookup_append_self tbl' s 0
  | some h =>
      exact ⟨h, tbl', by simp [buildVector, simulateQ_bind, StateT.run_bind, hrun], he, hv⟩

private theorem run_buildVectors (s : S) (css : List (List F)) (hs : List Handle)
    (gs outs : List (G s)) (tbl : Tbl G)
    (hr : List.Forall₂ (fun h g => h < (tbl s).length ∧ lookup tbl s h = g) hs gs)
    (hv : List.Forall₂ (fun g cs => cs.length = gs.length ∧ evaluate cs gs = g) outs css) :
    ∃ handles tbl',
      (simulateQ (handler M enc random game) (css.mapM fun cs => buildVector s cs hs)).run tbl =
        pure (handles, tbl') ∧ Extends tbl tbl' ∧
      List.Forall₂ (fun h g => h < (tbl' s).length ∧ lookup tbl' s h = g) handles outs := by
  induction hv generalizing tbl with
  | nil => exact ⟨[], tbl, by simp, extends_refl tbl, .nil⟩
  | @cons g cs outs css hv hvs ih =>
      obtain ⟨h, tbl₁, hrun₁, he₁, hh⟩ :=
        run_buildVector M enc random game s cs hs gs tbl hr hv.1
      obtain ⟨handles, tbl₂, hrun₂, he₂, ht⟩ :=
        ih tbl₁ (list_received_extends he₁ s hr)
      refine ⟨h :: handles, tbl₂, ?_, extends_trans he₁ he₂, .cons ?_ ht⟩
      · simp only [List.mapM_cons, simulateQ_bind, StateT.run_bind, hrun₁, pure_bind,
          hrun₂, simulateQ_pure, StateT.run_pure]
      · have heh := lookup_extends he₂ s h hh.1
        exact ⟨heh.1, heh.2.trans (hh.2.trans hv.2)⟩

private theorem run_sortMap (f : (s : S) →
    OracleComp (Target F S E Query Reply) (List Handle)) (values : Groups G) (tbl₀ : Tbl G)
    (hf : ∀ s tbl, Extends tbl₀ tbl → ∃ hs tbl',
      (simulateQ (handler M enc random game) (f s)).run tbl = pure (hs, tbl') ∧
      Extends tbl tbl' ∧
      List.Forall₂ (fun h g => h < (tbl' s).length ∧ lookup tbl' s h = g) hs (values s))
    (sorts : List S) (tbl : Tbl G) (he : Extends tbl₀ tbl) :
    ∃ handles tbl',
      (simulateQ (handler M enc random game) (sortMap f sorts)).run tbl = pure (handles, tbl') ∧
      Extends tbl tbl' ∧ ∀ s ∈ sorts,
      List.Forall₂ (fun h g => h < (tbl' s).length ∧ lookup tbl' s h = g)
        (handles s) (values s) := by
  induction sorts generalizing tbl with
  | nil => exact ⟨fun _ => [], tbl, by simp [sortMap], extends_refl tbl, by simp⟩
  | cons s ss ih =>
      obtain ⟨hs, tbl₁, hrun₁, he₁, hv₁⟩ := hf s tbl he
      obtain ⟨rest, tbl₂, hrun₂, he₂, hv₂⟩ := ih tbl₁ (extends_trans he he₁)
      refine ⟨Function.update rest s hs, tbl₂, ?_, extends_trans he₁ he₂, ?_⟩
      · simp [sortMap, simulateQ_bind, StateT.run_bind, hrun₁, hrun₂]
      · intro t ht
        by_cases hts : t = s
        · subst t
          simpa using list_received_extends he₂ s hv₁
        · simpa [Function.update_of_ne hts] using hv₂ t ((List.mem_cons.mp ht).resolve_left hts)

private theorem run_buildMessage [Fintype S] {Data : Type}
    (handles : Groups (fun _ : S => Handle)) (basis : Groups G)
    (out : Explained F Data G) (tbl : Tbl G) (hr : Received tbl handles basis)
    (hv : out.Valid basis) :
    ∃ msg tbl',
      (simulateQ (handler M enc random game) (buildMessage handles out)).run tbl =
        pure (msg, tbl') ∧ Extends tbl tbl' ∧ lookupMessage tbl' msg = out.value := by
  obtain ⟨hs, tbl', hrun, he, hreads⟩ := run_sortMap M enc random game
    (fun s => (out.coefficients s).mapM fun cs => buildVector s cs (handles s))
    out.value.groups tbl (fun s tbl' he =>
      run_buildVectors M enc random game s (out.coefficients s) (handles s) (basis s)
        (out.value.groups s) tbl' (received_extends hr he s) (hv s))
    Finset.univ.toList tbl (extends_refl tbl)
  refine ⟨⟨out.value.data, hs⟩, tbl', ?_, he, ?_⟩
  · simp [buildMessage, hrun]
  · have hh : Received tbl' hs out.value.groups := fun s => hreads s (by simp)
    cases out with
    | mk value coefficients =>
      cases value
      simp only [lookupMessage, hh.readback]

private theorem run_decodeList (dec : (s : S) → E s → G s)
    (hdec : ∀ s g, dec s (enc s g) = g) (s : S) (hs : List Handle) (tbl : Tbl G) :
    (simulateQ (handler M enc random game) (hs.mapM fun h => do
      let e ← encodingQ s h
      pure (dec s e))).run tbl = pure (hs.map (lookup tbl s), tbl) := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
      simp only [List.mapM_cons, simulateQ_bind, StateT.run_bind, simulateQ_pure,
        StateT.run_pure]
      have hquery : (simulateQ (handler M enc random game)
          (encodingQ s h)).run tbl =
          pure (enc s (lookup tbl s h), tbl) := by
        exact congrArg (fun st : StateT (Tbl G) N (E s) => st.run tbl)
          (simulateQ_spec_query (handler M enc random game) (.inr (.inl (s, h))))
      rw [hquery]
      simp only [pure_bind, hdec, ih, List.map_cons]

private theorem run_decodeSorts (dec : (s : S) → E s → G s)
    (hdec : ∀ s g, dec s (enc s g) = g) (hs : Groups (fun _ : S => Handle))
    (sorts : List S) (tbl : Tbl G) :
    (simulateQ (handler M enc random game) (sortMap (fun s => (hs s).mapM fun h => do
      let e ← encodingQ s h
      pure (dec s e)) sorts)).run tbl =
        pure ((fun s => if s ∈ sorts then (hs s).map (lookup tbl s) else []), tbl) := by
  induction sorts with
  | nil => simp [sortMap]
  | cons s ss ih =>
      simp only [sortMap, simulateQ_bind, StateT.run_bind,
        run_decodeList M enc random game dec hdec, pure_bind, ih,
        simulateQ_pure, StateT.run_pure]
      congr 2
      funext t
      by_cases hts : t = s
      · subst t
        simp
      · simp [hts]

private theorem run_decodeGroups [Fintype S] (dec : (s : S) → E s → G s)
    (hdec : ∀ s g, dec s (enc s g) = g) (hs : Groups (fun _ : S => Handle)) (tbl : Tbl G) :
    (simulateQ (handler M enc random game) (decodeGroups dec hs)).run tbl =
      pure ((fun s => (hs s).map (lookup tbl s)), tbl) := by
  simpa [decodeGroups] using run_decodeSorts M enc random game dec hdec hs Finset.univ.toList tbl

private theorem run_compile [Fintype S] (dec : (s : S) → E s → G s)
    (hdec : ∀ s g, dec s (enc s g) = g)
    (program : OracleComp (explainedSpec F G (CoinQuery Query) (CoinReply Reply))
      (Explained F Result G))
    (hs : Groups (fun _ : S => Handle)) (basis : Groups G) (tbl : Tbl G)
    (hr : Received tbl hs basis) (ha : IsAlgebraic basis program) :
    (fun z => lookupMessage z.2 z.1) <$>
      (simulateQ (handler M enc random game) (compile dec program hs)).run tbl =
    (fun z => z.1.value) <$>
      (simulateQ (certifiedHandler random game) program).run basis := by
  induction program using OracleComp.inductionOn generalizing hs basis tbl with
  | pure out =>
      obtain ⟨msg, tbl', hrun, _, hv⟩ :=
        run_buildMessage M enc random game hs basis out tbl hr ha
      simp [compile_pure, hrun, hv]
  | query_bind q next ih =>
      obtain ⟨hq, hn⟩ := (isAlgebraic_query basis q next).mp ha
      rcases q with ⟨⟨q, groups⟩, coefficients⟩
      cases q with
      | inr n =>
          rw [compile_coin dec n groups coefficients next hs]
          simp only [ simulateQ_bind, StateT.run_bind, run_coin,
            bind_map_left, simulateQ_spec_query, run_certified, withCoins_apply_inr,
            bind_assoc, pure_bind, map_bind]
          apply bind_congr
          intro coin
          have hempty : extend basis (fun _ => []) = basis := by
            funext s
            exact List.append_nil (basis s)
          have hnext := hn ⟨coin, fun _ => []⟩
          rw [hempty] at hnext ⊢
          exact ih ⟨coin, fun _ => []⟩ hs basis tbl hr hnext
      | inl q =>
          rw [compile_request dec q groups coefficients next hs]
          obtain ⟨msg, tbl₁, hrun, he, hv⟩ :=
            run_buildMessage M enc random game hs basis
              ⟨⟨Sum.inl q, groups⟩, coefficients⟩ tbl hr hq
          have hgroups : (fun s => (msg.groups s).map (lookup tbl₁ s)) = groups :=
            congrArg Message.groups hv
          simp only [simulateQ_bind, StateT.run_bind, hrun, pure_bind,
            run_game, simulateQ_spec_query, run_certified, withCoins_apply_inl,
            bind_assoc, map_bind]
          change Message (Reply q) G → OracleComp
            (explainedSpec F G (CoinQuery Query) (CoinReply Reply)) (Explained F Result G) at next
          dsimp only [lookupMessage, CoinReply, Sum.elim]
          rw [hgroups]
          change _ = ((do
            let reply : Message (Reply q) G ← game ⟨q, groups⟩
            pure (reply, extend basis reply.groups)) >>= fun z =>
              (fun z => z.1.value) <$>
                (simulateQ (certifiedHandler random game) (next z.1)).run z.2)
          simp only [bind_assoc, pure_bind]
          apply bind_congr
          intro reply
          have hdecode : (fun s => ((pushGroups reply.groups tbl₁).1 s).map
              (lookup (pushGroups reply.groups tbl₁).2 s)) = reply.groups :=
            funext (lookup_pushGroups reply.groups tbl₁)
          simp only [pure_bind, run_decodeGroups M enc random game dec hdec, hdecode]
          exact ih reply (extend hs (pushGroups reply.groups tbl₁).1)
            (extend basis reply.groups) (pushGroups reply.groups tbl₁).2
            (received_pushGroups (received_extends hr he) reply.groups) (hn reply)

/-- Reading back the compiled handle run gives exactly the certified run, including all
ambient monadic effects. Decoding must be a left inverse to the supplied encoding. -/
theorem ofExplained_run [Fintype S]
    (B : Interaction.Adversary F G Input (CoinQuery Query) (CoinReply Reply) Result)
    (dec : (s : S) → E s → G s) (hdec : ∀ s g, dec s (enc s g) = g)
    (input : Message Input G) :
    (fun z => lookupMessage z.2 z.1) <$> (ofExplained B dec).run M enc random game input =
      (fun z => z.1.value) <$> B.run (withCoins random game) input := by
  have hr := received_initial input.groups
  unfold HandleAdversary.run GroupModel.run ofExplained
  simp only [simulateQ_bind, StateT.run_bind,
    run_decodeGroups M enc random game dec hdec, hr.readback, pure_bind]
  exact run_compile M enc random game dec hdec (B.main input) _ input.groups input.groups
    hr (B.algebraic input)

end Semantics

end GroupModel
