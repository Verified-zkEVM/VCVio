/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Encoding
public import VCVio.CryptoFoundations.GroupModel.Interaction

/-!
# Handle adversaries and games on group elements
-/

public section

open OracleComp OracleSpec

namespace GroupModel

open Interaction

variable {S : Type} {G W E : S → Type}

/-- The game interface exchanges handles separated by sort. -/
@[expose] def handleSpec (Query : Type) (Reply : Query → Type) :
    OracleSpec (Message Query (fun _ : S => Handle)) :=
  fun q => Message (Reply q.data) (fun _ : S => Handle)

/-- Resolve all handles in a message against a table. -/
@[expose] def lookupMessage [∀ s, Zero (G s)] {R : Type} (tbl : Tbl G)
    (msg : Message R (fun _ : S => Handle)) : Message R G :=
  ⟨msg.data, fun s => (msg.groups s).map (lookup tbl s)⟩

/-- Append a reply at every sort, returning its fresh handles and the extended table. -/
@[expose] def pushGroups (groups : Groups G) (tbl : Tbl G) :
    Groups (fun _ : S => Handle) × Tbl G :=
  (fun s => List.range' (tbl s).length (groups s).length, fun s => tbl s ++ groups s)

/-- Fresh reply handles read back exactly the supplied group values. -/
theorem lookup_pushGroups [∀ s, Zero (G s)] (groups : Groups G) (tbl : Tbl G) (s : S) :
    ((pushGroups groups tbl).1 s).map (lookup (pushGroups groups tbl).2 s) = groups s := by
  apply List.ext_getElem
  · simp [pushGroups]
  · intro i hi hj
    simp [pushGroups, lookup, List.getD, hj]

/-- Pushing replies commutes with arbitrary sortwise maps of group values. -/
theorem pushGroups_map (φ : (s : S) → G s → W s) (groups : Groups G) (tbl : Tbl G) :
    pushGroups (mapTbl φ groups) (mapTbl φ tbl) =
      Prod.map id (mapTbl φ) (pushGroups groups tbl) := by
  apply Prod.ext
  · simp [pushGroups, mapTbl]
  · funext s
    simp [pushGroups, mapTbl]

/-- Run an element-valued game request and install its reply in the handle table. -/
@[expose] def liftGame [∀ s, Zero (G s)] {Query : Type} {Reply : Query → Type}
    {m : Type → Type} [Monad m] (impl : QueryImpl (plainSpec G Query Reply) m) :
    QueryImpl (handleSpec (S := S) Query Reply) (StateT (Tbl G) m) :=
  fun q tbl => do
    let reply ← impl (lookupMessage tbl q)
    let (handles, tbl') := pushGroups reply.groups tbl
    pure (⟨reply.data, handles⟩, tbl')

/-- Lift the shared randomness handler without changing the handle table. -/
abbrev coinImpl {N : Type → Type} [Monad N] (random : QueryImpl unifSpec N) :
    QueryImpl unifSpec (StateT (Tbl G) N) :=
  random.liftTarget (StateT (Tbl G) N)

/-- Sampling runs the shared handler and leaves the handle table unchanged. -/
theorem coinImpl_apply {N : Type → Type} [Monad N] [LawfulMonad N]
    (random : QueryImpl unifSpec N) (n : ℕ) (tbl : Tbl G) :
    (coinImpl random n).run tbl = (fun x => (x, tbl)) <$> random n := by
  simp [coinImpl]

/-- Uniform private coins specialize to the handler used by `runGen`. -/
theorem coinImpl_uniform :
    coinImpl (G := G) (QueryImpl.ofLift unifSpec ProbComp) =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Tbl G) ProbComp) := rfl

/-- A handle adversary has group operations, encodings, private coins, and game requests. -/
abbrev HandleAdversary (F : Type) (σ : Sig S) (E : S → Type)
    (Input Query : Type) (Reply : Query → Type) (Result : Type) :=
  Message Input (fun _ : S => Handle) →
    OracleComp (spec F σ + (encSpec E + (unifSpec + handleSpec (S := S) Query Reply)))
      (Message Result (fun _ : S => Handle))

/-- Execute an adversary from the input's group lists, with equality of real elements. -/
@[expose] def HandleAdversary.run {F : Type} [CommSemiring F] [DecidableEq S]
    {σ : Sig S} [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    [∀ s, DecidableEq (G s)] {Input Query Result : Type} {Reply : Query → Type}
    (A : HandleAdversary F σ E Input Query Reply Result) (M : Model F σ G)
    (enc : (s : S) → G s → E s) {N : Type → Type} [Monad N]
    (random : QueryImpl unifSpec N) (impl : QueryImpl (plainSpec G Query Reply) N)
    (input : Message Input G) : N (Message Result (fun _ : S => Handle) × Tbl G) :=
  GroupModel.run M (fun _ => id) (encImpl (m := N) enc + (coinImpl (G := G) random + liftGame impl))
    (A ⟨input.data, fun s => List.range (input.groups s).length⟩) input.groups

/-- Include a generic computation by granting it an additional encoding oracle. -/
@[expose] def toAlgebraic {F : Type} {σ : Sig S} {ι : Type} {Γ : OracleSpec ι} {α : Type}
    (A : OracleComp (spec F σ + (unifSpec + Γ)) α) :
    OracleComp (spec F σ + (encSpec E + (unifSpec + Γ))) α :=
  liftComp A _

/-- Inclusion preserves the exact computation, including private coins and final state. -/
theorem run_toAlgebraic {F : Type} [CommSemiring F] [DecidableEq S] {σ : Sig S}
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    {U : S → Type} [∀ s, DecidableEq (U s)] (M : Model F σ G)
    (obs : (s : S) → G s → U s) (enc : (s : S) → G s → E s)
    {N : Type → Type} [Monad N] [LawfulMonad N] (random : QueryImpl unifSpec N)
    {ι : Type} {Γ : OracleSpec ι} (game : QueryImpl Γ (StateT (Tbl G) N))
    {α : Type} (A : OracleComp (spec F σ + (unifSpec + Γ)) α) (tbl : Tbl G) :
    run M obs (encImpl (m := N) enc + (coinImpl (G := G) random + game)) (toAlgebraic A) tbl =
      run M obs (coinImpl (G := G) random + game) A tbl := by
  unfold run toAlgebraic
  congr 1
  rw [liftComp_def, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with t | t
  · change simulateQ _ (liftM ((spec F σ + (encSpec E + (unifSpec + Γ))).query
      (.inl t))) = _
    simp
  · change simulateQ _ (liftM ((spec F σ + (encSpec E + (unifSpec + Γ))).query
      (.inr (.inr t)))) = _
    simp

end GroupModel
