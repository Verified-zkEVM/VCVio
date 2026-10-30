/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSealBridge
public import VCVio.CryptoFoundations.TimeLockPuzzle.Hiding
public import VCVio.CryptoFoundations.TimeLockPuzzle.Lift

/-!
# leanSeal hiding over one random oracle: the adversary adapter

An encoding `E : RandomOracleEncoding spec D M` of typed oracles `spec` into one random oracle
`D →ₒ M` turns a two-phase adversary against the single oracle into one against the typed
oracles. Each raw input that encodes a typed point is answered through the typed oracle at that
point, and every other raw input from a private lazy random oracle, whose cache passes from the
preprocessing phase to the online phase.

This file states the adapter for a two-phase adversary whose online phase queries any free
summand `free` beside its rounds: local coins in the delay game, local coins together with the
left-or-right challenge oracle in the hiding game. Queries to `free` are forwarded unchanged. A
raw round draws the private values of all its inputs with local coins of `free`, embedded along
`unifSpec → free` (`TimeLockPuzzle.sideDraws`), submits the typed points its inputs encode as one
typed round, and reassembles the answers (`RandomOracleEncoding.assemble`). The preprocessing phase
is the one of `RandomOracleEncoding.adaptAdversary`.

## Main definitions

* `OracleComp.RandomOracleEncoding.freeOnlineImpl`: the online step of the adapter for any free
  summand.
* `OracleComp.RandomOracleEncoding.adaptTwoPhase`: the typed two-phase adversary of a raw one, for
  any free summand and output.
* `OracleComp.RandomOracleEncoding.adaptHidingAdversary`: the typed hiding adversary of a raw one.

## Main statements

* `OracleComp.RandomOracleEncoding.isOnlineQueryBound_freeOnlineImpl_inr_run`: a raw round is one
  typed round holding the typed points its inputs encode.
* `OracleComp.RandomOracleEncoding.isQueryBound_adaptTwoPhase`: the adapter keeps the
  preprocessing budget and the online budget of rounds and points.
* `OracleComp.RandomOracleEncoding.makesAtMostQueries_adaptHidingAdversary`: the hiding adapter
  forwards challenge queries one for one, so it keeps the encryption budget.
-/

public section

open OracleSpec OracleComp TimeLockPuzzle

namespace OracleComp.RandomOracleEncoding

variable {ι D M : Type} {spec : OracleSpec.{0, 0} ι} [SampleableType M]
  [∀ t, SampleableType (spec.Range t)] (E : RandomOracleEncoding spec D M) [DecidableEq D]

/-! ## The adapter for any free summand -/

section FreeSummand

variable {τ : Type} {free : OracleSpec.{0, 0} τ}
  [MonadLiftT (OracleQuery unifSpec) (OracleQuery free)]

/-- The online step of the adapter for the free summand `free`. Queries to `free` are forwarded.
A raw round draws the private values of all its inputs, in order and with repetitions, with local
coins of `free` (`TimeLockPuzzle.sideDraws`); submits the typed points that its inputs encode as
one typed round; and reassembles the answers: at an encoding, the typed answer completed from the
private value, and elsewhere the private value (`RandomOracleEncoding.assemble`). -/
@[expose]
def freeOnlineImpl :
    QueryImpl (free + (D →ₒ M).batch)
      (StateT (D →ₒ M).QueryCache (OracleComp (free + spec.batch)))
  | .inl t => StateT.lift (liftM ((free + spec.batch).query (.inl t)))
  | .inr xs => do
      let ps ← sideDraws (spec := spec) (side := (D →ₒ M)) (free := free) xs
      let us ← StateT.lift (liftM ((free + spec.batch).query (.inr (xs.filterMap E.route))))
      return E.assemble xs ps us

/-- The typed two-phase adversary of a raw one, for the free summand `free` and outputs `Out`.
The preprocessing phase runs the raw one through `RandomOracleEncoding.preprocessImpl` from the
empty private cache, and the online phase through `RandomOracleEncoding.freeOnlineImpl` from the
private cache that preprocessing leaves, kept in the state. -/
@[expose]
def adaptTwoPhase {Puzzle Out : Type} (adv : TwoPhaseAdversary free (D →ₒ M) Puzzle Out) :
    TwoPhaseAdversary free spec Puzzle Out where
  State := adv.State × (D →ₒ M).QueryCache
  preprocess := (simulateQ E.preprocessImpl adv.preprocess).run ∅
  online σ puzzle := (simulateQ E.freeOnlineImpl (adv.online σ.1 puzzle)).run' σ.2

/-- A raw round is simulated by one typed round holding the typed points that its inputs encode,
in order and with repetitions: the private draws submit no round. -/
theorem isOnlineQueryBound_freeOnlineImpl_inr_run (xs : List D) (s : (D →ₒ M).QueryCache) :
    IsOnlineQueryBound ((E.freeOnlineImpl (free := free) (.inr xs)).run s)
      (1, (xs.filterMap E.route).length) := by
  simp only [freeOnlineImpl, StateT.run_bind]
  refine isOnlineQueryBound_bind_le (0, 0) (1, (xs.filterMap E.route).length)
    (isOnlineQueryBound_sideDraws_run _ _ _) (fun z => ?_) ⟨by omega, by omega⟩
  rw [StateT.run_lift, bind_assoc]
  refine isOnlineQueryBound_bind_le (1, (xs.filterMap E.route).length) (0, 0) ?_
    (fun _ => ?_) ⟨le_rfl, le_rfl⟩
  · rw [IsOnlineQueryBound, isQueryBound_query_iff]
    simp
  · simp only [pure_bind, StateT.run_pure]
    exact isOnlineQueryBound_pure _ _

/-- A step of the online adapter costs at most the query it answers: nothing for a query to the
free summand, and at most one round of at most as many points for a raw round. -/
theorem isOnlineQueryBound_freeOnlineImpl (t : (free + (D →ₒ M).batch).Domain)
    (s : (D →ₒ M).QueryCache) :
    IsOnlineQueryBound ((E.freeOnlineImpl t).run s) (onlineStep t) := by
  rcases t with t | xs
  · simp only [freeOnlineImpl, onlineStep_inl, StateT.run_lift]
    exact (isOnlineQueryBound_query_bind_inl_iff _ _ _).2 fun _ => isOnlineQueryBound_pure _ _
  · exact (E.isOnlineQueryBound_freeOnlineImpl_inr_run xs s).mono
      (Prod.mk_le_mk.mpr ⟨le_rfl, List.length_filterMap_le _ _⟩)

/-- **The adapter keeps the budgets.** If a raw adversary makes at most `Q` preprocessing queries
and its online phase submits at most `b.1` rounds holding at most `b.2` points, so does its typed
adversary: each raw query or round becomes at most one typed query or round with at most as many
points, and raw inputs that encode no typed point and queries to the free summand cost nothing. -/
theorem isQueryBound_adaptTwoPhase {Puzzle Out : Type}
    {adv : TwoPhaseAdversary free (D →ₒ M) Puzzle Out} {Q : ℕ} {b : ℕ × ℕ}
    (h : adv.IsQueryBound Q b) : (E.adaptTwoPhase adv).IsQueryBound Q b := by
  refine ⟨h.1.simulateQ_run_StateT_of_step (E.isQueryBoundP_preprocessImpl) ∅, fun σ puzzle => ?_⟩
  have hrun : IsOnlineQueryBound ((simulateQ E.freeOnlineImpl (adv.online σ.1 puzzle)).run σ.2) b :=
    IsQueryBound.simulateQ_run_of_step (combine := (· + ·)) (mapBudget := id)
      (stepBudget := fun t _ => onlineStep t) (h.2 σ.1 puzzle) isOnlineQueryBound_bind
      (fun t _ s _ => E.isOnlineQueryBound_freeOnlineImpl t s)
      (fun t b hb => by
        rcases t with t | xs
        · simp
        · simp only [onlineCanQuery_inr] at hb
          refine Prod.ext ?_ ?_ <;> simp <;> omega) σ.2
  exact (isQueryBound_map_iff _ _ _ _ _).2 hrun

end FreeSummand

/-! ## The hiding adversary -/

section Hiding

variable {Msg C : Type}

/-- The typed hiding adversary of a raw one: `RandomOracleEncoding.adaptTwoPhase` with the free
summand of local coins and the left-or-right challenge oracle. Challenge queries and local coins
are forwarded at no cost, and the private draws are local coins. -/
abbrev adaptHidingAdversary {Puzzle : Type} (adv : HidingAdversary (D →ₒ M) Puzzle Msg C) :
    HidingAdversary spec Puzzle Msg C :=
  E.adaptTwoPhase adv

omit [∀ t, SampleableType (spec.Range t)] in
/-- Local coins lifted into the hiding adversary's interface make no challenge query. -/
lemma isQueryBoundP_liftComp_challenge {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftComp oa ((unifSpec + LeftOrRight.spec Msg C) + spec.batch))
      (· matches .inl (.inr _)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
      rw [liftComp_bind, liftComp_query]
      exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp, fun u => by simpa using ih u⟩

/-- A step of the hiding adapter makes a challenge query exactly when it answers one: a challenge
query is forwarded, and local coins, private draws and typed rounds make none. -/
lemma isQueryBoundP_freeOnlineImpl_challenge
    (t : ((unifSpec + LeftOrRight.spec Msg C) + (D →ₒ M).batch).Domain)
    (s : (D →ₒ M).QueryCache) :
    IsQueryBoundP ((E.freeOnlineImpl t).run s) (· matches .inl (.inr _))
      (if t matches .inl (.inr _) then 1 else 0) := by
  rcases t with (k | mm) | xs
  · simp only [freeOnlineImpl, StateT.run_lift]
    exact isQueryBoundP_bind_zero _ _ (by simp) fun _ => isQueryBoundP_pure _ _ _
  · simp only [freeOnlineImpl, StateT.run_lift, ↓reduceIte]
    rw [← Nat.add_zero 1]
    exact isQueryBoundP_bind (by simp) fun _ _ => isQueryBoundP_pure _ _ _
  · simp only [freeOnlineImpl, sideDraws, StateT.run_bind, StateT.run_mk, StateT.run_lift,
      bind_assoc, pure_bind, StateT.run_pure]
    refine isQueryBoundP_bind_zero _ _ (isQueryBoundP_liftComp_challenge _) fun _ => ?_
    exact isQueryBoundP_bind_zero _ _ (by simp) fun _ => isQueryBoundP_pure _ _ _

/-- **The hiding adapter keeps the encryption budget.** If a raw hiding adversary makes at most
`q` challenge queries, so does its typed adversary: challenge queries are forwarded one for one,
and the private draws are local coins. -/
theorem makesAtMostQueries_adaptHidingAdversary {Puzzle : Type}
    {adv : HidingAdversary (D →ₒ M) Puzzle Msg C} {q : ℕ} (h : adv.MakesAtMostQueries q) :
    (E.adaptHidingAdversary adv).MakesAtMostQueries q := fun σ puzzle => by
  have hrun : IsQueryBoundP ((simulateQ E.freeOnlineImpl (adv.online σ.1 puzzle)).run σ.2)
      (· matches .inl (.inr _)) q :=
    (h σ.1 puzzle).simulateQ_run_StateT_of_step
      (fun t s => by
        rcases t with (k | mm) | xs <;> exact E.isQueryBoundP_freeOnlineImpl_challenge _ s) σ.2
  rw [← isQueryBoundP_map_iff _ Prod.fst, ← StateT.run'_eq] at hrun
  exact (isQueryBoundP_congr_pred fun _ => Iff.rfl).mp hrun

end Hiding

end OracleComp.RandomOracleEncoding
