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
# leanSeal hiding over one random oracle: the adversary adapter and the experiment comparison

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

The file then compares the hiding experiments. A raw puzzle and a raw DEM refine a typed puzzle and
a typed DEM when the raw generator is the typed one with its rounds encoded and the raw encryption
is the typed one with its queries encoded. Under an encoding that never clashes, the raw hiding
experiment of a raw adversary then has the law of the typed hiding experiment of its adapted
adversary at each hidden bit, so the two hiding advantages are equal. The challenger's encryptions
query the typed oracles directly and never the adapter's private cache, so the typed points they
query and the raw inputs the adversary queries meet only through the encoding.

## Main definitions

* `OracleComp.RandomOracleEncoding.freeOnlineImpl`: the online step of the adapter for any free
  summand.
* `OracleComp.RandomOracleEncoding.adaptTwoPhase`: the typed two-phase adversary of a raw one, for
  any free summand and output.
* `OracleComp.RandomOracleEncoding.adaptHidingAdversary`: the typed hiding adversary of a raw one.
* `OracleComp.RandomOracleEncoding.combinedHidingExperiment`: the hiding experiment on the
  combined interface, where the adversary queries raw inputs and the generator and the challenger
  query typed points.

## Main statements

* `OracleComp.RandomOracleEncoding.isOnlineQueryBound_freeOnlineImpl_inr_run`: a raw round is one
  typed round holding the typed points its inputs encode.
* `OracleComp.RandomOracleEncoding.isQueryBound_adaptTwoPhase`: the adapter keeps the
  preprocessing budget and the online budget of rounds and points.
* `OracleComp.RandomOracleEncoding.makesAtMostQueries_adaptHidingAdversary`: the hiding adapter
  forwards challenge queries one for one, so it keeps the encryption budget.
* `OracleComp.RandomOracleEncoding.evalDist_hidingExperiment_adaptHidingAdversary`: the raw
  hiding experiment has the law of the typed hiding experiment of the adapted adversary.
* `OracleComp.RandomOracleEncoding.hidingAdvantage_eq_hidingAdvantage_adaptHidingAdversary`: the
  raw hiding advantage is the typed hiding advantage of the adapted adversary.
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

/-! ## Comparing the hiding experiments

A raw hiding experiment is compared with the typed hiding experiment of the adapted adversary
through a combined experiment on the interface `unifSpec + (spec + (D →ₒ M))`: the adversary
queries raw inputs, while the generator and the challenger's encryptions query typed points.
Encoded into the single oracle, the combined experiment is the raw experiment
(`simulateQ_encodeImpl_combinedHidingExperiment`); in the typed world it has the law of the typed
experiment of the adapted adversary (`typedImpl_combinedHidingExperiment_evalDistEq`). The
challenger never touches the adapter's private cache, so an input that the adversary and the
challenger both query must be the encoding of a typed point. -/

section Experiment

variable {Msg C : Type}

/-- The challenge handler of the combined experiment: local coins are forwarded, a challenge query
is answered by the left-or-right oracle over the typed encryption, whose queries go to the typed
side of the combined interface, and a raw input is forwarded to the raw side. -/
def combinedChallengeImpl {Puzzle Key Λ : Type} [DecidableEq Λ]
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) Msg C) (leak : Msg → Λ)
    (puzzle : Puzzle) (key : Key) (b : Bool) :
    QueryImpl ((unifSpec + LeftOrRight.spec Msg C) + (D →ₒ M))
      (OracleComp (unifSpec + (spec + (D →ₒ M)))) :=
  ((fun n => liftM ((unifSpec + (spec + (D →ₒ M))).query (.inl n)) :
      QueryImpl unifSpec (OracleComp (unifSpec + (spec + (D →ₒ M))))) +
    LeftOrRight.oracle
      (fun msg => simulateQ (typedLift (D := D) (M := M)) (dem.encrypt (puzzle, key) msg)) leak b) +
  (fun x => liftM ((unifSpec + (spec + (D →ₒ M))).query (.inr (.inr x))) :
      QueryImpl (D →ₒ M) (OracleComp (unifSpec + (spec + (D →ₒ M)))))

/-- The hiding experiment of a typed puzzle and a typed DEM against a raw hiding adversary, on the
combined interface: the adversary's preprocessing and online phases query raw inputs, and the
generator and the challenger's encryptions query typed points. -/
def combinedHidingExperiment {Puzzle Key Λ : Type} [DecidableEq Λ]
    (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) Msg C) (leak : Msg → Λ)
    (adv : HidingAdversary (D →ₒ M) Puzzle Msg C) (b : Bool) :
    OracleComp (unifSpec + (spec + (D →ₒ M))) Bool := do
  let σ ← simulateQ rawLift adv.preprocess
  let (puzzle, key) ← simulateQ typedLift (simulateQ spec.unbatch tlp.gen)
  simulateQ (combinedChallengeImpl dem leak puzzle key b)
    (simulateQ (D →ₒ M).unbatch (adv.online σ puzzle))

omit [DecidableEq D] in
/-- Encoded into the single oracle, the combined experiment is the raw hiding experiment of a raw
puzzle whose generator is the typed generator with its rounds encoded, and a raw DEM whose
encryption is the typed encryption with its queries encoded. -/
lemma simulateQ_encodeImpl_combinedHidingExperiment {Puzzle Key Λ : Type} [DecidableEq Λ]
    {tlpRaw : TimeLockPuzzle (D →ₒ M) Puzzle Key} {tlp : TimeLockPuzzle spec Puzzle Key}
    {demRaw : DEMScheme (OracleComp (unifSpec + (D →ₒ M))) (Puzzle × Key) Msg C}
    {dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) Msg C} (leak : Msg → Λ)
    (hgen : tlpRaw.gen = simulateQ E.roundImpl tlp.gen)
    (henc : ∀ key msg, demRaw.encrypt key msg =
      simulateQ (E.encodeImpl ∘ₛ typedLift) (dem.encrypt key msg))
    (adv : HidingAdversary (D →ₒ M) Puzzle Msg C) (b : Bool) :
    simulateQ E.encodeImpl (combinedHidingExperiment tlp dem leak adv b) =
      tlpRaw.hidingExperiment demRaw leak adv b := by
  have hg : simulateQ E.encodeImpl (simulateQ typedLift (simulateQ spec.unbatch tlp.gen)) =
      simulateQ (D →ₒ M).unbatch tlpRaw.gen := by
    rw [← QueryImpl.simulateQ_compose, QueryImpl.simulateQ_simulateQ_unbatch,
      encodeImpl_compose_typedLift_batch', QueryImpl.simulateQ_compose, hgen]
  have hch : ∀ (puzzle : Puzzle) (key : Key),
      E.encodeImpl ∘ₛ combinedChallengeImpl dem leak puzzle key b =
        (unifSpec.passthrough + LeftOrRight.oracle (demRaw.encrypt (puzzle, key)) leak b) +
          (QueryImpl.id' (D →ₒ M)).liftTarget (OracleComp (unifSpec + (D →ₒ M))) := by
    intro puzzle key
    funext t
    rcases t with (n | ⟨m₀, m₁⟩) | x
    · simp [combinedChallengeImpl, encodeImpl]
      rfl
    · simp only [QueryImpl.apply_compose, combinedChallengeImpl, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr, QueryImpl.passthrough_add, LeftOrRight.oracle_apply]
      split_ifs <;> simp [← QueryImpl.simulateQ_compose, henc]
    · simp [combinedChallengeImpl, encodeImpl]
      rfl
  simp only [combinedHidingExperiment, hidingExperiment, simulateQ_bind,
    simulateQ_encodeImpl_rawLift, hg]
  refine bind_congr fun σ => bind_congr fun pk => ?_
  rcases pk with ⟨puzzle, key⟩
  rw [← QueryImpl.simulateQ_compose, hch]

section typedWorld

variable [DecidableEq ι]

omit [∀ t, SampleableType (spec.Range t)] [DecidableEq ι] in
/-- Local coins lifted into the hiding adversary's interface, run through a handler that forwards
local coins without touching its state, are the local coins themselves. -/
private lemma run_simulateQ_liftComp_coins {σ α : Type}
    (impl : QueryImpl ((unifSpec + LeftOrRight.spec Msg C) + spec.batch) (StateT σ ProbComp))
    (himpl : ∀ n s, (impl (.inl (.inl n))).run s =
      (·, s) <$> (unifSpec.query n : ProbComp (Fin (n + 1))))
    (oa : ProbComp α) (s : σ) :
    (simulateQ impl (liftComp oa ((unifSpec + LeftOrRight.spec Msg C) + spec.batch))).run s =
      (·, s) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
      rw [liftComp_bind, liftComp_query, simulateQ_bind, StateT.run_bind]
      change (simulateQ impl (liftM (((unifSpec + LeftOrRight.spec Msg C) + spec.batch).query
        (.inl (.inl t))))).run s >>= _ = _
      rw [simulateQ_spec_query, himpl]
      simp [ih, map_bind]

/-- In the typed world, a challenge query of the combined experiment is the challenge query of the
typed hiding experiment in the random oracle model of the typed oracles: the encryption queries
the typed oracles on the typed cache, and the private cache is untouched. -/
private lemma challenge_run_step {Puzzle Key Λ : Type} [DecidableEq Λ]
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) Msg C) (leak : Msg → Λ)
    (puzzle : Puzzle) (key : Key) (b : Bool) (mm : Msg × Msg) (pv : (D →ₒ M).QueryCache)
    (c : spec.QueryCache) :
    (simulateQ E.typedImpl (LeftOrRight.oracle
        (fun msg => simulateQ (typedLift (D := D) (M := M)) (dem.encrypt (puzzle, key) msg))
        leak b mm)).run (c, pv) =
      (fun z => (z.1, (z.2, pv))) <$> (simulateQ spec.romImpl
        (LeftOrRight.oracle (dem.encrypt (puzzle, key)) leak b mm)).run c := by
  rw [LeftOrRight.oracle_apply, LeftOrRight.oracle_apply]
  split_ifs <;> first
    | simp only [simulateQ_map, StateT.run_map]
      rw [E.simulateQ_typedImpl_typedLift_run]
      simp [Functor.map_map]
    | simp

/-- An online step of the adapted adversary, run in the random oracle model of the typed oracles
under the typed hiding handler, has the law of the step of the combined experiment's handler in
the typed world, with the typed and the private caches kept apart. -/
lemma freeOnlineImpl_run_step {Puzzle Key Λ : Type} [DecidableEq Λ]
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) Msg C) (leak : Msg → Λ)
    (puzzle : Puzzle) (key : Key) (b : Bool)
    (t : ((unifSpec + LeftOrRight.spec Msg C) + (D →ₒ M).batch).Domain)
    (pv : (D →ₒ M).QueryCache) (c : spec.QueryCache) :
    (simulateQ (spec.romImpl ∘ₛ ((unifSpec.passthrough +
        LeftOrRight.oracle (dem.encrypt (puzzle, key)) leak b) +
        (QueryImpl.id' spec).liftTarget (OracleComp (unifSpec + spec)))).batch'
      ((E.freeOnlineImpl t).run pv)).run c =ᵈ
      (fun z => ((z.1, z.2.2), z.2.1)) <$>
        ((E.typedImpl ∘ₛ combinedChallengeImpl dem leak puzzle key b).batch' t).run (c, pv) := by
  rcases t with (n | mm) | xs
  · simp only [freeOnlineImpl, QueryImpl.batch'_apply_inl, QueryImpl.apply_compose,
      combinedChallengeImpl, QueryImpl.add_apply_inl, simulateQ_spec_query]
    rw [typedImpl_inl_run]
    simp [OracleSpec.romImpl, QueryImpl.simulateQ_add_liftM_left]
  · simp only [freeOnlineImpl, QueryImpl.batch'_apply_inl, QueryImpl.apply_compose,
      combinedChallengeImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      QueryImpl.passthrough_add, StateT.run_lift, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, StateT.run_bind, StateT.run_pure]
    rw [E.challenge_run_step dem leak puzzle key b mm pv c]
    simp [Functor.map_map]
  · have hround : QueryImpl.batch (fun t => (spec.romImpl ∘ₛ ((unifSpec.passthrough +
        LeftOrRight.oracle (dem.encrypt (puzzle, key)) leak b) +
        (QueryImpl.id' spec).liftTarget (OracleComp (unifSpec + spec)))) (.inr t)) =
          spec.randomOracle.batch := by
      congr 1
      funext t
      simp [OracleSpec.romImpl, QueryImpl.simulateQ_add_liftM_right]
    rw [QueryImpl.batch'_apply_inr, show (fun x => (E.typedImpl ∘ₛ
        combinedChallengeImpl dem leak puzzle key b) (.inr x)) =
        fun x => E.typedHashImpl (.inr x) from funext fun x => by
          simp [combinedChallengeImpl, typedImpl]]
    refine EvalDistEq.trans ?_ ((E.batch_typedHashImpl_run xs c pv).map _).symm
    simp only [freeOnlineImpl, sideDraws, StateT.run_bind, StateT.run_mk, StateT.run_lift,
      bind_assoc, pure_bind, StateT.run_pure, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, QueryImpl.batch'_apply_inr, hround]
    rw [run_simulateQ_liftComp_coins _ (fun n s => by
      simp [OracleSpec.romImpl, run_simulateQ_unifFwdImpl_add_liftM]), bind_map_left]
    simp [map_bind]

/-- In the typed world, the combined experiment has the law of the typed hiding experiment of the
adapted adversary. -/
lemma typedImpl_combinedHidingExperiment_evalDistEq {Puzzle Key Λ : Type} [DecidableEq Λ]
    (tlp : TimeLockPuzzle spec Puzzle Key)
    (dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) Msg C) (leak : Msg → Λ)
    (adv : HidingAdversary (D →ₒ M) Puzzle Msg C) (b : Bool) :
    Prod.fst <$> (simulateQ E.typedImpl (combinedHidingExperiment tlp dem leak adv b)).run (∅, ∅) =ᵈ
      (simulateQ spec.romImpl (tlp.hidingExperiment dem leak (E.adaptHidingAdversary adv) b)).run'
        ∅ := by
  have hpre := simulateQ_run_simulateQ_run_evalDistEq spec.romImpl E.preprocessImpl
    (E.typedImpl ∘ₛ rawLift) (fun t s q => by rw [E.preprocessImpl_run_step]) adv.preprocess ∅ ∅
  simp only [combinedHidingExperiment, hidingExperiment, adaptHidingAdversary, adaptTwoPhase,
    simulateQ_bind,
    StateT.run_bind, StateT.run'_eq, map_bind]
  refine EvalDistEq.trans ?_ (hpre.bind_left _).symm
  rw [← QueryImpl.simulateQ_compose, bind_map_left]
  refine EvalDistEq.bind_right _ fun z => ?_
  obtain ⟨st, c, pv⟩ := z
  simp only [simulateQ_typedImpl_typedLift_run, bind_map_left]
  refine EvalDistEq.bind_right _ fun w => ?_
  obtain ⟨⟨puzzle, key⟩, c'⟩ := w
  dsimp only
  rw [← QueryImpl.simulateQ_compose, QueryImpl.simulateQ_simulateQ_unbatch,
    ← QueryImpl.simulateQ_compose, QueryImpl.simulateQ_simulateQ_unbatch, simulateQ_map,
    StateT.run_map, Functor.map_map]
  refine EvalDistEq.trans ?_ ((simulateQ_run_simulateQ_run_evalDistEq _ E.freeOnlineImpl
    (E.typedImpl ∘ₛ combinedChallengeImpl dem leak puzzle key b).batch'
    (E.freeOnlineImpl_run_step dem leak puzzle key b) (adv.online st puzzle) pv c').map
      _).symm
  simp [Functor.map_map]

/-- **The raw hiding experiment against the typed one, at each hidden bit.** If the generator of a
raw puzzle is the typed generator with every round translated by `roundImpl`, the encryption of a
raw DEM is the typed encryption with every query encoded, and the encoding never clashes, then
the raw hiding experiment of a raw adversary has the law of the typed hiding experiment of its
adapted adversary, in the random oracle model. The hiding advantage is a distance between the
laws at the two hidden bits, so the comparison is an equality of laws rather than a bound on
one event. -/
theorem evalDist_hidingExperiment_adaptHidingAdversary {Puzzle Key Λ : Type} [DecidableEq Λ]
    {tlpRaw : TimeLockPuzzle (D →ₒ M) Puzzle Key} {tlp : TimeLockPuzzle spec Puzzle Key}
    {demRaw : DEMScheme (OracleComp (unifSpec + (D →ₒ M))) (Puzzle × Key) Msg C}
    {dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) Msg C} (leak : Msg → Λ)
    (hgen : tlpRaw.gen = simulateQ E.roundImpl tlp.gen)
    (henc : ∀ key msg, demRaw.encrypt key msg =
      simulateQ (E.encodeImpl ∘ₛ typedLift) (dem.encrypt key msg))
    (hclash : ∀ c, ¬ E.Clash c) (adv : HidingAdversary (D →ₒ M) Puzzle Msg C) (b : Bool) :
    (ProbCompRuntime.rom (D →ₒ M)).evalDist (tlpRaw.hidingExperiment demRaw leak adv b) =
      (ProbCompRuntime.rom spec).evalDist
        (tlp.hidingExperiment dem leak (E.adaptHidingAdversary adv) b) := by
  rw [ProbCompRuntime.rom_evalDist, ProbCompRuntime.rom_evalDist]
  have hle : ∀ x : Bool,
      Pr{let y ← (simulateQ (D →ₒ M).romImpl (tlpRaw.hidingExperiment demRaw leak adv b)).run' ∅}[
        y = x] ≤
      Pr{let y ← (simulateQ spec.romImpl
        (tlp.hidingExperiment dem leak (E.adaptHidingAdversary adv) b)).run' ∅}[y = x] := by
    intro x
    rw [← (E.typedImpl_combinedHidingExperiment_evalDistEq tlp dem leak adv b).prEvent_eq,
      ← E.simulateQ_encodeImpl_combinedHidingExperiment leak hgen henc adv b, StateT.run'_eq,
      prEvent_map, prEvent_map]
    refine (E.prEvent_simulateQ_romImpl_encodeImpl_run_le _ (· = x)).trans (le_of_eq ?_)
    simp [hclash]
  exact evalDist_eq_of_prEvent_le (hle true) (hle false)

/-- **The raw hiding advantage is the typed hiding advantage of the adapted adversary**, for a raw
puzzle and a raw DEM that refine a typed puzzle and a typed DEM through an encoding that never
clashes. -/
theorem hidingAdvantage_eq_hidingAdvantage_adaptHidingAdversary {Puzzle Key Λ : Type}
    [DecidableEq Λ] {tlpRaw : TimeLockPuzzle (D →ₒ M) Puzzle Key}
    {tlp : TimeLockPuzzle spec Puzzle Key}
    {demRaw : DEMScheme (OracleComp (unifSpec + (D →ₒ M))) (Puzzle × Key) Msg C}
    {dem : DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) Msg C} (leak : Msg → Λ)
    (hgen : tlpRaw.gen = simulateQ E.roundImpl tlp.gen)
    (henc : ∀ key msg, demRaw.encrypt key msg =
      simulateQ (E.encodeImpl ∘ₛ typedLift) (dem.encrypt key msg))
    (hclash : ∀ c, ¬ E.Clash c) (adv : HidingAdversary (D →ₒ M) Puzzle Msg C) :
    hidingAdvantage tlpRaw demRaw leak adv =
      hidingAdvantage tlp dem leak (E.adaptHidingAdversary adv) := by
  simp only [hidingAdvantage_eq,
    E.evalDist_hidingExperiment_adaptHidingAdversary leak hgen henc hclash]

end typedWorld

end Experiment

end OracleComp.RandomOracleEncoding
