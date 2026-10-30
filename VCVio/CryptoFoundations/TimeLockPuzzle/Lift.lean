/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle

/-!
# Lifting a time-lock puzzle and simulating a side oracle

A time-lock puzzle over oracles `spec` runs unchanged over any larger oracle specification
`superSpec` containing `spec` (`spec ⊂ₒ superSpec`): the generator and the solver are lifted query
by query, and each round becomes the round of the translated points, so the honest budgets carry
over.

An adversary against a puzzle over the sum `spec + side`, where `side` is an independent oracle,
is turned into an adversary against the puzzle over `spec` by answering `side` itself, from a
private lazy random oracle whose cache passes from the preprocessing phase to the online phase.
One online round of the adversary may mix points of `spec` and of `side`. Its `side` points are
drawn from the private cache, with local coins of the free summand, its `spec` points are
submitted as one round, in their original order and with repetitions, and the answer tuple of the
mixed round is reassembled position by position (`TimeLockPuzzle.batchMerge`). So one round of
the adversary is at most one round of the simulation, holding only the round's `spec` points.

## Main definitions

* `TimeLockPuzzle.liftSpec`: the puzzle over a larger oracle specification.
* `TimeLockPuzzle.batchMerge`: the answers to a mixed round of `spec + side`, from the answers to
  its `spec` points and to its `side` points.
* `TimeLockPuzzle.sideDraws`: the private lazy random oracle for `side` at the points of a list,
  drawing coins from the free summand.
* `TimeLockPuzzle.sidePreprocessImpl`, `TimeLockPuzzle.sideOnlineImpl`: the handlers answering
  `side` privately in the preprocessing and in the online phase.
* `TimeLockPuzzle.TwoPhaseAdversary.simulateSide`: the adversary against `spec` simulating an
  adversary against `spec + side`.

## Main statements

* `TimeLockPuzzle.IsGenQueryBound.liftSpec`, `TimeLockPuzzle.IsSolveQueryBound.liftSpec`: lifting
  keeps the honest budgets.
* `TimeLockPuzzle.isOnlineQueryBound_sideDraws_run`: the private draws submit no round.
* `TimeLockPuzzle.isOnlineQueryBound_sideOnlineImpl_inr_run`: a mixed round is simulated by one
  round holding its `spec` points.
* `TimeLockPuzzle.TwoPhaseAdversary.isQueryBound_simulateSide`: the simulation keeps the
  preprocessing budget and the online budget of rounds and points.
-/

public section

open OracleSpec OracleComp

namespace TimeLockPuzzle

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {Puzzle Key : Type}

/-! ## Lifting along a `SubSpec` -/

/-- The puzzle over a larger oracle specification `superSpec ⊇ spec`: the generator and the
solver lifted query by query along `spec ⊂ₒ superSpec`, each round becoming the round of its
translated points. -/
@[expose]
def liftSpec (tlp : TimeLockPuzzle spec Puzzle Key) (superSpec : OracleSpec.{0, 0} ι')
    [spec ⊂ₒ superSpec] : TimeLockPuzzle superSpec Puzzle Key where
  gen := liftComp tlp.gen (unifSpec + superSpec.batch)
  solve puzzle := liftComp (tlp.solve puzzle) (unifSpec + superSpec.batch)

/-- The lifted generator submits as many rounds and points as the generator. -/
theorem IsGenQueryBound.liftSpec {tlp : TimeLockPuzzle spec Puzzle Key}
    {superSpec : OracleSpec.{0, 0} ι'} [spec ⊂ₒ superSpec] {b : ℕ × ℕ}
    (h : tlp.IsGenQueryBound b) : (tlp.liftSpec superSpec).IsGenQueryBound b :=
  IsOnlineQueryBound.liftComp h

/-- The lifted solver submits as many rounds and points as the solver. -/
theorem IsSolveQueryBound.liftSpec {tlp : TimeLockPuzzle spec Puzzle Key}
    {superSpec : OracleSpec.{0, 0} ι'} [spec ⊂ₒ superSpec] {b : ℕ × ℕ}
    (h : tlp.IsSolveQueryBound b) : (tlp.liftSpec superSpec).IsSolveQueryBound b :=
  fun puzzle => IsOnlineQueryBound.liftComp (h puzzle)

/-! ## Mixed rounds -/

variable {side : OracleSpec.{0, 0} ι'}

/-- The answers to a mixed round `ts` of `spec + side`, reassembled from the answers `us` to its
`spec` points and the answers `vs` to its `side` points, each list in the order of `ts`: position
by position, a `spec` point takes the next answer of `us` and a `side` point the next answer of
`vs`. -/
@[expose]
def batchMerge : (ts : List (ι ⊕ ι')) → spec.batch.Range (ts.filterMap Sum.getLeft?) →
    side.batch.Range (ts.filterMap Sum.getRight?) → (spec + side).batch.Range ts
  | [], _, _ => batchNil
  | .inl _ :: ts, us, vs => batchCons (us ⟨0, by simp⟩) (batchMerge ts (fun j => us j.succ) vs)
  | .inr _ :: ts, us, vs => batchCons (vs ⟨0, by simp⟩) (batchMerge ts us (fun j => vs j.succ))

/-! ## Answering the side oracle privately -/

section Side

variable [DecidableEq ι'] [∀ t, SampleableType (side.Range t)]

/-- The private lazy random oracle for `side` at every point of a list, in order and with
repetitions, on the private cache. Its local coins are queries to the free summand, embedded along
`unifSpec → free`, so it submits no round (`isOnlineQueryBound_sideDraws_run`). -/
@[expose]
def sideDraws {τ : Type} {free : OracleSpec.{0, 0} τ}
    [MonadLiftT (OracleQuery unifSpec) (OracleQuery free)] (ts : List ι') :
    StateT side.QueryCache (OracleComp (free + spec.batch)) (side.batch.Range ts) :=
  StateT.mk fun c => liftComp ((side.randomOracle.batch ts).run c) (free + spec.batch)

/-- The private draws submit no round and no point, from every cache. -/
theorem isOnlineQueryBound_sideDraws_run {τ : Type} {free : OracleSpec.{0, 0} τ}
    [MonadLiftT (OracleQuery unifSpec) (OracleQuery free)] (ts : List ι')
    (c : side.QueryCache) (b : ℕ × ℕ) :
    IsOnlineQueryBound ((sideDraws (spec := spec) (free := free) ts).run c) b :=
  isOnlineQueryBound_liftComp _ b

/-- The preprocessing handler answering `side` privately: local coins and queries to `spec` pass
through, and a query to `side` is answered by the private lazy random oracle, whose local coins
are local coins of the preprocessing phase. -/
@[expose]
def sidePreprocessImpl :
    QueryImpl (unifSpec + (spec + side)) (StateT side.QueryCache (OracleComp (unifSpec + spec)))
  | .inl n => StateT.lift (liftM ((unifSpec + spec).query (.inl n)))
  | .inr (.inl t) => StateT.lift (liftM ((unifSpec + spec).query (.inr t)))
  | .inr (.inr t) => StateT.mk fun c => liftComp ((side.randomOracle t).run c) (unifSpec + spec)

/-- The online handler answering `side` privately: queries to the free summand pass through, and
a mixed round draws its `side` points from the private cache (`sideDraws`), submits its `spec`
points as one round, and reassembles the answer tuple (`batchMerge`). -/
@[expose]
def sideOnlineImpl {τ : Type} {free : OracleSpec.{0, 0} τ}
    [MonadLiftT (OracleQuery unifSpec) (OracleQuery free)] :
    QueryImpl (free + (spec + side).batch)
      (StateT side.QueryCache (OracleComp (free + spec.batch)))
  | .inl n => StateT.lift (liftM ((free + spec.batch).query (.inl n)))
  | .inr ts => do
      let vs ← sideDraws (ts.filterMap Sum.getRight?)
      let us ← StateT.lift (liftM ((free + spec.batch).query (.inr (ts.filterMap Sum.getLeft?))))
      return batchMerge ts us vs

/-- **Simulating an independent side oracle.** The adversary against `spec` that runs `adv`, an
adversary against `spec + side`, answering `side` from a private lazy random oracle: the
preprocessing phase starts it from the empty cache and passes the cache to the online phase in its
state, so an answer drawn in one phase is the answer in the other. -/
@[expose]
def TwoPhaseAdversary.simulateSide {τ : Type} {free : OracleSpec.{0, 0} τ}
    [MonadLiftT (OracleQuery unifSpec) (OracleQuery free)] {Out : Type}
    (adv : TwoPhaseAdversary free (spec + side) Puzzle Out) :
    TwoPhaseAdversary free spec Puzzle Out where
  State := adv.State × side.QueryCache
  preprocess := (simulateQ sidePreprocessImpl adv.preprocess).run ∅
  online σ puzzle := (simulateQ sideOnlineImpl (adv.online σ.1 puzzle)).run' σ.2

/-! ### Budgets -/

omit [DecidableEq ι'] [∀ t, SampleableType (side.Range t)] in
/-- Local coins lifted into the preprocessing phase make no query to `spec`. -/
private lemma isPreprocessingQueryBound_liftComp {α : Type} (oa : ProbComp α) :
    IsPreprocessingQueryBound (liftComp oa (unifSpec + spec)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
      rw [liftComp_bind, liftComp_query]
      exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp, fun u => by simpa using ih u⟩

/-- A step of the preprocessing handler makes at most one query to `spec`, and only for a query
to `spec + side`. -/
lemma isPreprocessingQueryBound_sidePreprocessImpl_run (t : (unifSpec + (spec + side)).Domain)
    (c : side.QueryCache) :
    IsPreprocessingQueryBound ((sidePreprocessImpl t).run c) (if t.isRight then 1 else 0) := by
  rcases t with n | t | t
  · simp only [sidePreprocessImpl, Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte,
      StateT.run_lift]
    exact isQueryBoundP_bind_zero _ _ (by simp) fun _ => isQueryBoundP_pure _ _ _
  · simp only [sidePreprocessImpl, Sum.isRight_inr, ↓reduceIte, StateT.run_lift]
    rw [← Nat.add_zero 1]
    exact isQueryBoundP_bind (by simp) fun _ _ => isQueryBoundP_pure _ _ _
  · simp only [sidePreprocessImpl, Sum.isRight_inr, ↓reduceIte]
    exact (isPreprocessingQueryBound_liftComp _).mono (Nat.zero_le 1)

/-- A mixed round `ts` is simulated by one round holding its `spec` points and no others: its
`side` points cost nothing. -/
theorem isOnlineQueryBound_sideOnlineImpl_inr_run {τ : Type} {free : OracleSpec.{0, 0} τ}
    [MonadLiftT (OracleQuery unifSpec) (OracleQuery free)] (ts : List (ι ⊕ ι'))
    (c : side.QueryCache) :
    IsOnlineQueryBound ((sideOnlineImpl (spec := spec) (free := free) (.inr ts)).run c)
      (1, (ts.filterMap Sum.getLeft?).length) := by
  simp only [sideOnlineImpl, StateT.run_bind]
  refine isOnlineQueryBound_bind_le (0, 0) (1, (ts.filterMap Sum.getLeft?).length)
    (isOnlineQueryBound_sideDraws_run _ _ _) (fun z => ?_) ⟨by omega, by omega⟩
  rw [StateT.run_lift, bind_assoc]
  refine isOnlineQueryBound_bind_le (1, (ts.filterMap Sum.getLeft?).length) (0, 0) ?_
    (fun _ => ?_) ⟨le_rfl, le_rfl⟩
  · rw [IsOnlineQueryBound, isQueryBound_query_iff]
    simp
  · simp only [pure_bind, StateT.run_pure]
    exact isOnlineQueryBound_pure _ _

/-- A step of the online handler costs at most the query it answers: nothing for a query to the
free summand, and at most one round of at most as many points for a round. -/
theorem isOnlineQueryBound_sideOnlineImpl_run {τ : Type} {free : OracleSpec.{0, 0} τ}
    [MonadLiftT (OracleQuery unifSpec) (OracleQuery free)]
    (t : (free + (spec + side).batch).Domain) (c : side.QueryCache) :
    IsOnlineQueryBound ((sideOnlineImpl (spec := spec) t).run c) (onlineStep t) := by
  rcases t with n | ts
  · simp only [sideOnlineImpl, onlineStep_inl, StateT.run_lift]
    exact (isOnlineQueryBound_query_bind_inl_iff _ _ _).2 fun _ => isOnlineQueryBound_pure _ _
  · exact (isOnlineQueryBound_sideOnlineImpl_inr_run ts c).mono
      (Prod.mk_le_mk.mpr ⟨le_rfl, List.length_filterMap_le _ _⟩)

/-- **The simulation keeps the budgets.** If `adv` makes at most `Q` preprocessing queries to
`spec + side` and its online phase submits at most `b.1` rounds holding at most `b.2` points, then
`adv.simulateSide` makes at most `Q` preprocessing queries to `spec` and its online phase submits at
most `b.1` rounds holding at most `b.2` points. Queries to `side` are answered privately with local
coins and cost nothing, and each round of `adv` becomes one round holding only its `spec` points. -/
theorem TwoPhaseAdversary.isQueryBound_simulateSide {τ : Type} {free : OracleSpec.{0, 0} τ}
    [MonadLiftT (OracleQuery unifSpec) (OracleQuery free)] {Out : Type}
    {adv : TwoPhaseAdversary free (spec + side) Puzzle Out} {Q : ℕ} {b : ℕ × ℕ}
    (h : adv.IsQueryBound Q b) : adv.simulateSide.IsQueryBound Q b := by
  refine ⟨h.1.simulateQ_run_StateT_of_step isPreprocessingQueryBound_sidePreprocessImpl_run ∅,
    fun σ puzzle => ?_⟩
  have hrun : IsOnlineQueryBound
      ((simulateQ sideOnlineImpl (adv.online σ.1 puzzle)).run σ.2) b :=
    IsQueryBound.simulateQ_run_of_step (combine := (· + ·)) (mapBudget := id)
      (stepBudget := fun t _ => onlineStep t) (h.2 σ.1 puzzle) isOnlineQueryBound_bind
      (fun t _ c _ => isOnlineQueryBound_sideOnlineImpl_run t c)
      (fun t b hb => by
        rcases t with n | ts
        · simp
        · simp only [onlineCanQuery_inr] at hb
          refine Prod.ext ?_ ?_ <;> simp <;> omega) σ.2
  exact (isQueryBound_map_iff _ _ _ _ _).2 hrun

end Side

end TimeLockPuzzle
