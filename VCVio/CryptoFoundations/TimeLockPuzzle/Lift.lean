/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle
import VCVio.OracleComp.SimSemantics.StateT.Measure

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
* `TimeLockPuzzle.evalDist_guessExperiment_liftSpec_add`: in the random oracle model, the guess
  experiment of the puzzle lifted to `spec + side` against `adv` has the law of the guess
  experiment of the puzzle against `adv.simulateSide`.
* `TimeLockPuzzle.delayAdvantage_liftSpec_add`, `TimeLockPuzzle.delaySecure_liftSpec_add`: delay
  security transfers to the puzzle lifted to an independent sum.
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

/-! ## Security for an independent sum

In the random oracle model on `spec + side`, the two summands are independent lazy random oracles
on a product cache (`OracleComp.map_run_simulateQ_add_parallelStateT_randomOracle`). The lifted
generator only touches the `spec` cache
(`QueryImpl.run_simulateQ_add_parallelStateT_batch_liftComp`). A mixed round answered point by
point has, in distribution, the law of its `side` points drawn first and its `spec` points
answered after (`TimeLockPuzzle.run_batch_parallelStateT_evalDistEq`), which is how
`sideOnlineImpl` answers it. -/

/-- **A mixed round against two handlers side by side.** A mixed round `ts` of `spec + side`,
answered point by point by `impl₁` and `impl₂` side by side, has the law of answering its `side`
points by `impl₂`, then its `spec` points by `impl₁`, each in order, and reassembling the answer
tuple with `batchMerge`. -/
theorem run_batch_parallelStateT_evalDistEq {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl side (StateT σ₂ ProbComp))
    (ts : List (ι ⊕ ι')) (s₁ : σ₁) (s₂ : σ₂) :
    ((QueryImpl.parallelStateT impl₁ impl₂).batch ts).run (s₁, s₂) =ᵈ
      (impl₂.batch (ts.filterMap Sum.getRight?)).run s₂ >>= fun z =>
        (impl₁.batch (ts.filterMap Sum.getLeft?)).run s₁ >>= fun y =>
          pure (batchMerge ts y.1 z.1, (y.2, z.2)) := by
  induction ts generalizing s₁ s₂ with
  | nil => exact EvalDistEq.rfl
  | cons t ts ih =>
    rcases t with t | t
    · dsimp only [QueryImpl.batch_cons, StateT.run_bind, List.filterMap, Sum.getLeft?,
        Sum.getRight?]
      rw [show (QueryImpl.parallelStateT impl₁ impl₂ (.inl t)).run (s₁, s₂) =
        Prod.map id (·, s₂) <$> (impl₁ t).run s₁ from rfl, bind_map_left]
      dsimp only [Prod.map, id]
      refine (EvalDistEq.bind_right _ fun (a : spec.Range t × σ₁) =>
        (ih a.2 s₂).bind_left _).trans ?_
      simp only [bind_assoc, pure_bind, StateT.run_pure]
      exact EvalDistEq.bind_bind_swap _ _ _
    · dsimp only [QueryImpl.batch_cons, StateT.run_bind, List.filterMap, Sum.getLeft?,
        Sum.getRight?]
      rw [show (QueryImpl.parallelStateT impl₁ impl₂ (.inr t)).run (s₁, s₂) =
        Prod.map id (s₁, ·) <$> (impl₂ t).run s₂ from rfl, bind_map_left]
      dsimp only [Prod.map, id]
      refine (EvalDistEq.bind_right _ fun (a : side.Range t × σ₂) =>
        (ih s₁ a.2).bind_left _).trans ?_
      simp only [bind_assoc, pure_bind, StateT.run_pure]
      exact EvalDistEq.rfl

section Security

variable [DecidableEq ι] [DecidableEq ι'] [∀ t, SampleableType (spec.Range t)]
  [∀ t, SampleableType (side.Range t)]

/-- The random oracle model on `spec + side` with the caches of the two summands kept apart. -/
private noncomputable abbrev sumRomImpl :
    QueryImpl (unifSpec + (spec + side)) (StateT (spec.QueryCache × side.QueryCache) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (spec.QueryCache × side.QueryCache) ProbComp) +
    QueryImpl.parallelStateT spec.randomOracle side.randomOracle

/-- A preprocessing step of the simulation, run in the random oracle model on `spec`, is the step
of the random oracle model on `spec + side` with the two caches kept apart. -/
private lemma sidePreprocessImpl_run_step (t : (unifSpec + (spec + side)).Domain)
    (sc : side.QueryCache) (c : spec.QueryCache) :
    (simulateQ spec.romImpl ((sidePreprocessImpl t).run sc)).run c =
      (fun z => ((z.1, z.2.2), z.2.1)) <$>
        ((sumRomImpl (spec := spec) (side := side)) t).run (c, sc) := by
  rcases t with n | t | t
  · simp [sidePreprocessImpl, unifFwdImpl]
  · simp only [sidePreprocessImpl, StateT.run_lift, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, OracleSpec.romImpl_apply_inr]
    rw [show (sumRomImpl (spec := spec) (side := side) (.inr (.inl t))).run (c, sc) =
      Prod.map id (·, sc) <$> (spec.randomOracle t).run c from rfl, Functor.map_map,
      bind_pure_comp]
    rfl
  · simp only [sidePreprocessImpl, StateT.run_mk]
    rw [roSim.simulateQ_liftComp, unifFwdImpl.simulateQ_run,
      show (sumRomImpl (spec := spec) (side := side) (.inr (.inr t))).run (c, sc) =
        Prod.map id (c, ·) <$> (side.randomOracle t).run sc from rfl, Functor.map_map]
    rfl

/-- An online step of the simulation, run in the random oracle model on `spec`, has the law of the
step of the random oracle model on `spec + side` with the two caches kept apart. -/
private lemma sideOnlineImpl_run_step (t : (unifSpec + (spec + side).batch).Domain)
    (sc : side.QueryCache) (c : spec.QueryCache) :
    (simulateQ (unifFwdImpl spec + spec.randomOracle.batch) ((sideOnlineImpl t).run sc)).run c =ᵈ
      (fun z => ((z.1, z.2.2), z.2.1)) <$>
        ((sumRomImpl (spec := spec) (side := side)).batch' t).run (c, sc) := by
  rcases t with n | ts
  · simp [sideOnlineImpl, unifFwdImpl]
  · refine EvalDistEq.trans ?_ ((run_batch_parallelStateT_evalDistEq _ _ ts c sc).map _).symm
    simp only [add_apply_inr, sideOnlineImpl, sideDraws, liftComp_eq_liftM,
      bind_pure_comp, StateT.run_bind, StateT.run_mk, StateT.run_map, StateT.run_lift,
      Functor.map_map, simulateQ_bind, simulateQ_map, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, QueryImpl.add_apply_inr, id_map, map_bind]
    rw [QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run, bind_map_left]

/-- **Delay security for an independent sum.** In the random oracle model, the guess experiment
of the puzzle lifted to `spec + side` against `adv` has the law of the guess experiment of the
puzzle against `adv.simulateSide`, for outputs of any type. The free summand is `unifSpec`, the
free summand of `guessExperiment`. -/
theorem evalDist_guessExperiment_liftSpec_add {Out : Type} (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : TwoPhaseAdversary unifSpec (spec + side) Puzzle Out) :
    (simulateQ (spec + side).romImpl ((tlp.liftSpec (spec + side)).guessExperiment adv)).run' ∅ =ᵈ
      (simulateQ spec.romImpl (tlp.guessExperiment adv.simulateSide)).run' ∅ := by
  have hsplit : (simulateQ (spec + side).romImpl
      ((tlp.liftSpec (spec + side)).guessExperiment adv)).run' ∅ =
      (simulateQ sumRomImpl ((tlp.liftSpec (spec + side)).guessExperiment adv)).run' (∅, ∅) := by
    have h := map_run_simulateQ_add_parallelStateT_randomOracle
      (QueryImpl.ofLift unifSpec ProbComp) ((tlp.liftSpec (spec + side)).guessExperiment adv)
      (∅, ∅)
    rw [QueryCache.addEquiv_empty] at h
    rw [StateT.run'_eq, StateT.run'_eq]
    exact (congrArg (Prod.fst <$> ·) h).symm.trans (by rw [Functor.map_map]; rfl)
  rw [hsplit]
  have hpre := simulateQ_run_simulateQ_run_evalDistEq spec.romImpl sidePreprocessImpl
    sumRomImpl (fun t s q => by rw [sidePreprocessImpl_run_step]) adv.preprocess ∅ ∅
  simp only [guessExperiment, liftSpec, TwoPhaseAdversary.simulateSide, simulateQ_bind,
    StateT.run_bind, StateT.run'_eq, map_bind]
  refine EvalDistEq.trans ?_ (hpre.bind_left _).symm
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun z => ?_
  obtain ⟨st, c, sc⟩ := z
  have hgen : (simulateQ sumRomImpl (simulateQ (spec + side).unbatch
      (liftComp tlp.gen (unifSpec + (spec + side).batch)))).run (c, sc) =
      Prod.map id (·, sc) <$> (simulateQ spec.romImpl (simulateQ spec.unbatch tlp.gen)).run c := by
    rw [QueryImpl.simulateQ_simulateQ_unbatch, simulateQ_romImpl_simulateQ_unbatch]
    exact QueryImpl.run_simulateQ_add_parallelStateT_batch_liftComp _ _ _ _ _ _
  simp only [hgen, bind_map_left]
  refine EvalDistEq.bind_right _ fun w => ?_
  simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map, id, simulateQ_map,
    StateT.run_map, QueryImpl.simulateQ_simulateQ_unbatch, bind_map_left]
  refine EvalDistEq.trans ?_ ((simulateQ_run_simulateQ_run_evalDistEq _ sideOnlineImpl
    sumRomImpl.batch' sideOnlineImpl_run_step (adv.online st w.1.1) sc w.2).bind_left _).symm
  rw [bind_map_left]

/-- The delay advantage of `adv` against the puzzle lifted to `spec + side` is the delay advantage
of `adv.simulateSide` against the puzzle. -/
theorem delayAdvantage_liftSpec_add [DecidableEq Key] (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary (spec + side) Puzzle Key) :
    (tlp.liftSpec (spec + side)).delayAdvantage adv = tlp.delayAdvantage adv.simulateSide := by
  rw [delayAdvantage_eq_prEvent_guessExperiment, delayAdvantage_eq_prEvent_guessExperiment]
  exact (evalDist_guessExperiment_liftSpec_add tlp adv).prEvent_eq _

open scoped ENNReal in
/-- **Delay security transfers to an independent sum.** If the puzzle is delay secure against
adversaries with at most `Q` preprocessing queries and an online budget `b`, so is the puzzle
lifted to `spec + side`: the simulation of an adversary against the lifted puzzle keeps its
budgets (`TwoPhaseAdversary.isQueryBound_simulateSide`) and its advantage. -/
theorem delaySecure_liftSpec_add [DecidableEq Key] {tlp : TimeLockPuzzle spec Puzzle Key}
    {Q : ℕ} {b : ℕ × ℕ} {ε : ℝ≥0∞} (h : tlp.DelaySecure Q b ε) :
    (tlp.liftSpec (spec + side)).DelaySecure Q b ε := fun adv hadv =>
  (delayAdvantage_liftSpec_add tlp adv).trans_le
    (h _ (TwoPhaseAdversary.isQueryBound_simulateSide hadv))

end Security

end TimeLockPuzzle
