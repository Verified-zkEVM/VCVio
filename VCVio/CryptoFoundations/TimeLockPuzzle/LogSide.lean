/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle.Lift

/-!
# Logging the side points of a two-phase adversary

An adversary against a time-lock puzzle over a sum `spec + side` is instrumented to also return
the points of `side` it queried, in both phases, in the order of its queries and with repetitions:
one point per preprocessing query to `side`, and the `side` points of each online round in the
order of the round. The instrumented adversary queries the same oracles, makes the same queries,
and is within the same budgets, so its run, forgetting the log, is the run of the adversary.

For a puzzle over `spec` lifted to `spec + side`, whose generator never queries `side`, the log
of the random-oracle run of the delay experiment is exactly the set of `side` points in the final
cache, beside those cached initially. So an event on the `side` points the random oracle was asked
during the experiment is an event on the output of the instrumented adversary.

## Main definitions

* `TimeLockPuzzle.sideLogPreImpl`, `TimeLockPuzzle.sideLogOnImpl`: the handlers passing every
  query through and appending its `side` points to a log, in the preprocessing and in the online
  phase.
* `TimeLockPuzzle.TwoPhaseAdversary.logSide`: the adversary that also returns its log of `side`
  points, carried from the preprocessing phase to the online phase in its state.

## Main statements

* `TimeLockPuzzle.TwoPhaseAdversary.isQueryBound_logSide`: the instrumentation keeps the budgets.
* `TimeLockPuzzle.map_guessExperiment_logSide`: forgetting the log, the delay experiment against
  the instrumented adversary is the delay experiment against the adversary.
* `TimeLockPuzzle.length_le_of_mem_support_guessExperiment_logSide`: the log holds at most
  `Q + b.2` points for preprocessing budget `Q` and online budget `b`.
* `TimeLockPuzzle.cache_inr_isSome_iff_or_mem_log`, `TimeLockPuzzle.cache_inr_isSome_iff_mem_log`:
  in the random-oracle run of the delay experiment of a lifted puzzle against the instrumented
  adversary, a `side` point is cached at the end exactly when it was cached initially or is in the
  log; from the empty cache, exactly when it is in the log.
-/

public section

open OracleSpec OracleComp

namespace TimeLockPuzzle

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {side : OracleSpec.{0, 0} ι'}
  {Puzzle Key : Type}

/-! ## The instrumented adversary -/

/-- The preprocessing handler logging `side` points: every query passes through unchanged, and a
query to `side` appends its point to the log. -/
@[expose]
def sideLogPreImpl : QueryImpl (unifSpec + (spec + side))
    (StateT (List ι') (OracleComp (unifSpec + (spec + side))))
  | .inl n => StateT.lift (liftM ((unifSpec + (spec + side)).query (.inl n)))
  | .inr (.inl t) => StateT.lift (liftM ((unifSpec + (spec + side)).query (.inr (.inl t))))
  | .inr (.inr t) => do
      modify (· ++ [t])
      StateT.lift (liftM ((unifSpec + (spec + side)).query (.inr (.inr t))))

/-- The online handler logging `side` points: every query passes through unchanged, and a round
appends its `side` points to the log, in the order of the round and with repetitions. -/
@[expose]
def sideLogOnImpl {τ : Type} {free : OracleSpec.{0, 0} τ} :
    QueryImpl (free + (spec + side).batch)
      (StateT (List ι') (OracleComp (free + (spec + side).batch)))
  | .inl n => StateT.lift (liftM ((free + (spec + side).batch).query (.inl n)))
  | .inr ts => do
      modify (· ++ ts.filterMap Sum.getRight?)
      StateT.lift (liftM ((free + (spec + side).batch).query (.inr ts)))

/-- **Logging the side points.** The adversary that runs `adv`, with the same oracles and the same
queries, and also returns the `side` points it queried in both phases, in order and with
repetitions: the preprocessing phase starts the log empty and passes it to the online phase in
its state. -/
@[expose]
def TwoPhaseAdversary.logSide {τ : Type} {free : OracleSpec.{0, 0} τ} {Out : Type}
    (adv : TwoPhaseAdversary free (spec + side) Puzzle Out) :
    TwoPhaseAdversary free (spec + side) Puzzle (Out × List ι') where
  State := adv.State × List ι'
  preprocess := (simulateQ sideLogPreImpl adv.preprocess).run []
  online σ puzzle := (simulateQ sideLogOnImpl (adv.online σ.1 puzzle)).run σ.2

/-- A step of the preprocessing handler makes its query and appends the `side` point of the
query, if any, to the log. -/
lemma sideLogPreImpl_run (t : (unifSpec + (spec + side)).Domain) (s : List ι') :
    (sideLogPreImpl t).run s = (liftM ((unifSpec + (spec + side)).query t) >>= fun u =>
      pure (u, s ++ (t.getRight?.bind Sum.getRight?).toList)) := by
  rcases t with n | t | t <;> simp [sideLogPreImpl]

/-- A step of the online handler makes its query and appends the `side` points of the query, if
it is a round, to the log. -/
lemma sideLogOnImpl_run {τ : Type} {free : OracleSpec.{0, 0} τ}
    (t : (free + (spec + side).batch).Domain) (s : List ι') :
    (sideLogOnImpl t).run s = (liftM ((free + (spec + side).batch).query t) >>= fun u =>
      pure (u, s ++ (t.getRight?.map (·.filterMap Sum.getRight?)).getD [])) := by
  rcases t with n | ts <;> simp [sideLogOnImpl]

/-! ## Budgets and the run -/

/-- **The instrumentation keeps the budgets.** If `adv` makes at most `Q` preprocessing queries
and its online phase submits at most `b.1` rounds holding at most `b.2` points, then so does
`adv.logSide`: logging makes no query. -/
theorem TwoPhaseAdversary.isQueryBound_logSide {τ : Type} {free : OracleSpec.{0, 0} τ}
    {Out : Type} {adv : TwoPhaseAdversary free (spec + side) Puzzle Out} {Q : ℕ} {b : ℕ × ℕ}
    (h : adv.IsQueryBound Q b) : adv.logSide.IsQueryBound Q b := by
  refine ⟨h.1.simulateQ_run_StateT_of_step (fun t s => ?_) [], fun σ puzzle => ?_⟩
  · rw [sideLogPreImpl_run]
    exact (isQueryBoundP_bind (n := if t.isRight then 1 else 0) (m := 0)
      ((isQueryBoundP_query_iff _ _ _).2 fun ht => by simp [ht])
      fun _ _ => isQueryBoundP_pure _ _ _).mono (by simp)
  · refine IsQueryBound.simulateQ_run_of_step (combine := (· + ·)) (mapBudget := id)
      (stepBudget := fun t _ => onlineStep t) (h.2 σ.1 puzzle) isOnlineQueryBound_bind
      (fun t _ s _ => ?_)
      (fun t b hb => by
        rcases t with n | ts
        · simp
        · simp only [onlineCanQuery_inr] at hb
          refine Prod.ext ?_ ?_ <;> simp <;> omega) σ.2
    rw [sideLogOnImpl_run, ← add_zero (onlineStep t)]
    refine isOnlineQueryBound_bind ?_ fun _ => isOnlineQueryBound_pure _ _
    rcases t with n | ts
    · exact (isQueryBound_query_iff _ _ _ _).2 trivial
    · exact (isQueryBound_query_iff _ _ _ _).2 (by simp)

/-- **The instrumentation does not change the run.** Forgetting the log, the delay experiment
against `adv.logSide` is the delay experiment against `adv`. -/
theorem map_guessExperiment_logSide {Out : Type} (tlp : TimeLockPuzzle (spec + side) Puzzle Key)
    (adv : TwoPhaseAdversary unifSpec (spec + side) Puzzle Out) :
    (fun z => (z.1.1, z.2)) <$> tlp.guessExperiment adv.logSide = tlp.guessExperiment adv := by
  have hpre : Prod.fst <$> (simulateQ sideLogPreImpl adv.preprocess).run [] = adv.preprocess :=
    StateT_run'_simulateQ_eq_self _ (fun t s => by simp [StateT.run'_eq, sideLogPreImpl_run]) _ _
  have hon : ∀ σ puzzle s,
      Prod.fst <$> (simulateQ sideLogOnImpl (adv.online σ puzzle)).run s = adv.online σ puzzle :=
    fun σ puzzle s => StateT_run'_simulateQ_eq_self _
      (fun t s => by simp [StateT.run'_eq, sideLogOnImpl_run]) _ _
  conv_rhs => rw [guessExperiment, ← hpre]
  simp only [guessExperiment, TwoPhaseAdversary.logSide, map_bind, map_pure, bind_map_left]
  refine bind_congr fun σ => bind_congr fun pk => ?_
  conv_rhs => rw [← hon σ.1 pk.1 σ.2]
  simp [simulateQ_map]

/-! ## The length of the log -/

/-- A preprocessing phase with at most `Q` queries to `spec + side` appends at most `Q` points to
the log. -/
lemma length_le_of_mem_support_run_simulateQ_sideLogPreImpl {α : Type}
    {oa : OracleComp (unifSpec + (spec + side)) α} {Q : ℕ} (h : IsPreprocessingQueryBound oa Q)
    (s : List ι') {z : α × List ι'} (hz : z ∈ support ((simulateQ sideLogPreImpl oa).run s)) :
    z.2.length ≤ s.length + Q := by
  induction oa using OracleComp.inductionOn generalizing Q s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  | query_bind t k ih =>
    change IsQueryBoundP _ _ _ at h
    rw [isQueryBoundP_query_bind_iff] at h
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hk := ih y.1 (h.2 y.1) y.2 hz
    rw [sideLogPreImpl_run] at hy
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨u, -, rfl⟩ := hy
    rcases t with n | t | t
    · simpa using hk
    · have hQ := h.1
      simp at hQ hk
      omega
    · have hQ := h.1
      simp at hQ hk
      omega

/-- An online phase with at most `b.2` points appends at most `b.2` points to the log. -/
lemma length_le_of_mem_support_run_simulateQ_sideLogOnImpl {τ : Type}
    {free : OracleSpec.{0, 0} τ} {α : Type} {oa : OracleComp (free + (spec + side).batch) α}
    {b : ℕ × ℕ} (h : IsOnlineQueryBound oa b) (s : List ι') {z : α × List ι'}
    (hz : z ∈ support ((simulateQ sideLogOnImpl oa).run s)) :
    z.2.length ≤ s.length + b.2 := by
  induction oa using OracleComp.inductionOn generalizing b s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  | query_bind t k ih =>
    rw [IsOnlineQueryBound, isQueryBound_query_bind_iff] at h
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hk := ih y.1 (h.2 y.1) y.2 hz
    rw [sideLogOnImpl_run] at hy
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨u, -, rfl⟩ := hy
    rcases t with n | ts
    · simpa using hk
    · simp only [onlineCanQuery_inr, onlineCost_inr] at h hk
      have := List.length_filterMap_le Sum.getRight? ts
      simp at hk
      omega

/-- **The log is within the budget.** On every outcome of the delay experiment against
`adv.logSide`, for `adv` with preprocessing budget `Q` and online budget `b`, the log holds at
most `Q + b.2` points. -/
theorem length_le_of_mem_support_guessExperiment_logSide {Out : Type}
    (tlp : TimeLockPuzzle (spec + side) Puzzle Key)
    {adv : TwoPhaseAdversary unifSpec (spec + side) Puzzle Out} {Q : ℕ} {b : ℕ × ℕ}
    (h : adv.IsQueryBound Q b) {z : (Out × List ι') × Key}
    (hz : z ∈ support (tlp.guessExperiment adv.logSide)) : z.1.2.length ≤ Q + b.2 := by
  simp only [guessExperiment, TwoPhaseAdversary.logSide, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨σ, hσ, pk, -, out, hout, rfl⟩ := hz
  have h₁ := length_le_of_mem_support_run_simulateQ_sideLogPreImpl h.1 [] hσ
  have h₂ := length_le_of_mem_support_run_simulateQ_sideLogOnImpl (h.2 σ.1 pk.1) σ.2
    (support_simulateQ_subset _ _ hout)
  simp only [List.length_nil, zero_add] at h₁ ⊢
  omega

/-! ## The log and the random-oracle cache -/

section Cache

variable [DecidableEq ι] [DecidableEq ι'] [∀ t, SampleableType (spec.Range t)]
  [∀ t, SampleableType (side.Range t)]

/-- A preprocessing step in the random oracle model keeps the cached `side` points those of `P`
together with the logged ones. -/
private lemma isSome_inr_iff_of_mem_support_sideLogPreImpl
    (t : (unifSpec + (spec + side)).Domain) (s : List ι') (P : ι' → Prop)
    (c : (spec + side).QueryCache) (hc : ∀ x, (c (.inr x)).isSome ↔ P x ∨ x ∈ s)
    {z : ((unifSpec + (spec + side)).Range t × List ι') × (spec + side).QueryCache}
    (hz : z ∈ support ((simulateQ (spec + side).romImpl ((sideLogPreImpl t).run s)).run c))
    (x : ι') : (z.2 (.inr x)).isSome ↔ P x ∨ x ∈ z.1.2 := by
  rw [sideLogPreImpl_run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rcases t with n | t | t
  · rw [unifFwdImpl.snd_eq_of_mem_support_run n c hy]
    simpa using hc x
  · rw [OracleSpec.romImpl_apply_inr] at hy
    rw [QueryImpl.withCaching_run_isSome_apply_iff _ hy, hc x]
    simp
  · rw [OracleSpec.romImpl_apply_inr] at hy
    rw [QueryImpl.withCaching_run_isSome_apply_iff _ hy, hc x]
    simp [or_assoc]

/-- An online step in the random oracle model, rounds answered point by point, keeps the cached
`side` points those of `P` together with the logged ones. -/
private lemma isSome_inr_iff_of_mem_support_sideLogOnImpl
    (t : (unifSpec + (spec + side).batch).Domain) (s : List ι') (P : ι' → Prop)
    (c : (spec + side).QueryCache) (hc : ∀ x, (c (.inr x)).isSome ↔ P x ∨ x ∈ s)
    {z : ((unifSpec + (spec + side).batch).Range t × List ι') × (spec + side).QueryCache}
    (hz : z ∈ support ((simulateQ (unifFwdImpl (spec + side) + (spec + side).randomOracle.batch)
      ((sideLogOnImpl t).run s)).run c))
    (x : ι') : (z.2 (.inr x)).isSome ↔ P x ∨ x ∈ z.1.2 := by
  rw [sideLogOnImpl_run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rcases t with n | ts
  · rw [unifFwdImpl.snd_eq_of_mem_support_run n c hy]
    simpa using hc x
  · rw [QueryImpl.add_apply_inr] at hy
    rw [(QueryImpl.withCaching_batch_le_and_isSome_iff _ hy).2, hc x]
    simp [or_assoc]

/-- A program over `spec`, lifted to `spec + side` and run in the random oracle model with rounds
answered point by point, caches no `side` point. -/
private lemma isSome_inr_iff_of_mem_support_liftComp {α : Type}
    (oa : OracleComp (unifSpec + spec.batch) α) (c : (spec + side).QueryCache)
    {z : α × (spec + side).QueryCache}
    (hz : z ∈ support ((simulateQ (unifFwdImpl (spec + side) + (spec + side).randomOracle.batch)
      (liftComp oa (unifSpec + (spec + side).batch))).run c)) (x : ι') :
    (z.2 (.inr x)).isSome ↔ (c (.inr x)).isSome := by
  rw [liftComp_def, ← QueryImpl.simulateQ_compose] at hz
  refine simulateQ_run_preservesInv _ (fun c' => ∀ x, (c' (.inr x)).isSome ↔ (c (.inr x)).isSome)
    (fun t c' hc' y hy x => ?_) oa c (fun _ => Iff.rfl) z hz x
  rw [QueryImpl.apply_compose] at hy
  rw [OracleComp.liftM_eq_liftM_liftM, simulateQ_query, StateT.run_map, support_map] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  rcases t with n | ts
  · change w ∈ support (((unifFwdImpl (spec + side) + (spec + side).randomOracle.batch)
      (.inl n)).run c') at hw
    rw [QueryImpl.add_apply_inl] at hw
    change (w.2 (.inr x)).isSome ↔ _
    rw [unifFwdImpl.snd_eq_of_mem_support_run n c' hw]
    exact hc' x
  · change w ∈ support (((unifFwdImpl (spec + side) + (spec + side).randomOracle.batch)
      (.inr (ts.map Sum.inl))).run c') at hw
    rw [QueryImpl.add_apply_inr] at hw
    change (w.2 (.inr x)).isSome ↔ _
    rw [(QueryImpl.withCaching_batch_le_and_isSome_iff _ hw).2, hc' x]
    simp

/-- **The log is the cache of side points.** In the random-oracle run from the cache `cache` of
the delay experiment of the puzzle `tlp` lifted to `spec + side` against `adv.logSide`, a `side`
point is cached at the end exactly when it was cached in `cache` or is in the log: the lifted
generator never queries `side`, and every `side` point the adversary queries is logged. -/
theorem cache_inr_isSome_iff_or_mem_log {Out : Type}
    (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : TwoPhaseAdversary unifSpec (spec + side) Puzzle Out) (cache : (spec + side).QueryCache)
    {z : ((Out × List ι') × Key) × (spec + side).QueryCache}
    (hz : z ∈ support ((simulateQ (spec + side).romImpl
      ((tlp.liftSpec (spec + side)).guessExperiment adv.logSide)).run cache)) (t : ι') :
    (z.2 (.inr t)).isSome ↔ (cache (.inr t)).isSome ∨ t ∈ z.1.1.2 := by
  simp only [guessExperiment, liftSpec, TwoPhaseAdversary.logSide, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, mem_support_bind_iff, OracleSpec.simulateQ_romImpl_simulateQ_unbatch] at hz
  obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, hz⟩ := hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have h₁ := simulateQ_run_simulateQ_run_preservesInv _ _
    (fun s c => ∀ x, (c (.inr x)).isSome ↔ (cache (.inr x)).isSome ∨ x ∈ s)
    (fun t s c hc y hy x => isSome_inr_iff_of_mem_support_sideLogPreImpl t s _ c hc hy x)
    _ _ _ (by simp) hy₁
  have h₂ := isSome_inr_iff_of_mem_support_liftComp _ _ hy₂
  have h₃ := simulateQ_run_simulateQ_run_preservesInv _ _
    (fun s c => ∀ x, (c (.inr x)).isSome ↔ (cache (.inr x)).isSome ∨ x ∈ s)
    (fun t s c hc y hy x => isSome_inr_iff_of_mem_support_sideLogOnImpl t s _ c hc hy x)
    _ _ _ (fun x => (h₂ x).trans (h₁ x)) hy₃
  exact h₃ t

/-- **The log is the cache of side points, from the empty cache.** In the random-oracle run from
the empty cache of the delay experiment of the puzzle `tlp` lifted to `spec + side` against
`adv.logSide`, a `side` point is cached at the end exactly when it is in the log. -/
theorem cache_inr_isSome_iff_mem_log {Out : Type}
    (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : TwoPhaseAdversary unifSpec (spec + side) Puzzle Out)
    {z : ((Out × List ι') × Key) × (spec + side).QueryCache}
    (hz : z ∈ support ((simulateQ (spec + side).romImpl
      ((tlp.liftSpec (spec + side)).guessExperiment adv.logSide)).run ∅)) (t : ι') :
    (z.2 (.inr t)).isSome ↔ t ∈ z.1.1.2 := by
  simpa using cache_inr_isSome_iff_or_mem_log tlp adv ∅ hz t

end Cache

end TimeLockPuzzle
