/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Game
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! # Lazy hash-to-group oracles

The cache stores values, while the receipt list records every answer, including repetitions.
A reduction stores coefficient vectors as values and decodes them into group elements. Only
the decoded cache and receipts are visible in the perfect-simulation statement.
-/

public section

namespace GroupModel.HashToGroup

open OracleComp OracleSpec Interaction

variable {Label C D F G α Data Query σ : Type} {Reply : Query → Type}

/-- Private cache and chronological receipts, with one receipt for every adversary query. -/
abbrev State (Label C : Type) := (Label →ₒ C).QueryCache × List C

/-- An empty cache with an optional list of initially supplied representations. -/
@[expose] def initial (rows : List C := []) : State Label C := (∅, rows)

/-- Apply a value interpretation to both the private cache and the receipt list. -/
@[expose] def mapState (f : C → D) (st : State Label C) : State Label D :=
  (QueryCache.ofFn fun l => (st.1 l).map f, st.2.map f)

/-- A hash query samples only on a cache miss and records its answer even on a cache hit. -/
@[expose] def oracle [DecidableEq Label] (decode : C → G) (sample : Label → ProbComp C) :
    QueryImpl (Label →ₒ G) (StateT (State Label C) ProbComp) :=
  fun l st => do
    let (c, cache) ← (QueryImpl.withCaching (spec := Label →ₒ C) sample l).run st.1
    pure (decode c, cache, st.2 ++ [c])

/-- One cached hash step, exposing the fresh and repeated-query branches. -/
theorem oracle_apply [DecidableEq Label] (decode : C → G) (sample : Label → ProbComp C)
    (l : Label) (st : State Label C) :
    (oracle decode sample l).run st = match st.1 l with
      | some c => pure (decode c, st.1, st.2 ++ [c])
      | none => (fun c => (decode c, st.1.cacheQuery l c, st.2 ++ [c])) <$> sample l := by
  change ((QueryImpl.withCaching (spec := Label →ₒ C) sample l).run st.1 >>=
    fun z => pure (decode z.1, z.2, st.2 ++ [z.1])) = _
  cases hc : st.1 l with
  | some c => rw [QueryImpl.withCaching_run_some _ hc]; simp
  | none => rw [QueryImpl.withCaching_run_none _ hc]; simp

/-- Each hash step appends exactly its reply to the decoded receipts. -/
theorem oracle_receipts [DecidableEq Label] (decode : C → G) (sample : Label → ProbComp C)
    (l : Label) (st : State Label C) (z : G × State Label C)
    (hz : z ∈ support ((oracle decode sample l).run st)) :
    z.2.2.map decode = st.2.map decode ++ [z.1] := by
  rw [oracle_apply] at hz
  cases hc : st.1 l with
  | some c => simp only [hc, support_pure, Set.mem_singleton_iff] at hz; subst z; simp
  | none =>
    simp only [hc, support_map, Set.mem_image] at hz
    obtain ⟨c, _, rfl⟩ := hz
    simp

/-- A hash reply carries one group input and no plain data. -/
@[expose] def reply (g : G) : Message Unit (fun _ : Unit => G) := ⟨(), fun _ => [g]⟩

/-- Hash-to-group requests use their label as plain data; their group arguments are ignored. -/
abbrev gameSpec (Label G : Type) := plainSpec (fun _ : Unit => G) Label (fun _ => Unit)

/-- The interaction presentation of a hash-to-group oracle. -/
@[expose] def game [DecidableEq Label] (decode : C → G) (sample : Label → ProbComp C) :
    QueryImpl (gameSpec Label G) (StateT (State Label C) ProbComp) :=
  fun q => reply <$> oracle decode sample q.data

/-- The honest lazy random oracle, with every answer recorded in chronological order. -/
@[expose] def honest [DecidableEq Label] [SampleableType G] :
    QueryImpl (gameSpec Label G) (StateT (State Label G) ProbComp) :=
  game id (fun _ => $ᵗ G)

/-- Forgetting receipts recovers the existing lazy random-oracle handler exactly. -/
theorem oracle_uniform_cache [DecidableEq Label] [SampleableType G]
    (l : Label) (st : State Label G) :
    (fun z => (z.1, z.2.1)) <$> (oracle id (fun _ => $ᵗ G) l).run st =
      ((Label →ₒ G).randomOracle l).run st.1 := by
  simp [StateT.run, oracle, OracleSpec.randomOracle, uniformSampleImpl]

private theorem map_cacheQuery [DecidableEq Label] (f : C → D)
    (cache : (Label →ₒ C).QueryCache) (l : Label) (c : C) :
    QueryCache.ofFn (spec := Label →ₒ D) (fun k => ((cache.cacheQuery l c) k).map f) =
      (QueryCache.ofFn (spec := Label →ₒ D) fun k => (cache k).map f).cacheQuery l (f c) := by
  ext k
  by_cases h : k = l
  · subst k; simp
  · simp [h]

/-- Interpreting each fresh sample in distribution interprets each complete cached step,
including its retained cache and chronological receipts. -/
theorem oracle_mapState [DecidableEq Label] (f : C → D) (decode : D → G)
    (sample : Label → ProbComp C) (target : Label → ProbComp D)
    (h : ∀ l, f <$> sample l =ᵈ target l) (l : Label) (st : State Label C) :
    Prod.map id (mapState f) <$> (oracle (decode ∘ f) sample l).run st =ᵈ
      (oracle decode target l).run (mapState f st) := by
  cases hc : st.1 l with
  | some c =>
    simp [oracle_apply, mapState, hc]
  | none =>
    simpa [oracle_apply, mapState, hc, Function.comp_def, map_cacheQuery] using (h l).map (fun d =>
        (decode d, (mapState f st).1.cacheQuery l d, (mapState f st).2 ++ [d]))

/-- Perfect simulation for arbitrary adaptive hash computations, retaining all visible state. -/
theorem simulateQ_oracle_mapState [DecidableEq Label] (f : C → D) (decode : D → G)
    (sample : Label → ProbComp C) (target : Label → ProbComp D)
    (h : ∀ l, f <$> sample l =ᵈ target l)
    (p : OracleComp (Label →ₒ G) α) (st : State Label C) :
    Prod.map id (mapState f) <$> (simulateQ (oracle (decode ∘ f) sample) p).run st =ᵈ
      (simulateQ (oracle decode target) p).run (mapState f st) :=
  evalDistEq_map_run_simulateQ_eq_of_query_evalDistEq_map_eq _ _ _
    (oracle_mapState f decode sample target h) p st

/-- Interpreting each fresh sample in distribution interprets each step of the interaction. -/
theorem game_mapState [DecidableEq Label] (f : C → D) (decode : D → G)
    (sample : Label → ProbComp C) (target : Label → ProbComp D)
    (h : ∀ l, f <$> sample l =ᵈ target l) (q : Message Label (fun _ : Unit => G))
    (st : State Label C) :
    Prod.map id (mapState f) <$> (game (decode ∘ f) sample q).run st =ᵈ
      (game decode target q).run (mapState f st) := by
  simpa [game, Function.comp_def] using
    (oracle_mapState f decode sample target h q.data st).map (fun z => (reply z.1, z.2))

/-- Perfect simulation in the interaction shape, for arbitrary computations and visible state.
Binding either side to any downstream computation preserves this equality in distribution. -/
theorem simulateQ_game_mapState [DecidableEq Label] (f : C → D) (decode : D → G)
    (sample : Label → ProbComp C) (target : Label → ProbComp D)
    (h : ∀ l, f <$> sample l =ᵈ target l)
    (p : OracleComp (gameSpec Label G) α) (st : State Label C) :
    Prod.map id (mapState f) <$> (simulateQ (game (decode ∘ f) sample) p).run st =ᵈ
      (simulateQ (game decode target) p).run (mapState f st) :=
  evalDistEq_map_run_simulateQ_eq_of_query_evalDistEq_map_eq _ _ _
    (game_mapState f decode sample target h) p st

/-- Handle hash replies install a fresh table entry on every query, including cache hits. -/
@[expose] def handle [DecidableEq Label] [Zero G]
    (decode : C → G) (sample : Label → ProbComp C) :
    QueryImpl (handleSpec (S := Unit) Label (fun _ => Unit))
      (StateT (Tbl (fun _ : Unit => G)) (StateT (State Label C) ProbComp)) :=
  liftGame (game decode sample)

/-- The handle presentation returns the old table length as its handle and appends the answer. -/
theorem handle_apply [DecidableEq Label] [Zero G]
    (decode : C → G) (sample : Label → ProbComp C)
    (q : Message Label (fun _ : Unit => Handle)) (tbl : Tbl (fun _ : Unit => G)) :
    (handle decode sample q).run tbl = (do
      let g ← oracle decode sample q.data
      pure (⟨(), fun s => [(tbl s).length]⟩, fun s => tbl s ++ [g])) := by
  simp [StateT.run, handle, liftGame, game, lookupMessage, reply, pushGroups, map_eq_bind_pure_comp]

/-! ## Explained programs -/

/-- Forward explained requests to the plain game while retaining explanations in the result. -/
@[expose] def interactionProgram
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) Query Reply) α) :
    OracleComp (plainSpec (fun _ : Unit => G) Query Reply) α :=
  simulateQ (fun q => (plainSpec (fun _ : Unit => G) Query Reply).query q.value) p

/-- If every step of a handler records exactly the group elements in its reply, a certified
program's output is explained over what the handler recorded. -/
theorem run_receipts_valid [CommSemiring F] [AddCommMonoid G] [Module F G]
    (impl : QueryImpl (plainSpec (fun _ : Unit => G) Query Reply) (StateT σ ProbComp))
    (received : σ → List G)
    (hstep : ∀ query st z, z ∈ support ((impl query).run st) →
      received z.2 = received st ++ z.1.groups ())
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) Query Reply)
      (Explained F Data (fun _ : Unit => G)))
    (st : σ) (hp : IsAlgebraic (fun _ => received st) p) (z)
    (hz : z ∈ support ((simulateQ impl (interactionProgram p)).run st)) :
    z.1.Valid (fun _ => received z.2) := by
  induction p using OracleComp.inductionOn generalizing st z with
  | pure out =>
    simp only [interactionProgram, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hp
  | query_bind query next ih =>
    simp only [interactionProgram, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    apply ih w.1 w.2 _ z hz
    have hn := ((isAlgebraic_query (fun _ => received st) query next).mp hp).2 w.1
    change IsAlgebraic (fun _ => received st ++ w.1.groups ()) (next w.1) at hn
    rwa [hstep query.value st w hw]

end GroupModel.HashToGroup
