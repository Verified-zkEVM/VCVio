/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
public import HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Programming
public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthBudget

/-!
# Pre-sampling an unused oracle entry is free

Every charge is parameterised by the honest cells, but the experiment samples the seeds — and
so determines the cells — inside the run. Closing that needs the experiment rewritten as
*sample a cell table, then program the oracle from it*, which is what
`CanonicalGraph.Programming` does for key generation.

The step that lets such a rewrite be prepended to a run at all is below: filling a cache entry
that is currently empty, with a uniform value, does not change the law of whatever runs next.
In the lazy random-oracle model this is intuitively obvious — the entry would have been
sampled with the same law on first use, and never used entries are never observed — but it is
exactly the fact a presampling argument needs, and VCVio does not carry it.

`evalDist_prepend_fresh_world` is that statement, in the experiment's oracle world. Note the
`Prod.fst`: the two runs end with *different caches*, since one has an extra entry, so only the
value can be compared. That is all any later step needs, because the caches agree wherever the
entry is not involved.

Iterating it along an adaptive traversal gives `evalDist_prepend_worldEvaluate`; specialised to
the honest warmup `worldWarmup` it gives `evalDist_prepend_warmup` and
`evalDist_prepend_warmup_after`, and `evalDist_counted_warmed` places the warmup outside the
hash counter so that the query budget is unaffected.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.Presample

/-- Writing two different keys commutes. -/
theorem cacheQuery_comm (cache : QueryCache HashSpec) {left right : Bytes}
    (hne : left ≠ right) (leftValue rightValue : HashOutput) :
    (cache.cacheQuery left leftValue).cacheQuery right rightValue =
      (cache.cacheQuery right rightValue).cacheQuery left leftValue := by
  simp only [QueryCache.cacheQuery, QueryCache.toFn_ofFn]
  exact congrArg QueryCache.ofFn (Function.update_comm hne _ _ _)

/-! ## Pre-sampling one entry in the game's oracle world

The experiment is `OracleComp OracleWorld` — hash calls and coin flips together — so the step
is stated there. A coin flip does not touch the hash cache, so it commutes with the prepended
draw exactly as a hash query at a different input does.

One detail decides whether this goes through. The prepended draw puts the right-hand side
under a binder, and `rw` does not rewrite under binders: unfolding the query step with `rw`
rewrites only the left, after which the two sides no longer match and every later step fails
on a `Range` mismatch that is really just the untouched side. Using `simp only` for that first
unfolding, which does go under binders, removes the whole difficulty. -/

/-- **Pre-sampling an empty hash entry is free.** Filling an entry the cache does not yet hold
with a uniform value, before the run, leaves the law of the run's value unchanged. -/
theorem evalDist_prepend_fresh_world {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (cache : QueryCache HashSpec) (target : Bytes), cache target = none →
      (Prod.fst <$> (simulateQ KeygenUniform.rom computation).run cache) =ᵈ
        (do
          let value ← ($ᵗ HashOutput : ProbComp HashOutput)
          Prod.fst <$> (simulateQ KeygenUniform.rom computation).run
            (cache.cacheQuery target value)) := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
    intro cache target _
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | query_bind queried next ih =>
    intro cache target hfresh
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases queried with coin | input
    · have hcoin : ∀ probe : QueryCache HashSpec,
          (KeygenUniform.rom (Sum.inl coin)).run probe =
            (fun value => (value, probe)) <$>
              ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) := fun _ => rfl
      simp only [hcoin, bind_map_left]
      refine (EvalDistEq.bind_right _
        (fun value => ih value cache target hfresh)).trans ?_
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
    · have hmissAt : ∀ probe : QueryCache HashSpec, probe input = none →
          (KeygenUniform.rom (Sum.inr input)).run probe =
            (fun value => (value, probe.cacheQuery input value)) <$>
              ($ᵗ (OracleWorld.Range (Sum.inr input)) : ProbComp _) := by
        intro probe hprobe
        change (randomOracle input).run probe = _
        rw [QueryImpl.withCaching_run_none _ hprobe]
        simp [uniformSampleImpl]
      have hhitAt : ∀ (probe : QueryCache HashSpec)
          (value : OracleWorld.Range (Sum.inr input)), probe input = some value →
          (KeygenUniform.rom (Sum.inr input)).run probe = pure (value, probe) := by
        intro probe value hprobe
        change (randomOracle input).run probe = _
        rw [QueryImpl.withCaching_run_some _ hprobe]
      by_cases hsame : input = target
      · subst hsame
        simp only [hmissAt cache hfresh, bind_map_left]
        refine EvalDistEq.bind_right _ (fun value => ?_)
        simp only [hhitAt (cache.cacheQuery input value) value
          (QueryCache.cacheQuery_self cache input value), pure_bind]
        exact EvalDistEq.rfl
      · cases hlookup : cache input with
        | some cached =>
          simp only [hhitAt cache cached hlookup, pure_bind]
          refine (ih cached cache target hfresh).trans
            (EvalDistEq.bind_right _ (fun value => ?_))
          simp only [hhitAt (cache.cacheQuery target value) cached
            (by rw [QueryCache.cacheQuery_of_ne cache value hsame]; exact hlookup), pure_bind]
          exact EvalDistEq.rfl
        | none =>
          simp only [hmissAt cache hlookup, bind_map_left]
          refine (EvalDistEq.bind_right _
            (fun value => ih value (cache.cacheQuery input value) target
              (by rw [QueryCache.cacheQuery_of_ne cache value (Ne.symm hsame)];
                  exact hfresh))).trans ?_
          refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
          refine EvalDistEq.bind_right _ (fun extra => ?_)
          simp only [hmissAt (cache.cacheQuery target extra)
            (by rw [QueryCache.cacheQuery_of_ne cache extra hsame]; exact hlookup),
            bind_map_left, cacheQuery_comm cache hsame]
          rfl

/-! ## Prepending a traversal, in the game's world

The honest parties' queries form an adaptive traversal: each node's byte input is built from
its children's cells, so it depends on answers given earlier. `worldEvaluate` is that traversal
in the experiment's own monad, and prepending it is free for the same reason prepending one
entry is — each query lands on an input still empty — with the induction peeling one query at
a time because the next input is chosen using the value just drawn. -/

/-- The graph traversal, in the experiment's oracle world. -/
@[expose] noncomputable def worldEvaluate {State Index : Type} (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) :
    List Index → State → OracleComp OracleWorld State
  | [], state => pure state
  | node :: nodes, state => do
      let output ← (query (spec := OracleWorld) (Sum.inr (input node state)) :
        OracleComp OracleWorld HashOutput)
      worldEvaluate input step nodes (step node state output)

/-- **Prepending a fresh traversal is free.** Running an adaptive traversal whose inputs are
pairwise separated and still empty in the cache before a computation leaves the law of the
computation's value unchanged. -/
theorem evalDist_prepend_worldEvaluate {α State Index : Type}
    (computation : OracleComp OracleWorld α) (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State)
    (hseparated : GraphFreshSampling.Separated input) :
    ∀ (nodes : List Index) (state : State) (cache : QueryCache HashSpec), nodes.Nodup →
      GraphFreshSampling.FreshFor input nodes cache →
      (Prod.fst <$> (simulateQ KeygenUniform.rom computation).run cache) =ᵈ
        (Prod.fst <$> (simulateQ KeygenUniform.rom
          (worldEvaluate input step nodes state >>= fun _ => computation)).run cache) := by
  intro nodes
  induction nodes with
  | nil =>
    intro state cache _ _
    rw [worldEvaluate, pure_bind]
  | cons node rest ih =>
    intro state cache hnodup hfresh
    have hnotMem : node ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have hhead : cache (input node state) = none := hfresh node (by simp) state
    refine (evalDist_prepend_fresh_world computation cache (input node state) hhead).trans ?_
    have hstep : ∀ value : HashOutput,
        (Prod.fst <$> (simulateQ KeygenUniform.rom computation).run
            (cache.cacheQuery (input node state) value)) =ᵈ
          (Prod.fst <$> (simulateQ KeygenUniform.rom
            (worldEvaluate input step rest (step node state value) >>=
              fun _ => computation)).run (cache.cacheQuery (input node state) value)) := by
      intro value
      refine ih (step node state value) (cache.cacheQuery (input node state) value) hrest ?_
      intro other hother otherState
      rw [QueryCache.cacheQuery_of_ne cache value
        (hseparated other node (fun hsame => hnotMem (hsame ▸ hother)) otherState state)]
      exact hfresh other (by simp [hother]) otherState
    refine (EvalDistEq.bind_right _ hstep).trans ?_
    have hmiss : (KeygenUniform.rom (Sum.inr (input node state))).run cache =
        (fun value => (value, cache.cacheQuery (input node state) value)) <$>
          ($ᵗ (OracleWorld.Range (Sum.inr (input node state))) : ProbComp _) := by
      change (randomOracle (input node state)).run cache = _
      rw [QueryImpl.withCaching_run_none _ hhead]
      simp [uniformSampleImpl]
    have hsim : simulateQ KeygenUniform.rom
        (query (spec := OracleWorld) (Sum.inr (input node state))) =
        KeygenUniform.rom (Sum.inr (input node state)) := by simp
    simp only [worldEvaluate, bind_assoc, simulateQ_bind, hsim,
      StateT.run_bind, map_bind, hmiss, bind_map_left]
    rfl

/-! ## Prepending the warmup

The traversal the experiment's honest parties perform is
`CanonicalGraph.Programming.warmup`, whose coordinates are the structural nodes in rank order.
Every hypothesis of `evalDist_prepend_worldEvaluate` is available for it: the order is
duplicate-free (`order_nodup`), distinct nodes have distinct byte inputs
(`input_separated`), and from the empty cache every input is of course still empty.

So the warmup may be prepended to any computation of the game's world for free — which is what
fixes the honest cells before the adversary runs, since
`GraphFreshSampling.evalDist_evaluate_eq_uniform_program` then turns that traversal into a
uniform table and a programmed cache. -/

/-- The warmup traversal, in the experiment's oracle world. -/
@[expose] noncomputable def worldWarmup (publicSeed secretSeed : Digest) :
    OracleComp OracleWorld CanonicalGraph.Cells :=
  worldEvaluate (CanonicalGraph.Programming.input publicSeed)
    CanonicalGraph.Programming.assign CanonicalGraph.Programming.order
    (CanonicalGraph.Programming.initialCells secretSeed)

/-- **The warmup may be prepended to any run from the empty cache.** -/
theorem evalDist_prepend_warmup {α : Type} (computation : OracleComp OracleWorld α)
    (publicSeed secretSeed : Digest) :
    (Prod.fst <$> (simulateQ KeygenUniform.rom computation).run ∅) =ᵈ
      (Prod.fst <$> (simulateQ KeygenUniform.rom
        (worldWarmup publicSeed secretSeed >>= fun _ => computation)).run ∅) :=
  evalDist_prepend_worldEvaluate computation _ _
    (CanonicalGraph.Programming.input_separated publicSeed)
    CanonicalGraph.Programming.order
    (CanonicalGraph.Programming.initialCells secretSeed) ∅
    CanonicalGraph.Programming.order_nodup (fun _ _ _ => rfl)

/-! ## Inserting the warmup after the seeds

The experiment does not begin with hash calls: it begins by sampling the three seeds, which
are coin queries. The warmup can only be written down once those seeds exist, so it has to be
inserted *after* them rather than prepended to the whole run.

That is sound because coin queries leave the hash cache alone — `run_liftM_probComp` — so the
run still meets the warmup with an empty cache, which is what `evalDist_prepend_warmup`
requires. -/

/-- Simulating a purely-sampling computation leaves the hash cache untouched.

`rom` is `unifFwdImpl + randomOracle`, so a left-lifted computation simulates through the
left component alone (`simulateQ_add_liftM_left`), and that component never writes to the
cache. -/
theorem run_liftM_probComp {γ : Type} (sample : ProbComp γ) (cache : QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom (liftM sample : OracleComp OracleWorld γ)).run cache =
      (fun value => (value, cache)) <$> sample := by
  rw [show KeygenUniform.rom = unifFwdImpl HashSpec + (randomOracle :
      QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) from rfl,
    QueryImpl.simulateQ_add_liftM_left]
  induction sample using OracleComp.inductionOn generalizing cache with
  | pure value => simp [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind coin next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, ih,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
    rfl

/-- **The warmup may be inserted after the seeds are sampled.** -/
theorem evalDist_prepend_warmup_after {α γ : Type} (sample : ProbComp γ)
    (rest : γ → OracleComp OracleWorld α) (publicSeed secretSeed : γ → Digest) :
    (Prod.fst <$> (simulateQ KeygenUniform.rom
        ((liftM sample : OracleComp OracleWorld γ) >>= rest)).run ∅) =ᵈ
      (Prod.fst <$> (simulateQ KeygenUniform.rom
        ((liftM sample : OracleComp OracleWorld γ) >>= fun value =>
          worldWarmup (publicSeed value) (secretSeed value) >>= fun _ => rest value)).run ∅) := by
  simp only [simulateQ_bind, StateT.run_bind, map_bind, run_liftM_probComp, bind_map_left]
  refine EvalDistEq.bind_right _ (fun value => ?_)
  simpa only [simulateQ_bind, StateT.run_bind, map_bind] using
    evalDist_prepend_warmup (rest value) (publicSeed value) (secretSeed value)

/-! ## The world traversal is the lifted one

`worldEvaluate` was written in the experiment's monad so the prepend lemma could be stated
there. It is the same computation as `GraphFreshSampling.evaluate`, lifted — each step's query
is the hash query routed through the sum — and `rom` simulates a right-lifted computation
through `randomOracle` alone.

So everything already proved about the warmup in the hash-only world transfers: in particular
`CanonicalGraph.Programming.warmup_uniform`, which gives the traversal's exact law as a uniform
table and a programmed cache. That is what turns the prepended warmup into *fixed cells*. -/

/-- The world traversal is the hash-only traversal, lifted into the experiment's oracle world. -/
theorem worldEvaluate_eq_liftM {State Index : Type} (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index) (state : State) :
    worldEvaluate input step nodes state =
      liftM (GraphFreshSampling.evaluate input step nodes state) := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node rest ih =>
    rw [worldEvaluate, GraphFreshSampling.evaluate, liftM_bind]
    exact congrArg (Bind.bind _) (funext fun output => ih (step node state output))

/-- The warmup's run in the game's world is its run in the hash-only world. -/
theorem run_worldWarmup (publicSeed secretSeed : Digest) (cache : QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom (worldWarmup publicSeed secretSeed)).run cache =
      (simulateQ randomOracle
        (CanonicalGraph.Programming.warmup publicSeed secretSeed)).run cache := by
  rw [worldWarmup, worldEvaluate_eq_liftM,
    show KeygenUniform.rom = unifFwdImpl HashSpec + (randomOracle :
      QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) from rfl,
    QueryImpl.simulateQ_add_liftM_right]
  rfl

/-! ## The warmup must sit outside the counting

A trap worth naming, because taking the obvious route would quietly break the budget. The
warmup queries every structural node — around `2 ^ 26` of them — so inserting it *inside*
`Security.countAllHashes` would charge all of those to `q`. The analysis needs the warmup; the
accounting must not see it.

So the warmup goes outside the counted computation. That in turn means the seeds, which the
warmup needs, must be sampled outside it too — and they can be, because they are coin queries
and `Security.hashCost` charges nothing for a coin. `countAllHashes_liftM_probComp` is that
fact, and with `GrowthBudget.countAllHashes_bind` it lets the seed sampling be pulled out of
the counter without changing a single count. -/

/-- Counting a purely-sampling computation charges nothing. -/
theorem countAllHashes_liftM_probComp {γ : Type} (sample : ProbComp γ) :
    Security.countAllHashes (liftM sample : OracleComp OracleWorld γ) =
      (fun value => (value, 0)) <$> (liftM sample : OracleComp OracleWorld γ) := by
  induction sample using OracleComp.inductionOn with
  | pure value => simp [GrowthBudget.countAllHashes_pure]
  | query_bind coin next ih =>
    have hlift : (liftM (liftM (OracleSpec.query coin) >>= next) :
        OracleComp OracleWorld _) =
        liftM (OracleWorld.query (Sum.inl coin)) >>= fun answer =>
          (liftM (next answer) : OracleComp OracleWorld _) := by
      rw [liftM_bind]
      rfl
    rw [hlift, GrowthBudget.countAllHashes_query_bind]
    simp only [ih, Security.hashCost, RandomOracleModel.hashCost,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Nat.zero_add]

/-- The counter passes through a purely-sampling prefix untouched. -/
theorem countAllHashes_liftM_bind {α γ : Type} (sample : ProbComp γ)
    (rest : γ → OracleComp OracleWorld α) :
    Security.countAllHashes ((liftM sample : OracleComp OracleWorld γ) >>= rest) =
      (liftM sample : OracleComp OracleWorld γ) >>= fun value =>
        Security.countAllHashes (rest value) := by
  rw [GrowthBudget.countAllHashes_bind, countAllHashes_liftM_probComp]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Nat.zero_add]
  exact congrArg (Bind.bind _) (funext fun value => by simp)

/-- **The experiment, warmed.** Inserting the warmup after the seeds leaves the law of the
counted run's value unchanged — the warmup is outside the counter, so it costs nothing, and
the seeds are coin queries, so pulling them out of the counter costs nothing either. -/
theorem evalDist_counted_warmed {α γ : Type} (sample : ProbComp γ)
    (rest : γ → OracleComp OracleWorld α) (publicSeed secretSeed : γ → Digest) :
    (Prod.fst <$> (simulateQ KeygenUniform.rom
        (Security.countAllHashes ((liftM sample : OracleComp OracleWorld γ) >>= rest))).run ∅) =ᵈ
      (Prod.fst <$> (simulateQ KeygenUniform.rom
        ((liftM sample : OracleComp OracleWorld γ) >>= fun value =>
          worldWarmup (publicSeed value) (secretSeed value) >>= fun _ =>
            Security.countAllHashes (rest value))).run ∅) := by
  rw [countAllHashes_liftM_bind]
  exact evalDist_prepend_warmup_after sample
    (fun value => Security.countAllHashes (rest value)) publicSeed secretSeed

end SlhDsaSecurity.Presample
