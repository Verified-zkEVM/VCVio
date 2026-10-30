/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay
public import VCVio.OracleComp.QueryTracking.RandomOracle.Presampling
public import HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Programming
public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthBudget

/-!
# Value laws for presampling in the SLH-DSA experiment

Discarding any actual total prefix preserves a fixed subsequent experiment's returned-value
distribution under the shared lazy oracle and stateless private sampling. The laws include the
client's complete counted outcome; they discard final public cache and prefix work or trace.

`worldEvaluate` lifts the canonical random-oracle traversal into the experiment's oracle world.
Its independent-table coupling has separate separation, duplicate-freedom and freshness premises.
Private seed sampling leaves the hash cache untouched; keeping warmup outside `countAllHashes`
preserves the selected downstream count rather than charging the warmup to the adversary.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Presample

/-! ## Discarded prefixes -/

/-- Discarding an actual total world prefix preserves the fixed client's returned-value law. -/
theorem evalDist_prepend_prefix_world {α β : Type}
    (before : OracleComp OracleWorld β) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    (Prod.fst <$> (simulateQ KeygenUniform.rom computation).run cache) =ᵈ
      (Prod.fst <$> (simulateQ KeygenUniform.rom
        (before >>= fun _ => computation)).run cache) := by
  simpa only [KeygenUniform.rom, RandomOracleModel.impl, unifFwdImpl] using
    OracleComp.RandomOraclePresampling.evalDist_prepend_prefix
      (QueryImpl.ofLift unifSpec ProbComp) before computation cache

/-! ## Presampling the canonical traversal -/

/-- The canonical full-answer graph traversal in the experiment's oracle world. -/
noncomputable def worldEvaluate {State Index : Type} (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) :
    List Index → State → OracleComp OracleWorld State :=
  fun nodes state => liftM (OracleComp.RandomOracleTraversal.evaluate input step nodes state)

/-! ## Prepending the warmup

The value law discards the complete actual warmup, so it needs no independent-answer
hypotheses. The separate uniform-table representation of the canonical warmup retains its
coordinate separation, duplicate-freedom and cache freshness requirements.
-/

/-- The warmup traversal, in the experiment's oracle world. -/
@[expose] noncomputable def worldWarmup (publicSeed secretSeed : Digest) :
    OracleComp OracleWorld CanonicalGraph.Cells :=
  worldEvaluate (CanonicalGraph.Programming.input publicSeed)
    CanonicalGraph.Programming.assign CanonicalGraph.Programming.order
    (CanonicalGraph.Programming.initialCells secretSeed)

/-- A discarded warmup preserves the subsequent returned-value law from the empty cache. -/
theorem evalDist_prepend_warmup {α : Type} (computation : OracleComp OracleWorld α)
    (publicSeed secretSeed : Digest) :
    (Prod.fst <$> (simulateQ KeygenUniform.rom computation).run ∅) =ᵈ
      (Prod.fst <$> (simulateQ KeygenUniform.rom
        (worldWarmup publicSeed secretSeed >>= fun _ => computation)).run ∅) :=
  evalDist_prepend_prefix_world (worldWarmup publicSeed secretSeed) computation ∅

/-! ## Inserting the warmup after the seeds

The experiment does not begin with hash calls: it begins by sampling the three seeds, which
are coin queries. The warmup can only be written down once those seeds exist, so it has to be
inserted *after* them rather than prepended to the whole run.

Private seed sampling leaves the hash cache alone (`run_liftM_probComp`). The value law
applies pointwise to each fixed seed value; no result of the discarded warmup is passed to
the subsequent client. -/

/-- Simulating a purely-sampling computation leaves the hash cache untouched.

`rom` is `unifFwdImpl + randomOracle`, so a left-lifted computation simulates through the
left component alone (`simulateQ_add_liftM_left`), and that component never writes to the
cache. -/
theorem run_liftM_probComp {γ : Type} (sample : ProbComp γ) (cache : QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom (liftM sample : OracleComp OracleWorld γ)).run cache =
      (fun value => (value, cache)) <$> sample := by
  exact roSim.run_liftM (randomOracle :
    QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) sample cache

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

/-! ## The lifted traversal

The full byte-answer evaluator and the canonical traversal have the same operational meaning.
Their lift into the experiment therefore has the same complete warmup run in the shared cache.
-/

/-- The world traversal is the hash-only traversal, lifted into the experiment's oracle world. -/
theorem worldEvaluate_eq_liftM {State Index : Type} (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index) (state : State) :
    worldEvaluate input step nodes state =
      liftM (GraphFreshSampling.evaluate input step nodes state) := by
  rw [worldEvaluate, GraphFreshSampling.evaluate_eq_traversal]

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

end SLHDSA.SHAKE128s.Presample
