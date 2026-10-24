/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Presample
public import HashSig.SLHDSA.SHAKE128s.Proof.WholeGameStructural
public import HashSig.SLHDSA.SHAKE128s.Proof.Averaging

/-!
# The game with its honest cells fixed first

Every charge bounds an event against a *fixed* table of honest cells, because the alternative (a
cell drawn after the colliding query) would need a union bound over all `2 ^ 26`-odd cells and
lose far more than the budget allows.

In the experiment the cells are not fixed: they are whatever key generation and signing
happen to query. The repair is `Presample.worldWarmup`, which walks the whole canonical graph
in topological order before the adversary runs. Every one of its queries is fresh and
separated, so prepending it changes nothing about the law of the outcome; afterwards the cells
are determined, and the rest of the game runs against a cache that already carries them.

This file puts the experiment into the shape the warmup needs — a `liftM` of the three seeds
followed by everything else — and records the resulting game, `warmedRun`, together with the
one fact that transfers the target to it: the winning event is an event about the outcome
alone, and the outcome's law is unchanged.

What is gained is that `warmedRun`'s value carries the seeds and the cells, so statements may
speak about *this run's* honest key rather than an arbitrary fixed one. What is paid is nothing:
`Presample.evalDist_counted_warmed` is an equality.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.WarmedGame

open Security CanonicalGraph

/-- The three seeds key generation draws, as one sample. -/
@[expose] noncomputable def seeds : ProbComp (Digest × Digest × Digest) := do
  let secretSeed ← $ᵗ Digest
  let prfSeed ← $ᵗ Digest
  let publicSeed ← $ᵗ Digest
  pure (secretSeed, prfSeed, publicSeed)

/-- The experiment after its seeds are drawn: key generation from those seeds, the
adversary's interaction, and the verification of what it returns. -/
@[expose] noncomputable def afterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest) :
    OracleComp OracleWorld Outcome := do
  let (sk, pk) ← Scheme.keygenInternal sds.1 sds.2.1 sds.2.2
  let ((forgery, adversaryCounts), signed) ←
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
          (fun input => Counts.single .hash (hashCost input)) + signingOracle sk)
      (adversary.main pk)).run.run []
  let (verified, verifierCounts) ← countQueries
    (fun input => Counts.single .verification (hashCost input))
    (Scheme.verify pk forgery.message forgery.signature)
  return {
    forgery := forgery
    signed := signed
    verified := verified
    counts := Multiplicative.toAdd adversaryCounts + verifierCounts }

/-- **The experiment is its seeds, then the rest.** -/
theorem experiment_eq (adversary : Adversary) :
    experiment adversary = (liftM seeds : OracleComp OracleWorld _) >>= afterSeeds adversary := by
  have hsample : (simulateQ (fun i => query (spec := unifSpec) i) ($ᵗ Digest) :
      OracleComp OracleWorld Digest) = liftM ($ᵗ Digest : ProbComp Digest) := rfl
  unfold experiment afterSeeds seeds Scheme.keygen
  simp only [liftM_bind, bind_pure_comp, bind_assoc, liftM_map, bind_map_left, hsample]

/-! ## The warmed run

`warmedRun` draws the seeds, walks the canonical graph, and then plays the counted game. Its
value keeps everything the halves need: the seeds, the cells the walk produced, and the
counted outcome; its state is the final cache.

The warmup sits outside `countAllHashes`, which is what makes it free — it makes on the order
of `2 ^ 26` queries, far more than any budget would allow, and none of them is charged. -/

/-- The experiment with the canonical graph walked first, keeping seeds, cells and cache. -/
@[expose] noncomputable def warmedRun (adversary : Adversary) :
    ProbComp ((((Digest × Digest × Digest) × Cells) × (Outcome × Nat)) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom (do
    let sds ← (liftM seeds : OracleComp OracleWorld _)
    let cells ← Presample.worldWarmup sds.2.2 sds.1
    let counted ← countAllHashes (afterSeeds adversary sds)
    pure ((sds, cells), counted))).run ∅

/-- The warmed run, projected to the counted outcome, is the warmed experiment of
`Presample.evalDist_counted_warmed`. -/
theorem map_warmedRun (adversary : Adversary) :
    (fun result => result.1.2) <$> warmedRun adversary =
      Prod.fst <$> (simulateQ KeygenUniform.rom
        ((liftM seeds : OracleComp OracleWorld _) >>= fun sds =>
          Presample.worldWarmup sds.2.2 sds.1 >>= fun _ =>
            countAllHashes (afterSeeds adversary sds))).run ∅ := by
  have hmap : (Prod.snd <$> (simulateQ KeygenUniform.rom (do
        let sds ← (liftM seeds : OracleComp OracleWorld _)
        let cells ← Presample.worldWarmup sds.2.2 sds.1
        let counted ← countAllHashes (afterSeeds adversary sds)
        pure ((sds, cells), counted))
          : StateT (QueryCache HashSpec) ProbComp _)) =
      simulateQ KeygenUniform.rom
        ((liftM seeds : OracleComp OracleWorld _) >>= fun sds =>
          Presample.worldWarmup sds.2.2 sds.1 >>= fun _ =>
            countAllHashes (afterSeeds adversary sds)) := by
    rw [← simulateQ_map]
    simp [map_eq_bind_pure_comp, bind_assoc]
  rw [← hmap, StateT.run_map, Functor.map_map, warmedRun]

/-- **The outcome's law is unchanged by warming.** -/
theorem evalDist_outcome (adversary : Adversary) :
    ((fun result => result.1.2) <$> warmedRun adversary) =ᵈ
      (Prod.fst <$> WholeGameStructural.instrumentedRun adversary) := by
  rw [map_warmedRun, WholeGameStructural.instrumentedRun, experiment_eq]
  exact (Presample.evalDist_counted_warmed seeds (afterSeeds adversary)
    (fun sds => sds.2.2) (fun sds => sds.1)).symm

/-- **The target's event, transferred to the warmed run.** The winning event looks only at the
outcome, so warming — which changes the cache, and only the cache — leaves it alone. -/
theorem prEvent_warmed (adversary : Adversary) (event : Outcome × Nat → Prop) :
    Pr{let result ← WholeGameStructural.instrumentedRun adversary}[event result.1] =
      Pr{let result ← warmedRun adversary}[event result.1.2] := by
  rw [← prEvent_map (WholeGameStructural.instrumentedRun adversary) Prod.fst event,
    ← prEvent_map (warmedRun adversary) (fun result => result.1.2) event]
  exact ((evalDist_outcome adversary).prEvent_eq event).symm

/-! ## Splitting the warmed run at the adversary

The charges apply to what happens *after* the graph is walked, with the cells held fixed and
the cache already carrying them. So the run is split in two: `graphWalk`, which draws the
seeds and evaluates the canonical graph, and `tail`, which plays the counted game from the
cache the walk left. A bound that holds after every walk holds for the run, by
`Averaging.prEvent_bind_pair_le`; nothing else about the walk is used, since its output is an
arbitrary fixed cell table from here on. -/

/-- The seeds and the canonical graph's evaluation, with the cache they leave. -/
@[expose] noncomputable def graphWalk :
    ProbComp (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom (do
    let sds ← (liftM seeds : OracleComp OracleWorld _)
    let cells ← Presample.worldWarmup sds.2.2 sds.1
    pure (sds, cells))).run ∅

/-- The counted game, played from what the walk left. -/
@[expose] noncomputable def tail (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) :
    ProbComp ((Outcome × Nat) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom (countAllHashes (afterSeeds adversary start.1.1))).run start.2

/-- **The warmed run is the walk, then the game.** -/
theorem warmedRun_eq (adversary : Adversary) :
    warmedRun adversary =
      (fun pair => ((pair.1.1, pair.2.1), pair.2.2)) <$>
        (do let walk ← graphWalk; let result ← tail adversary walk; pure (walk, result)) := by
  have hsplit : (do
      let sds ← (liftM seeds : OracleComp OracleWorld _)
      let cells ← Presample.worldWarmup sds.2.2 sds.1
      let counted ← countAllHashes (afterSeeds adversary sds)
      pure ((sds, cells), counted)) =
    ((do
      let sds ← (liftM seeds : OracleComp OracleWorld _)
      let cells ← Presample.worldWarmup sds.2.2 sds.1
      pure (sds, cells)) :
        OracleComp OracleWorld ((Digest × Digest × Digest) × Cells)) >>= fun walk =>
        countAllHashes (afterSeeds adversary walk.1) >>= fun counted => pure (walk, counted) := by
    simp [bind_assoc]
  rw [warmedRun, hsplit, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc,
    ← graphWalk]
  apply bind_congr
  intro walk
  rw [simulateQ_bind, StateT.run_bind]
  simp [tail, map_eq_bind_pure_comp, bind_assoc]

/-! ## What the walk leaves

The walk's whole purpose is the shape of what it leaves behind: a cell table that is some
uniform output table read through `cellsOfOutputs`, and a cache that is exactly the canonical
entries of that table. `CanonicalGraph.Programming.warmup_uniform` is that law; here it is read
as a statement about the support, which is all the charges need — they are uniform over the
walk, so only the *form* of its result matters, never its distribution. -/

/-- The walk, as the seeds followed by the hash-only graph traversal. -/
theorem graphWalk_eq :
    graphWalk = (do
      let sds ← seeds
      let result ← (simulateQ randomOracle
        (CanonicalGraph.Programming.warmup sds.2.2 sds.1)).run ∅
      pure ((sds, result.1), result.2)) := by
  rw [graphWalk]
  simp only [simulateQ_bind, StateT.run_bind, Presample.run_liftM_probComp, bind_map_left,
    Presample.run_worldWarmup, simulateQ_pure, StateT.run_pure]

/-- **Every walk is a programmed table.** -/
theorem mem_support_graphWalk {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) :
    ∃ outputs : CanonicalGraph.Programming.Outputs,
      walk.1.2 = CanonicalGraph.Programming.cellsOfOutputs walk.1.1.1 outputs ∧
        walk.2 = CanonicalGraph.Programming.cacheFrom walk.1.1.2.2 walk.1.2 outputs
          CanonicalGraph.Programming.order ∅ := by
  rw [graphWalk_eq] at hwalk
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop] at hwalk
  obtain ⟨sds, -, result, hresult, hpair⟩ := hwalk
  rw [Averaging.support_eq_of_evalDistEq
    (CanonicalGraph.Programming.warmup_uniform sds.2.2 sds.1), support_map] at hresult
  obtain ⟨outputs, -, houtputs⟩ := hresult
  refine ⟨outputs, ?_, ?_⟩ <;> rw [hpair] <;> rw [← houtputs]

end SlhDsaSecurity.WarmedGame
