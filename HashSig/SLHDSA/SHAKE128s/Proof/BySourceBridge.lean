/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.KeygenCost
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedCharges
public import HashSig.SLHDSA.SHAKE128s.Proof.SigningFaithful

/-!
# The game counted by source is the game

`Security.runBySource` and `Security.runAll` are the same experiment instrumented two ways: one
counts key generation and the rest apart, the other counts them together. So both are images of
one run, `joint`, which keeps the two counts side by side, and two facts follow:

* the outcome has the same law in both (`map_fst_runBySource`), so the main framework's
  advantage is the total advantage (`advantage_securityGame`);
* key generation's count is at least the `36 · 2 ^ subtreeHeight` calls `KeygenCost` reads off
  the Merkle recursion, on every run (`exists_sourceCounts`).

Together they turn the framework's two almost-sure hypotheses into what the proof consumes: a
pathwise fact at the warmed game's tail, `TailBudget`, saying that the requests, the
adversary's own calls, the verifier's and key generation's fit in `q`. That fact never mentions
the signer's calls, which is the point.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BySourceBridge

open Security

/-! ## One run, counted twice -/

/-- **Key generation counted, then the rest counted**, with both counts kept. -/
noncomputable def joint (adversary : Adversary) :
    OracleComp OracleWorld (((SecretKey × PublicKey) × Nat) × (Outcome × Nat)) :=
  countAllHashes Scheme.keygen >>= fun first =>
    countAllHashes (afterKeygen adversary first.1) >>= fun second =>
      pure (first, second)

theorem experiment_eq_keygen_bind (adversary : Adversary) :
    experiment adversary = Scheme.keygen >>= afterKeygen adversary := rfl

theorem countAllHashes_experiment (adversary : Adversary) :
    countAllHashes (experiment adversary) =
      (fun pair => (pair.2.1, pair.1.2 + pair.2.2)) <$> joint adversary := by
  rw [experiment_eq_keygen_bind, GrowthBudget.countAllHashes_bind, joint]
  simp [map_bind]

theorem experimentBySource_eq (adversary : Adversary) :
    experimentBySource adversary =
      (fun pair => (pair.2.1, sourceCounts pair.2.1 pair.1.2 pair.2.2)) <$> joint adversary := by
  unfold experimentBySource joint
  simp [map_bind]

theorem run_map {α β : Type} (reshape : α → β) (computation : OracleComp OracleWorld α) :
    Xmss.RandomOracleModel.run (reshape <$> computation) =
      reshape <$> Xmss.RandomOracleModel.run computation := by
  unfold Xmss.RandomOracleModel.run
  rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
    Functor.map_map]

/-- **The outcome has one law in both games.** -/
theorem map_fst_runBySource (adversary : Adversary) :
    Prod.fst <$> runBySource adversary = Prod.fst <$> runAll adversary := by
  rw [runBySource, runAll, experimentBySource_eq, countAllHashes_experiment, run_map, run_map,
    Functor.map_map, Functor.map_map]

/-- **The framework's advantage is the total advantage.** -/
theorem advantage_securityGame (adversary : Adversary) :
    securityGame.advantage () adversary = totalAdvantage adversary := by
  unfold Xmss.SecurityGame.advantage totalAdvantage
  change Pr{let result ← (fun result => (decide (Wins result.1), result.2)) <$> runBySource adversary}[result.1 = true] = _
  calc Pr{let result ← (fun result => (decide (Wins result.1), result.2)) <$> runBySource adversary}[result.1 = true]
      = Pr{let x ← Prod.fst <$> runBySource adversary}[Wins x] := by
        rw [prEvent_map, prEvent_map]
        exact probEvent_congr' (fun result _ => by simp) rfl
    _ = Pr{let x ← Prod.fst <$> runAll adversary}[Wins x] := by rw [map_fst_runBySource]
    _ = Pr{let result ← runAll adversary}[Wins result.1] := by
        rw [prEvent_map]
        rfl

/-! ## Key generation's count -/

theorem keygen_eq_seeds_bind :
    (Scheme.keygen : OracleComp OracleWorld (SecretKey × PublicKey)) =
      (liftM WarmedGame.seeds : OracleComp OracleWorld _) >>= fun sds =>
        Scheme.keygenInternal sds.1 sds.2.1 sds.2.2 := by
  have hsample : (simulateQ (fun i => query (spec := unifSpec) i) ($ᵗ Digest) :
      OracleComp OracleWorld Digest) = liftM ($ᵗ Digest : ProbComp Digest) := rfl
  unfold Scheme.keygen WarmedGame.seeds
  simp only [liftM_bind, bind_pure_comp, bind_assoc, liftM_map, bind_map_left, hsample]

attribute [local irreducible] Scheme.keygenInternal Scheme.keygen Scheme.verify Scheme.sign
  afterKeygen Security.countQueries

set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
/-- **Key generation spends its whole top tree, on every run.** -/
theorem keygen_count_ge (cache : QueryCache HashSpec)
    (result : ((SecretKey × PublicKey) × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (Scheme.keygen : OracleComp OracleWorld (SecretKey × PublicKey)))).run
        cache)) :
    (chains + 1) * 2 ^ subtreeHeight ≤ result.1.2 := by
  rw [keygen_eq_seeds_bind] at hmem
  obtain ⟨sds, middleCache, first, second, -, hsecond, hsum⟩ :=
    AdversaryQueries.mem_support_counted_bind_count _ _ cache result hmem
  have h := KeygenCost.count_keygen_ge sds.1 sds.2.1 sds.2.2 middleCache _ hsecond
  simp only at h
  omega

set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
/-- **Every result of the game counted by source carries the outcome's own counts**, and a key
generation count of at least its top tree. -/
theorem exists_sourceCounts (adversary : Adversary)
    (result : Outcome × Xmss.Unforgeability.QueryCounts)
    (hresult : result ∈ support (runBySource adversary)) :
    ∃ keygenHashes laterHashes : Nat,
      result.2 = sourceCounts result.1 keygenHashes laterHashes ∧
        (chains + 1) * 2 ^ subtreeHeight ≤ keygenHashes := by
  rw [runBySource, experimentBySource_eq, run_map, support_map] at hresult
  obtain ⟨pair, hpair, rfl⟩ := hresult
  refine ⟨pair.1.2, pair.2.2, rfl, ?_⟩
  unfold Xmss.RandomOracleModel.run at hpair
  rw [StateT.run'_eq, support_map] at hpair
  obtain ⟨full, hfull, rfl⟩ := hpair
  change full ∈ support ((simulateQ KeygenUniform.rom (joint adversary)).run ∅) at hfull
  rw [joint, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hfull
  obtain ⟨first, hfirst, hrest⟩ := hfull
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨second, -, hpure⟩ := hrest
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  exact keygen_count_ge ∅ first hfirst

/-! ## What the budget hands the proof -/

/-! ## The adversary's own work -/

/-- **The budget at the adversary's own work, read at the warmed tail**: at most `2 ^ 64`
requests, and the requests, the adversary's own calls and the verifier's within `q`. -/
def TailBudgetW (adversary : Adversary) (q : Nat) : Prop :=
  ∀ walk ∈ support WarmedGame.graphWalk, ∀ result ∈ support (WarmedGame.tail adversary walk),
    result.1.1.counts .signing ≤ signingLimit ∧
      result.1.1.counts.work + result.1.1.counts .signing ≤ q

theorem sum_adversaryWork (counts : Xmss.Unforgeability.QueryCounts) :
    ∑ kind ∈ adversaryWork, counts kind = counts .sign + (counts .hash + counts .verifier) := by
  simp [adversaryWork, Finset.sum_insert]

set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
/-- **The framework's hypotheses at `adversaryWork` give the tail budget.** -/
theorem tailBudgetW_of {adversary : Adversary} {q : Nat}
    (hlimit : WithinSigningLimit adversary)
    (hbound : securityGame.HasQueryBound () adversaryWork adversary q) :
    TailBudgetW adversary q := by
  intro walk hwalk result hresult
  have houtcome : result.1 ∈ support ((fun pair => pair.1.2) <$>
      WarmedGame.warmedRun adversary) := by
    rw [support_map]
    exact ⟨_, WarmedCharges.mem_support_warmedRun hwalk hresult, rfl⟩
  rw [Averaging.support_eq_of_evalDistEq (WarmedGame.evalDist_outcome adversary),
    support_map] at houtcome
  obtain ⟨inner, hinner, houter⟩ := houtcome
  have hall := WholeGameStructural.mem_support_runAll_of_mem_support hinner
  have hfst : result.1.1 ∈ support (Prod.fst <$> runBySource adversary) := by
    rw [map_fst_runBySource, support_map]
    exact ⟨inner.1, hall, by rw [houter]⟩
  rw [support_map] at hfst
  obtain ⟨bySource, hbySource, hfstEq⟩ := hfst
  obtain ⟨keygenHashes, laterHashes, hcounts, -⟩ :=
    exists_sourceCounts adversary bySource hbySource
  have hgame : (decide (Wins bySource.1), bySource.2) ∈
      support (securityGame.experiment () adversary) := by
    change _ ∈ support ((fun result => (decide (Wins result.1), result.2)) <$>
      runBySource adversary)
    rw [support_map]
    exact ⟨bySource, hbySource, rfl⟩
  have hsign := (probEvent_eq_one_iff.mp hlimit).2 _ hgame
  have hsum := (probEvent_eq_one_iff.mp hbound).2 _ hgame
  simp only at hsign hsum
  rw [sum_adversaryWork, hcounts] at hsum
  rw [hcounts] at hsign
  simp only [sourceCounts] at hsign hsum
  rw [hfstEq] at hsign hsum
  refine ⟨hsign, ?_⟩
  unfold Counts.work
  omega

end SlhDsaSecurity.BySourceBridge
