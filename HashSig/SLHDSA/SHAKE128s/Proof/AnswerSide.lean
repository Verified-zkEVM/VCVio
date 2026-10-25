/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.RoutedSplit
public import HashSig.SLHDSA.SHAKE128s.Proof.CoverageTail
public import HashSig.SLHDSA.SHAKE128s.Proof.AddressBounds
public import HashSig.SLHDSA.SHAKE128s.Proof.WalkDefects
public import HashSig.SLHDSA.SHAKE128s.Proof.ClassGrowth
public import HashSig.SLHDSA.SHAKE128s.Proof.CoverageCount
public import HashSig.SLHDSA.SHAKE128s.Proof.SplitWitness

/-!
# The answer side: the canonical-hit predicate and the key the walk fixes

Helpers for the answer-side charge. `CanonicalBad` is the structural clause as a per-answer
predicate, with its `2 ^ -128` rate off the message class. The remaining lemmas say that the
key the tail's final cache generates is the key the graph walk already fixed (its seed and its
top cell), so a hypothesis on the walk's key is a hypothesis on the generated one.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.AnswerSide

open Security CanonicalGraph WarmedGame

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Scheme.sign Security.signingOracle Security.countQueries

/-- The structural clause as a per-answer predicate: this answer hits the canonical cell of the
node its own input names, the input's child values deviating from the honest ones. -/
@[expose] noncomputable def CanonicalBad (publicSeed : Digest) (cells : Cells) :
    Bytes → HashOutput → Prop :=
  fun input answer =>
    CanonicalTarget.canonicalTarget publicSeed cells input = some (Hashing.truncate answer)

/-- **Off the message class the rate is one unit of `2 ^ -128`.** -/
theorem prob_canonicalBad_le (publicSeed : Digest) (cells : Cells) (input : Bytes) :
    Pr{let answer ← ($ᵗ HashOutput : ProbComp HashOutput)}[
        CanonicalBad publicSeed cells input answer] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_trans (prEvent_mono _ _ _ fun _ hbad => hbad.symm)
    (FreshHitBound.prob_target_match_le (CanonicalTarget.canonicalTarget publicSeed cells input))

/-! ## The key the charge is stated at

The routing names the key this run's own final cache generates. After the graph is walked, key
generation asks the cache nothing new, so the key is already determined by the walk and the
tail cannot move it. -/

/-- **The key the run generates is the key the walk already fixed.** -/
theorem generatedKey_eq_walk (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) :
    SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2 =
      SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2 := by
  obtain ⟨outputs, hwarm⟩ := HonestGrowth.walk_cache_eq_warmCache hwalk
  have hrun : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (afterSeeds adversary walk.1.1))).run walk.2) := hresult
  obtain ⟨keys, keyCache, verifyCache, hkeys, hpersist, -⟩ :=
    WarmedSplit.split_afterSeeds adversary walk.1.1 walk.2 result hrun
  have hpure := hkeys
  rw [hwarm, HonestProbes.run_keygenInternal_world_eq_pure, support_pure,
    Set.mem_singleton_iff] at hpure
  have hvalue : keys = @Scheme.keygenInternal Id Id.instMonad
      (CacheReplay.replayQuery walk.2) walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 := by
    rw [hwarm]; exact (Prod.ext_iff.mp hpure).1
  rw [WarmedSplit.keygenInternal_liftM, WarmedSplit.run_rom_liftM] at hkeys
  have hreplay := WarmedSplit.keygenInternal_eq_replay_of_subset walk.1.1.1 walk.1.1.2.1
    walk.1.1.2.2 walk.2 keyCache result.2 keys hkeys hpersist
  rw [SplitCharged.generatedKey, SplitCharged.generatedKey, ← hreplay, hvalue]

/-! ## The hypothesis on the key is the walk's own

A hypothesis on the generated key is a statement about the walk: its public seed is the seed
the walk drew and its root is the walk's own cell at the top node. So it is the walk defect
`WalkDefects.prob_possible_walk` charges. -/

/-- **The walk's cache computes the walk's cells.** -/
theorem value_replay_walk_eq_cells
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) :
    @CanonicalGraph.value (CacheReplay.replayQuery walk.2) walk.1.1.1 walk.1.1.2.2 =
      walk.1.2 := by
  obtain ⟨outputs, hcells, hcache⟩ := mem_support_graphWalk hwalk
  rw [hcells]
  refine GameBridge.value_eq_cellsOfOutputs walk.1.1.2.2 walk.1.1.1 outputs walk.2
    fun input output hentry => ?_
  rw [hcache, hcells]
  exact hentry

/-- **The generated key is the walk's seed and the walk's top cell.** -/
theorem generatedKey_eq_walk_pair
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) :
    ((SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).seed,
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).root) =
      (walk.1.1.2.2, walk.1.2 (.structural WalkDefects.topNode)) := by
  have hseed : (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).seed =
      walk.1.1.2.2 :=
    (GameBridge.keygen_publicKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).1
  have hroot : (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).root =
      walk.1.2 (.structural WalkDefects.topNode) := by
    rw [SplitCharged.generatedKey,
      (GameBridge.keygen_publicKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).2,
      ← @WalkDefects.value_topNode (CacheReplay.replayQuery walk.2) walk.1.1.1 walk.1.1.2.2,
      value_replay_walk_eq_cells hwalk]
  rw [hseed, hroot]

/-- **The key is no coincidence as soon as the walk is not one.** -/
theorem not_possible_generatedKey
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    (hgood : ¬ HashSeparation.Possible
      (walk.1.1.2.2, walk.1.2 (.structural WalkDefects.topNode))) :
    ¬ HashSeparation.Possible
      ((SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).seed,
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).root) := by
  rw [generatedKey_eq_walk_pair hwalk]
  exact hgood

end SLHDSA.SHAKE128s.AnswerSide
