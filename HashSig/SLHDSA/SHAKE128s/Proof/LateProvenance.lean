/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.FusedCoverage
public import HashSig.SLHDSA.SHAKE128s.Proof.RandomiserProvenance
public import HashSig.SLHDSA.SHAKE128s.Proof.PhaseRightRecord

/-!
# Who made a target-recorded query

The ordering term's containment asks one thing the recorder cannot answer by itself: that an
input the target recording holds is a query the **record** holds. The recorder sees every query
the run makes, the record only the adversary's and the verifier's, and the two coincide here
because of what the other parties ask.

Key generation asks at canonical inputs, which are not message inputs once the key is no
coincidence. The signer asks at canonical inputs, at its request's own `PRF_msg` input — which
the narrowing excludes — and at its request's own digest input, which is signer-randomised at
the moment it is made, by the answer the signer has just drawn, and so is taken by the left test
rather than the right. Nothing else is left, and the adversary's and the verifier's queries are
recorded by construction.

The provenance is taken at the recorded game: the run is split at its three sequencing points
and the entry attributed to the first phase whose cache holds it. The record is the one the run's
own value carries, which is the one `SharedJoin.recordOf` reads and the one
`RecordedTail.card_eq_work` counts — so the containment lands in the part the join names rather
than in a multiset that merely has the same size.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.LateProvenance

variable {α : Type}

open Security CacheReplay RecordedQueries CacheProvenance PhaseProvenance

/-! ## The verifier records what it asks -/

/-- **A fresh query the verifier's phase installed is in the record it keeps.** The phase charges
and records at the same step, so an entry that was not there before is one of the inputs it
wrote down. -/
theorem mem_record_countRecorded {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (cache : QueryCache HashSpec) (result : (α × Tally) × QueryCache HashSpec),
      result ∈ support ((simulateQ KeygenUniform.rom
        (countRecorded verifierCost computation)).run cache) →
      ∀ probe : Bytes, cache probe = none → result.2 probe ≠ none →
        probe ∈ result.1.2.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache result hmem probe hfresh hpresent
    rw [countRecorded_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    rw [show result.2 = cache from by rw [hmem]] at hpresent
    exact absurd hfresh hpresent
  | query_bind queried next ih =>
    intro cache result hmem probe hfresh hpresent
    rw [countRecorded_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have hcache : result.2 = inner.2 := by rw [← heq]
    have hrecord : result.1.2 = verifierCost queried + inner.1.2 := by rw [← heq]
    rw [hrecord]
    show probe ∈ (verifierCost queried).2 + inner.1.2.2
    by_cases hstepfresh : step.2 probe = none
    · exact Multiset.mem_add.mpr (Or.inr
        (ih step.1 step.2 inner hinner probe hstepfresh (by rw [← hcache]; exact hpresent)))
    · refine Multiset.mem_add.mpr (Or.inl ?_)
      rw [show (verifierCost queried).2 = recordOf queried from rfl,
        show queried = Sum.inr probe from
          queried_of_fresh_step queried cache step (by simpa using hstep) probe hfresh hstepfresh]
      simp [recordOf]

set_option maxHeartbeats 800000 in
/-- **An entry the verifier's phase files as a target is one of its own queries**, hence in the
record it keeps. Who asked is a question the record answers, so this projects the sub-run to the
shared oracle and asks it there — the recorder is needed only where the recording itself is the
question. -/
theorem verify_right_record (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (pk : PublicKey) (message : Message) (signature : Bytes)
    (state : SplitPrefix.SplitState)
    (result : (Bool × Tally) × SplitPrefix.SplitState)
    (hmem : result ∈ support ((simulateQ (SplitPrefix.recorder leftKeep rightKeep)
      (countRecorded verifierCost (Scheme.verify pk message signature))).run state))
    (entry : Bytes × HashOutput) (hentry : entry ∈ result.2.2.2) :
    entry ∈ state.2.2 ∨ entry.1 ∈ result.1.2.2 := by
  classical
  obtain ⟨suffix, hsuffix, hentries⟩ :=
    SplitPrefix.right_record_suffix leftKeep rightKeep _ state result hmem
  rw [hsuffix] at hentry
  rcases List.mem_append.mp hentry with hprior | hnew
  · exact Or.inl hprior
  · obtain ⟨mid, hstart, -, habsent, -, hfinal⟩ := hentries entry hnew
    have hfresh : state.1 entry.1 = none := by
      rcases hstate : state.1 entry.1 with _ | value
      · rfl
      · rw [hstart entry.1 value hstate] at habsent
        exact absurd habsent (by simp)
    refine Or.inr (mem_record_countRecorded _ state.1 (result.1, result.2.1)
      (SplitPrefix.mem_support_rom leftKeep rightKeep _ state result hmem) entry.1 hfresh ?_)
    exact Option.ne_none_iff_exists'.mpr ⟨entry.2, hfinal⟩

/-! ## Two readings of a generated key

Key generation's last line builds the pair, so its secret key carries the seed it was given and
the public key beside it. Both are definitional, and both are stated before the phase splits
make `Scheme.keygenInternal` opaque. -/

theorem keygen_prf (cache : QueryCache HashSpec) (secretSeed prfSeed publicSeed : Digest) :
    (@Scheme.keygenInternal Id Id.instMonad (replayQuery cache)
      secretSeed prfSeed publicSeed).1.prf = prfSeed := rfl

theorem keygen_publicKey (cache : QueryCache HashSpec) (secretSeed prfSeed publicSeed : Digest) :
    (@Scheme.keygenInternal Id Id.instMonad (replayQuery cache)
        secretSeed prfSeed publicSeed).1.publicKey =
      (@Scheme.keygenInternal Id Id.instMonad (replayQuery cache)
        secretSeed prfSeed publicSeed).2 := rfl

/-! ## Where an entry the recorded game installed came from

The run is split at its three sequencing points and the entry attributed to the first phase
whose cache holds it. The verifier's phase is not a case: it records what it asks, so an entry
it installed is already in the record the run's value carries. -/

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

set_option maxHeartbeats 1000000 in
/-- **An entry the recorded game installed is the adversary's or the verifier's own query, key
generation's, or a signing sub-run's.** The record is the one the run's own value carries. -/
theorem provenance_recordedAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec)
    (result : (((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec))
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (RecordedTail.recordedAfterSeeds adversary sds))).run cache)) :
    ∃ keys : SecretKey × PublicKey,
      keys = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
        sds.1 sds.2.1 sds.2.2 ∧
      ∀ probe : Bytes, cache probe = none → result.2 probe ≠ none →
        probe ∈ result.1.1.2 ∨
          QueriesUnder result.2
            (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2) probe ∨
          ∃ entry ∈ result.1.1.1.signed, SignerMade keys.1 result.2 entry.1 probe := by
  rw [RecordedTail.recordedAfterSeeds] at hresult
  obtain ⟨keys, keyCache, keyCount, hkeys, hrest1⟩ :=
    WarmedSplit.mem_support_counted_bind _ _ _ _ hresult
  obtain ⟨sk, pk⟩ := keys
  obtain ⟨value, advCache, advCount, hadv, hrest2⟩ :=
    WarmedSplit.mem_support_counted_bind _ _ _ _ hrest1
  obtain ⟨verified, verifyFinal, verifyCount, hverify, hrest3⟩ :=
    WarmedSplit.mem_support_counted_bind _ _ _ _ hrest2
  rw [GrowthBudget.countAllHashes_pure, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hrest3
  simp only [Prod.mk.injEq] at hrest3
  obtain ⟨⟨houtcome, -⟩, hcache⟩ := hrest3
  have hadvGrow : ∀ (input : Bytes) (output : HashOutput),
      advCache input = some output → result.2 input = some output := by
    intro input output hentry
    rw [hcache]
    exact GrowthCharge.cache_value_persists _ advCache verifyFinal _ hverify input output hentry
  have hkeyGrow : ∀ (input : Bytes) (output : HashOutput),
      keyCache input = some output → result.2 input = some output := by
    intro input output hentry
    exact hadvGrow input output
      (GrowthCharge.cache_value_persists _ keyCache advCache _ hadv input output hentry)
  have hkeyreplay : (sk, pk) = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
      sds.1 sds.2.1 sds.2.2 := by
    rw [WarmedSplit.keygenInternal_liftM, WarmedSplit.run_rom_liftM] at hkeys
    exact WarmedSplit.keygenInternal_eq_replay_of_subset _ _ _ cache keyCache result.2 (sk, pk)
      hkeys hkeyGrow
  refine ⟨(sk, pk), hkeyreplay, ?_⟩
  intro probe hfresh hpresent
  by_cases hkeyFresh : keyCache probe = none
  · by_cases hadvFresh : advCache probe = none
    · refine Or.inl ?_
      rw [show result.1.1.2 = (Multiplicative.toAdd value.1.2).2 + verified.2.2 from by
        rw [houtcome]]
      exact Multiset.mem_add.mpr (Or.inr
        (mem_record_countRecorded _ advCache (verified, verifyFinal) hverify probe hadvFresh
          (by rw [hcache] at hpresent; exact hpresent)))
    · rcases provenance_phase_subset sk (adversary.main pk) [] keyCache (value, advCache) hadv
        result.2 (fun input output hentry => hadvGrow input output hentry)
        probe hkeyFresh hadvFresh with hmem | ⟨entry, hentry, hquery⟩
      · refine Or.inl ?_
        rw [show result.1.1.2 = (Multiplicative.toAdd value.1.2).2 + verified.2.2 from by
          rw [houtcome]]
        exact Multiset.mem_add.mpr (Or.inl hmem)
      · refine Or.inr (Or.inr ⟨entry, ?_, hquery⟩)
        rw [show result.1.1.1.signed = value.2 from by rw [houtcome]]
        exact hentry
  · exact Or.inr (Or.inl (queriesUnder_keygenInternal_of_fresh sds.1 sds.2.1 sds.2.2 cache
      keyCache result.2 (sk, pk) hkeys hkeyGrow probe hfresh hkeyFresh))

/-! ## The containment

The adversary's and the verifier's queries are the record. Key generation's are canonical, and a
canonical input is not a message input once the key is no coincidence. The signer asks at
canonical inputs, at its request's own `PRF_msg` input — which the narrowing excludes — and at its
request's own digest input.

**Replay is faithful to a run only at the run's final cache.** That is the invariant inside
`CacheReplay.cached_of_queriesUnder`: each query's answer is in the final cache, so replaying
there reproduces the continuations the run took. At an *intermediate* cache the replay diverges,
since a miss replays to `default`. So the cases that read the **input alone** — "not
message-class" and "in the `PRF_msg` class at the real seed" are predicates on bytes — are
settled by replay at the final cache. The digest case reads the **state**, and is read at the
step the query was made at, from the signer's own sub-run. -/

set_option maxHeartbeats 1000000 in
/-- **Every target-recorded input is a query the record holds**, with no hypothesis.

The game splits at its three sequencing points and each branch asks its question of the object
that can answer it. Key generation's and the verifier's are about an input's shape and about who
asked, so those sub-runs project to the shared oracle and the lemmas already proved there
answer. The adversary's phase is about the *recording*, so it is asked of the recorder, and its
signer branch is asked of the signer's own sub-run — which hands back the cache the entry was
filed at, the randomiser answer in it, and what the sub-run queried, so the disclosure witness
closes at the frame the entry itself names. -/
theorem hrecord (adversary : Adversary) :
    ∀ pair ∈ support (LateProbes.pairedOf FusedCoverage.fusedTail adversary),
      Target.GoodWalk pair.1 → ∀ entry ∈ pair.2.2.2.2,
        entry.1 ∈ SharedJoin.recordOf (LateProbes.forgetRecordings pair) := by
  classical
  intro pair hpair hgood entry hentry
  obtain ⟨walk, hwalk, result, hresult, hvalue⟩ := LateProbes.mem_support_pairedOf hpair
  subst hvalue
  rw [FusedCoverage.fusedTail] at hresult
  have hpublic := AnswerSide.not_possible_generatedKey hwalk hgood.2
  have hnarrow : SplitWitness.narrowClass walk.1.1.2.1
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) entry.1 :=
    SplitPrefix.right_record_class (FusedCoverage.leftKeepAt walk) (FusedCoverage.rightKeepAt walk)
      (SplitWitness.narrowClass walk.1.1.2.1
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
      (fun input inner hkeep => SplitWitness.Served.targetKeep_narrow _ _ input inner hkeep)
      _ (walk.2, [], []) result hresult (by simp) entry hentry
  -- The game, split at its three sequencing points.
  rw [RecordedTail.recordedAfterSeeds] at hresult
  obtain ⟨keys, keyState, keyCount, keyCount', hkeysCounted, hrest1⟩ :=
    PhaseRightRecord.mem_support_counted_bind _ _ _ _ (walk.2, [], []) result hresult
  obtain ⟨phase, phaseState, phaseCount, phaseCount', hphaseCounted, hrest2⟩ :=
    PhaseRightRecord.mem_support_counted_bind _ _ _ _ keyState _ hrest1
  obtain ⟨verified, verifyState, verifyCount, verifyCount', hverifyCounted, hrest3⟩ :=
    PhaseRightRecord.mem_support_counted_bind _ _ _ _ phaseState _ hrest2
  rw [GrowthBudget.countAllHashes_pure, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hrest3
  simp only [Prod.mk.injEq] at hrest3
  obtain ⟨⟨houtcome, -⟩, hcache⟩ := hrest3
  -- The three sub-runs, with the count off.
  have hkeygen := PhaseRightRecord.mem_support_of_countAllHashes _ _ _ (walk.2, [], [])
    ((keys, keyCount), keyState) hkeysCounted
  have hphase := PhaseRightRecord.mem_support_of_countAllHashes _ _ _ keyState
    ((phase, phaseCount), phaseState) hphaseCounted
  have hverify := PhaseRightRecord.mem_support_of_countAllHashes _ _ _ phaseState
    ((verified, verifyCount), verifyState) hverifyCounted
  -- Each phase's cache survives the ones after it.
  have hverifyGrow : ∀ (probe : Bytes) (value : HashOutput),
      phaseState.1 probe = some value → result.2.1 probe = some value := by
    intro probe value hprobe
    rw [show result.2 = verifyState from hcache]
    exact SplitPrefix.recorder_cache_value_persists _ _ _ phaseState (verified, verifyState)
      hverify probe value hprobe
  have hphaseGrow : ∀ (probe : Bytes) (value : HashOutput),
      keyState.1 probe = some value → result.2.1 probe = some value := fun probe value hprobe =>
    hverifyGrow probe value (SplitPrefix.recorder_cache_value_persists _ _ _ keyState
      (phase, phaseState) hphase probe value hprobe)
  -- Where the entry was filed.
  rw [show result.2 = verifyState from hcache] at hentry
  rcases verify_right_record _ _ keys.2 phase.1.1.message phase.1.1.signature phaseState
      (verified, verifyState) hverify entry hentry with hphaseMem | hrec
  · rcases PhaseRightRecord.right_record_phase _ _ keys.1 (adversary.main keys.2) [] keyState
        (phase, phaseState) hphase result.2.1 hverifyGrow entry hphaseMem with
      hkeyMem | hsource
    · -- Key generation's probes are canonical, which a message input is not.
      rcases PhaseRightRecord.keygen_right_record _ _ walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2
          (walk.2, [], []) (keys, keyState) hkeygen result.2.1 hphaseGrow entry hkeyMem with
        hstart | hkeygenQuery
      · exact absurd hstart (by simp)
      · obtain ⟨randomizer, message, hinput⟩ := hnarrow.1
        obtain ⟨parent, hparent⟩ :=
          HonestProbes.probes_keygenInternal result.2.1 walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2
            entry.1 hkeygenQuery
        exact absurd (hinput ▸ hparent)
          (HashSeparation.message_tweakable_ne hpublic (withinBounds_structural parent))
    · -- The adversary's phase. The key the run generated is the one the walk fixed.
      obtain ⟨outputs, hwarm⟩ := HonestGrowth.walk_cache_eq_warmCache hwalk
      have hkeysRom : (keys, keyState.1) ∈ support ((simulateQ KeygenUniform.rom
          (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 :
            OracleComp OracleWorld (SecretKey × PublicKey))).run walk.2) :=
        SplitPrefix.mem_support_rom _ _ _ (walk.2, [], []) (keys, keyState) hkeygen
      rw [hwarm, HonestProbes.run_keygenInternal_world_eq_pure, support_pure,
        Set.mem_singleton_iff] at hkeysRom
      have hvalue : keys = @Scheme.keygenInternal Id Id.instMonad
          (CacheReplay.replayQuery walk.2) walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 := by
        rw [hwarm]
        exact (Prod.ext_iff.mp hkeysRom).1
      have hprf : keys.1.prf = walk.1.1.2.1 := by
        rw [hvalue]
        exact keygen_prf walk.2 walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2
      have hpk : keys.1.publicKey =
          SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2 := by
        rw [hvalue, SplitCharged.generatedKey]
        exact keygen_publicKey walk.2 walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2
      rcases hsource with hrecMem |
        ⟨framed, hrandomiser | ⟨mid, answer, hmid, -, -, hkeep, hqueries⟩⟩
      · show entry.1 ∈ result.1.1.2
        rw [show result.1.1.2 = (Multiplicative.toAdd phase.1.2).2 + verified.2.2 from by
          rw [houtcome]]
        exact Multiset.mem_add.mpr (Or.inl hrecMem)
      · -- The signer's randomiser probe is the `PRF_msg` class the narrowing removes.
        refine absurd ⟨keys.1.publicKey.seed, framed, ?_⟩ hnarrow.2
        rw [hrandomiser, hprf]
      · -- Its digest probe is signer-randomised at the cache it was filed at.
        rcases SignerRandomiser.probes_signInternalAt result.2.1 (Hashing.truncate answer)
            keys.1 framed entry.1 hqueries with ⟨parent, hparent⟩ | hdigest
        · obtain ⟨randomizer, message, hinput⟩ := hnarrow.1
          exact absurd (hinput ▸ hparent)
            (HashSeparation.message_tweakable_ne hpublic (withinBounds_structural parent))
        · refine absurd (show CacheAvailability.SignerRandomised walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) mid entry.1
            from ⟨framed, answer, ?_, ?_⟩) hkeep.2
          · rw [hprf, hpk] at hmid
            exact hmid
          · rw [hdigest, hpk]
  · show entry.1 ∈ result.1.1.2
    rw [show result.1.1.2 = (Multiplicative.toAdd phase.1.2).2 + verified.2.2 from by
      rw [houtcome]]
    exact Multiset.mem_add.mpr (Or.inr hrec)

end SlhDsaSecurity.LateProvenance
