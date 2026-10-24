/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedGame
public import HashSig.SLHDSA.SHAKE128s.Proof.GameBridge

/-!
# An accepted forgery in a warmed tail, read at the walk's own honest key

`GameBridge` and `HypertreeDispatch.cases_of_accepted` are the structural reduction, but they
speak about `Id`-level operations under `CacheReplay.replayQuery` of a single cache.
`WarmedGame.tail` is a probabilistic run of the whole game. This file is the passage from one
to the other: an accepted forgery in a warmed tail yields the three extraction cases, stated
against *this* run's final cache and *this* walk's seeds.

Three things have to be arranged, and each is a lemma here.

* **Factoring the run.** `WarmedGame.afterSeeds` is key generation, then the adversary, then
  verification, then a `pure`. `mem_support_counted_bind` factors a counted run at any sequencing
  point — the prefix as an *uncounted* sub-run, the suffix from the cache the prefix left — and
  `split_afterSeeds` applies it three times. The instrumentation is pushed out of the way first:
  `countAllHashes` and `countQueries` issue exactly the queries of what they wrap, so their runs
  have the same value and the same final cache.

* **Which cache each phase ends at.** Verification is the last phase that queries anything, so its
  final cache *is* the run's final cache — that is what `GameBridge.verify_eq_replay` needs, and the
  trailing `pure` is what supplies it. Key generation ends much earlier, at a cache the adversary
  and the verifier then extend. Entries never change along a run
  (`GrowthCharge.cache_value_persists`), so `run_eq_replay_of_subset` —
  `CacheReplay.run_eq_replay` relaxed to replay against any cache extending the run's own —
  recovers the generated key from the *final* cache all the same.

* **Crossing from the game's world to the hash-only one.** The scheme's operations are written
  against `[HasQuery HashSpec m]`, so in the game's world they are the hash-only ones lifted
  (`verify_liftM`, `keygenInternal_liftM`), and `rom` routes a lifted computation to `randomOracle`
  alone (`run_rom_liftM`).

The one obstruction worth naming is that `WarmedGame.afterSeeds` and the scheme's operations must be
opaque everywhere except in `split_afterSeeds`, where the factoring happens. Left reducible they
unfold into the whole game, and even a step that closes a goal with a syntactically identical
hypothesis exhausts the heartbeat budget.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.WarmedSplit

variable {α β : Type}

open Security

/-! ## From the game's world to the hash-only one -/

/-- `rom` routes a lifted hash-only computation to `randomOracle`. -/
theorem run_rom_liftM {α : Type} (computation : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom (liftM computation : OracleComp OracleWorld α)).run cache =
      (simulateQ randomOracle computation).run cache := by
  rw [show KeygenUniform.rom = unifFwdImpl HashSpec + (randomOracle :
      QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) from rfl,
    QueryImpl.simulateQ_add_liftM_right]

/-- The game's verifier is the hash-only verifier, lifted. -/
theorem verify_liftM (pk : PublicKey) (request : Message) (signature : Bytes) :
    (Scheme.verify pk request signature : OracleComp OracleWorld Bool) =
      liftM (Scheme.verify (m := OracleComp HashSpec) pk request signature) := by
  rw [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_def]
  exact (VerifierNaturality.verify_simulate (m := OracleComp OracleWorld)
    (fun t => liftM (HashSpec.query t)) (fun _ => rfl) pk request signature).symm

/-- The game's key generation is the hash-only key generation, lifted. -/
theorem keygenInternal_liftM (secretSeed prfSeed publicSeed : Digest) :
    (Scheme.keygenInternal secretSeed prfSeed publicSeed :
        OracleComp OracleWorld (SecretKey × PublicKey)) =
      liftM (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed) := by
  rw [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_def]
  exact (Correctness.Naturality.keygenInternal_simulate (m := OracleComp OracleWorld)
    (fun t => liftM (HashSpec.query t)) (fun _ => rfl) secretSeed prfSeed publicSeed).symm

/-! ## Replaying against a later cache

`CacheReplay.run_eq_replay` reproduces a run from the cache that run itself ended at. Key
generation's cache is not the game's final one, so the replay has to be relaxed: since entries
never change, replaying against any cache that extends the sub-run's final cache answers every
query the sub-run made in the same way, and therefore computes the same value. -/

/-- Replaying against any cache that extends the run's own final cache computes the same value.
-/
theorem run_eq_replay_of_subset {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache laterCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (hlater : ∀ (input : Bytes) (output : HashOutput),
      finalCache input = some output → laterCache input = some output) :
    result = simulateQ (CacheReplay.replay laterCache) computation := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    simp only [Prod.mk.injEq] at hmem
    obtain ⟨rfl, -⟩ := hmem
    rw [simulateQ_pure]
    rfl
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    have hfinal : finalCache input = some step.1 :=
      CacheReplay.cache_value_persists (next step.1) step.2 finalCache result hrest input step.1
        (CacheReplay.step_cached input initialCache step hstep)
    rw [ih step.1 step.2 result hrest, simulateQ_bind, simulateQ_spec_query]
    have hreplay : CacheReplay.replay laterCache input = step.1 := by
      simp [CacheReplay.replay, hlater input step.1 hfinal]
    rw [hreplay]
    rfl

/-- **What the game generated, a later cache still generates.** -/
theorem keygenInternal_eq_replay_of_subset (secretSeed prfSeed publicSeed : Digest)
    (initialCache finalCache laterCache : QueryCache HashSpec) (keys : SecretKey × PublicKey)
    (hmem : (keys, finalCache) ∈
      support ((simulateQ randomOracle
        (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed)).run
          initialCache))
    (hlater : ∀ (input : Bytes) (output : HashOutput),
      finalCache input = some output → laterCache input = some output) :
    keys = @Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery laterCache)
      secretSeed prfSeed publicSeed := by
  rw [run_eq_replay_of_subset _ initialCache finalCache laterCache keys hmem hlater]
  exact @Correctness.Naturality.keygenInternal_simulate Id Id.instMonad _
    (CacheReplay.replay laterCache) (CacheReplay.replayQuery laterCache)
    (GameBridge.replay_agrees laterCache) secretSeed prfSeed publicSeed

/-! ## Seeing past the instrumentation

Both counters wrap a computation in a writer that records a per-query cost. Neither issues a query
of its own, so a counted run has exactly the value and the final cache of the run it wraps, and a
counted run of a sequencing factors into an uncounted prefix and a counted suffix. -/

/-- The `Counts` instrumentation, peeled one query at a time. -/
theorem countQueries_query_bind {α : Type} (cost : OracleWorld.Domain → Counts)
    (queried : OracleWorld.Domain)
    (next : OracleWorld.Range queried → OracleComp OracleWorld α) :
    countQueries cost (liftM (OracleWorld.query queried) >>= next) =
      liftM (OracleWorld.query queried) >>= fun answer =>
        (fun result => (result.1, cost queried + result.2)) <$>
          countQueries cost (next answer) := by
  simp only [countQueries, simulateQ_bind, simulateQ_spec_query, addCostOracle,
    QueryImpl.withAddCost, QueryImpl.withCost]
  simp [Functor.map_map, map_bind, bind_map_left]

/-- Instrumentation adds bookkeeping to the value and nothing to the oracle: a counted run's
value and final cache are those of the underlying run. -/
theorem mem_support_of_countAllHashes {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (result : (α × Nat) × QueryCache HashSpec)
    (hmem : result ∈
      support ((simulateQ KeygenUniform.rom (countAllHashes computation)).run cache)) :
    (result.1.1, result.2) ∈ support ((simulateQ KeygenUniform.rom computation).run cache) := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
    rw [GrowthBudget.countAllHashes_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    subst hmem
    rw [simulateQ_pure, StateT.run_pure, support_pure]
    rfl
  | query_bind queried next ih =>
    rw [GrowthBudget.countAllHashes_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    refine ⟨step, hstep, ?_⟩
    rw [show result.1.1 = inner.1.1 from by rw [← heq], show result.2 = inner.2 from by rw [← heq]]
    exact ih step.1 step.2 inner hinner

/-- The same for the `Counts`-valued instrumentation. -/
theorem mem_support_of_countQueries {α : Type} (cost : OracleWorld.Domain → Counts)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (result : (α × Counts) × QueryCache HashSpec)
    (hmem : result ∈
      support ((simulateQ KeygenUniform.rom (countQueries cost computation)).run cache)) :
    (result.1.1, result.2) ∈ support ((simulateQ KeygenUniform.rom computation).run cache) := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
    rw [VerificationBudget.countQueries_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    subst hmem
    rw [simulateQ_pure, StateT.run_pure, support_pure]
    rfl
  | query_bind queried next ih =>
    rw [countQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    refine ⟨step, hstep, ?_⟩
    rw [show result.1.1 = inner.1.1 from by rw [← heq], show result.2 = inner.2 from by rw [← heq]]
    exact ih step.1 step.2 inner hinner

/-- **A counted run factors at every sequencing point.** The prefix is an ordinary, uncounted
sub-run, and the suffix picks up from the cache the prefix left. -/
theorem mem_support_counted_bind {α β : Type} (computation : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec)
    (result : (β × Nat) × QueryCache HashSpec)
    (hmem : result ∈
      support ((simulateQ KeygenUniform.rom
        (countAllHashes (computation >>= next))).run cache)) :
    ∃ (value : α) (middleCache : QueryCache HashSpec) (count : Nat),
      (value, middleCache) ∈ support ((simulateQ KeygenUniform.rom computation).run cache) ∧
        ((result.1.1, count), result.2) ∈
          support ((simulateQ KeygenUniform.rom (countAllHashes (next value))).run
            middleCache) := by
  rw [GrowthBudget.countAllHashes_bind, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨first, hfirst, hrest⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨second, hsecond, hpure⟩ := hrest
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  refine ⟨first.1.1, first.2, second.1.2, mem_support_of_countAllHashes _ _ _ hfirst, ?_⟩
  rw [show result.1.1 = second.1.1 from by rw [hpure],
    show result.2 = second.2 from by rw [hpure]]
  exact hsecond

/-! ## Factoring the game

From here on the scheme's operations are opaque: the factoring below needs only that
`WarmedGame.afterSeeds` is a sequence of four phases, and leaving the phases themselves reducible
unfolds the entire game into every unification the proof performs. -/

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

/-- **The counted game factors at its honest key and at its verification.** The key the game
generated is the value of a genuine key-generation sub-run from the starting cache; the
verification is the last phase, so its final cache is the run's own; and everything key
generation cached is still cached at the end. -/
theorem split_afterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec) (result : (Outcome × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (WarmedGame.afterSeeds adversary sds))).run cache)) :
    ∃ (keys : SecretKey × PublicKey) (keyCache verifyCache : QueryCache HashSpec),
      (keys, keyCache) ∈ support ((simulateQ KeygenUniform.rom
        (Scheme.keygenInternal sds.1 sds.2.1 sds.2.2)).run cache) ∧
      (∀ (input : Bytes) (output : HashOutput),
        keyCache input = some output → result.2 input = some output) ∧
      (result.1.1.verified, result.2) ∈ support ((simulateQ KeygenUniform.rom
        (Scheme.verify keys.2 result.1.1.forgery.message result.1.1.forgery.signature)).run
          verifyCache) := by
  unfold WarmedGame.afterSeeds at hresult
  obtain ⟨keys, keyCache, keyCount, hkeys, hrest1⟩ := mem_support_counted_bind _ _ _ _ hresult
  obtain ⟨sk, pk⟩ := keys
  obtain ⟨⟨⟨forgery, adversaryCounts⟩, signed⟩, advCache, advCount, hadv, hrest2⟩ :=
    mem_support_counted_bind _ _ _ _ hrest1
  obtain ⟨⟨verified, verifierCounts⟩, verifyFinal, verifyCount, hverify, hrest3⟩ :=
    mem_support_counted_bind _ _ _ _ hrest2
  rw [GrowthBudget.countAllHashes_pure, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hrest3
  simp only [Prod.mk.injEq] at hrest3
  obtain ⟨⟨hvalue, -⟩, hcache⟩ := hrest3
  refine ⟨(sk, pk), keyCache, advCache, hkeys, ?_, ?_⟩
  · intro input output hentry
    rw [hcache]
    exact GrowthCharge.cache_value_persists _ advCache verifyFinal _ hverify input output
      (GrowthCharge.cache_value_persists _ keyCache advCache _ hadv input output hentry)
  · rw [hvalue, hcache]
    exact mem_support_of_countQueries _ _ _ _ hverify

attribute [local irreducible] WarmedGame.afterSeeds

/-! ## The three cases

Composing the pieces: the key the game generated is the replayed key of the run's final cache, the
verdict the game reached is the replayed verifier's verdict on that key, and
`HypertreeDispatch.cases_of_accepted` takes it from there.

The honest FORS public key is left *universally* quantified, matching
`HypertreeDispatch.cases_of_accepted`'s own parameter: for whichever key the FORS side names as the
honest one, either the forgery's recovered FORS key is that key or the hypertree carries a fault.
Quantifying it existentially instead would make the first disjunct true by choosing the recovered
key itself, and say nothing.

The fault is `Extraction.HypertreeChain.HypertreeFault` itself, at the forgery's own signature
array, rather than a flattened "some layer collides" — a predicate that forgets which signature it
is about can be satisfied by building one, and cannot supply the cache entry every charge
composition requires. -/

/-- **An accepted forgery in a warmed tail is canonical at the walk's own honest key,
or the hypertree carries a fault.** -/
theorem cases_of_win (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (hverified : result.1.1.verified = true) :
    ∃ (message : Bytes) (parsed : Signature),
      result.1.1.forgery.message.frame = some message ∧
        Signature.fromBytes? result.1.1.forgery.signature = some parsed ∧
          ∀ honestForsKey : Digest,
            @SLHDSA.SHAKE128s.Fors.publicKeyFromSignature Id Id.instMonad
                (CacheReplay.replayQuery result.2) parsed.fors
                (MessageDigest.forsIndices
                  (@Hashing.messageDigest Id (CacheReplay.replayQuery result.2)
                    parsed.randomizer
                    (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery result.2)
                      walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2).2 message))
                (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery result.2)
                  walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2).2.seed
                (Scheme.forsAddress
                  (@Hashing.messageDigest Id (CacheReplay.replayQuery result.2)
                    parsed.randomizer
                    (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery result.2)
                      walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2).2 message)) = honestForsKey ∨
              @Extraction.HypertreeChain.HypertreeFault (CacheReplay.replayQuery result.2)
                walk.1.1.1 walk.1.1.2.2 layers parsed.hypertree 0
                (MessageDigest.treeIndex
                  (@Hashing.messageDigest Id (CacheReplay.replayQuery result.2)
                  parsed.randomizer
                  (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery result.2)
                    walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2).2 message)).toNat
                (MessageDigest.leafIndex
                  (@Hashing.messageDigest Id (CacheReplay.replayQuery result.2)
                  parsed.randomizer
                  (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery result.2)
                    walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2).2 message)).toFin
                (@SLHDSA.SHAKE128s.Fors.publicKeyFromSignature Id Id.instMonad
                (CacheReplay.replayQuery result.2) parsed.fors
                (MessageDigest.forsIndices
                  (@Hashing.messageDigest Id (CacheReplay.replayQuery result.2)
                  parsed.randomizer
                  (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery result.2)
                    walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2).2 message))
                (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery result.2)
                  walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2).2.seed
                (Scheme.forsAddress (@Hashing.messageDigest Id (CacheReplay.replayQuery result.2)
                  parsed.randomizer
                  (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery result.2)
                    walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2).2 message)))
                honestForsKey := by
  unfold WarmedGame.tail at hresult
  obtain ⟨keys, keyCache, verifyCache, hkeys, hpersist, hverify⟩ :=
    split_afterSeeds adversary walk.1.1 walk.2 result hresult
  rw [keygenInternal_liftM, run_rom_liftM] at hkeys
  rw [verify_liftM, run_rom_liftM] at hverify
  have hkeyreplay : keys = @Scheme.keygenInternal Id Id.instMonad
      (CacheReplay.replayQuery result.2) walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 :=
    keygenInternal_eq_replay_of_subset _ _ _ walk.2 keyCache result.2 keys hkeys hpersist
  have hverifyreplay : result.1.1.verified =
      @Scheme.verify Id Id.instMonad (CacheReplay.replayQuery result.2) keys.2
        result.1.1.forgery.message result.1.1.forgery.signature :=
    GameBridge.verify_eq_replay keys.2 _ _ verifyCache result.2 _ hverify
  have haccept : @Scheme.verify Id Id.instMonad (CacheReplay.replayQuery result.2)
      (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery result.2)
        walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2).2
      result.1.1.forgery.message result.1.1.forgery.signature = true := by
    rw [← congrArg Prod.snd hkeyreplay, ← hverifyreplay, hverified]
  obtain ⟨message, parsed, hframe, hparsed, hinternal⟩ :=
    @GameBridge.verifyInternal_of_verify (CacheReplay.replayQuery result.2) _ _ _ haccept
  refine ⟨message, parsed, hframe, hparsed, fun honestForsKey => ?_⟩
  exact @HypertreeDispatch.cases_of_accepted (CacheReplay.replayQuery result.2)
    walk.1.1.1 walk.1.1.2.2 _ _ _ _ honestForsKey _
    (GameBridge.keygen_publicKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2).1
    (GameBridge.keygen_publicKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2).2
    (@GameBridge.hypertree_of_verifyInternal (CacheReplay.replayQuery result.2) _ _ _ hinternal)

end SLHDSA.SHAKE128s.WarmedSplit
