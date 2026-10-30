/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareRealCap
public import HashSig.SLHDSA.SHAKE128s.Proof.CoverageCount

/-!
# The real game and the lenient game, coupled

The lenient handler is the real game in another representation. Its state splits the real
oracle's cache three ways — the walk's table, the signer's `PRF_msg` answers keyed by frame, and
everything else — and `realView` puts them back together. This file couples the two games step
by step, with the real cache equal to the view of the lenient state, and with every input the
real game records also filed in the lenient record.

The coupling is built up one oracle step at a time: `couple_hash` is one hash query (the real
oracle at the view, against the lenient routing); `real_sign_framed` and
`advImpl_sign_framed_run` unfold a framed signing request on either side into two such queries
and a table read; `couple_adv` couples one adversary step under the invariant `Rel`; and
`couple_verify` couples one verifier step under `RelV`, which also keeps the digests the
adversary's phase served.
-/

public section

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace SLHDSA.SHAKE128s.ShareCouple

open Security CanonicalGraph ShareGame

/-! ## The real cache, as a view of the lenient state -/

open scoped Classical in
/-- The oracle's entries off the table: the signer's `PRF_msg` answers at their inputs, and
everything else from the plain cache. -/
@[expose] noncomputable def merged (setup : Setup) (state : St) : QueryCache HashSpec :=
  QueryCache.ofFn fun input =>
  if IsPrfInput setup input then state.prfs (prfFrame input) else state.cache input

/-- **The real oracle's cache**, read off the lenient state. -/
@[expose] noncomputable def realView (setup : Setup) (state : St) : QueryCache HashSpec :=
  QueryCache.ofFn fun input =>
  match setup.warm input with
  | some answer => some answer
  | none => merged setup state input

/-- The view at a warm-table input is the table's answer. -/
theorem realView_of_warm (setup : Setup) (state : St) (input : Bytes) (answer : HashOutput)
    (hwarm : setup.warm input = some answer) : realView setup state input = some answer := by
  simp [realView, hwarm]

/-- Off the warm table, the view is the merged cache. -/
theorem realView_of_not_warm (setup : Setup) (state : St) (input : Bytes)
    (hwarm : setup.warm input = none) :
    realView setup state input = merged setup state input := by
  simp [realView, hwarm]

/-- A `PRF_msg` input at the real seed is named by its frame. -/
theorem eq_of_isPrfInput (setup : Setup) {input other : Bytes}
    (hinput : IsPrfInput setup input) (hother : IsPrfInput setup other)
    (hframe : prfFrame input = prfFrame other) : input = other := by
  rw [hinput, hother, hframe]

/-- **Answering a `PRF_msg` input from the frame table is caching it.** -/
theorem realView_prfs_update (setup : Setup) (state : St) (input : Bytes)
    (hwarm : setup.warm input = none) (hprf : IsPrfInput setup input) (answer : HashOutput) :
    realView setup
        { state with prfs := Function.update state.prfs (prfFrame input) (some answer) } =
      (realView setup state).cacheQuery input answer := by
  classical
  ext other
  by_cases hother : other = input
  · subst hother
    simp [realView, hwarm, merged, hprf, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ hother]
    simp only [realView, merged, QueryCache.ofFn_apply]
    cases hw : setup.warm other with
    | some a => rfl
    | none =>
      simp only
      by_cases hprfOther : IsPrfInput setup other
      · rw [ite_eq_left hprfOther, ite_eq_left hprfOther, Function.update_of_ne]
        exact fun hframe => hother (eq_of_isPrfInput setup hprfOther hprf hframe)
      · rw [ite_eq_right hprfOther, ite_eq_right hprfOther]

/-- **Answering any other input from the plain cache is caching it.** -/
theorem realView_cache_update (setup : Setup) (state : St) (input : Bytes)
    (hwarm : setup.warm input = none) (hprf : ¬ IsPrfInput setup input) (answer : HashOutput) :
    realView setup { state with cache := state.cache.cacheQuery input answer } =
      (realView setup state).cacheQuery input answer := by
  classical
  ext other
  by_cases hother : other = input
  · subst hother
    simp [realView, hwarm, merged, hprf, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ hother]
    simp only [realView, merged, QueryCache.ofFn_apply]
    cases hw : setup.warm other with
    | some a => rfl
    | none =>
      simp only
      by_cases hprfOther : IsPrfInput setup other
      · rw [ite_eq_left hprfOther, ite_eq_left hprfOther]
      · rw [ite_eq_right hprfOther, ite_eq_right hprfOther,
          QueryCache.cacheQuery_of_ne _ _ hother]

/-! ## One hash query -/

/-- What one routed hash query leaves of the lenient state: everything but the two caches. -/
@[expose] def Quiet (state next : St) : Prop :=
  next.served = state.served ∧ next.record = state.record ∧ next.log = state.log

open scoped Classical in
/-- **One hash query, coupled.** The real oracle at the view and the lenient routing give the same
answer, and the real oracle's new cache is the view of the lenient state's. -/
theorem couple_hash (setup : Setup) (state : St) (input : Bytes) :
    RelTriple ((KeygenUniform.rom (Sum.inr input)).run (realView setup state))
      (route true setup state input)
      (fun p q => p.1 = q.1 ∧ p.2 = realView setup q.2 ∧ Quiet state q.2) := by
  classical
  cases hwarm : setup.warm input with
  | some answer =>
    rw [CoverageCount.rom_run_inr_some input _ answer (realView_of_warm setup state input answer
      hwarm)]
    have hroute : route true setup state input = pure (answer, state) := by
      simp [route, hwarm]
    rw [hroute]
    exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, rfl⟩
  | none =>
    by_cases hprf : IsPrfInput setup input
    · cases hcached : state.prfs (prfFrame input) with
      | some answer =>
        have hview : realView setup state input = some answer := by
          rw [realView_of_not_warm setup state input hwarm, merged, QueryCache.ofFn_apply,
            ite_eq_left hprf, hcached]
        rw [CoverageCount.rom_run_inr_some input _ answer hview]
        have hroute : route true setup state input = pure (answer, state) := by
          simp [route, hwarm, hprf, prfAt, hcached]
        rw [hroute]
        exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, rfl⟩
      | none =>
        have hview : realView setup state input = none := by
          rw [realView_of_not_warm setup state input hwarm, merged, QueryCache.ofFn_apply,
            ite_eq_left hprf, hcached]
        rw [CoverageCount.rom_run_inr_none input _ hview]
        have hroute : route true setup state input =
            (($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
              pure (value, { state with
                prfs := Function.update state.prfs (prfFrame input) (some value) })) := by
          simp [route, hwarm, hprf, prfAt, hcached]
        rw [hroute, map_eq_bind_pure_comp]
        refine relTriple_bind relTriple_uniformSample_refl fun a b hab => ?_
        cases hab
        refine relTriple_pure_pure ⟨rfl, ?_, rfl, rfl, rfl⟩
        exact (realView_prfs_update setup state input hwarm hprf a).symm
    · cases hcached : state.cache input with
      | some answer =>
        have hview : realView setup state input = some answer := by
          rw [realView_of_not_warm setup state input hwarm, merged, QueryCache.ofFn_apply,
            ite_eq_right hprf, hcached]
        rw [CoverageCount.rom_run_inr_some input _ answer hview]
        have hroute : route true setup state input = pure (answer, state) := by
          simp [route, hwarm, hprf, plain, hcached]
        rw [hroute]
        exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, rfl⟩
      | none =>
        have hview : realView setup state input = none := by
          rw [realView_of_not_warm setup state input hwarm, merged, QueryCache.ofFn_apply,
            ite_eq_right hprf, hcached]
        rw [CoverageCount.rom_run_inr_none input _ hview]
        have hroute : route true setup state input =
            (($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
              pure (value, { state with cache := state.cache.cacheQuery input value })) := by
          simp [route, hwarm, hprf, plain, hcached]
        rw [hroute, map_eq_bind_pure_comp]
        refine relTriple_bind relTriple_uniformSample_refl fun a b hab => ?_
        cases hab
        refine relTriple_pure_pure ⟨rfl, ?_, rfl, rfl, rfl⟩
        exact (realView_cache_update setup state input hwarm hprf a).symm

/-! ## The signer's `PRF_msg` query is a routed query -/

/-- The frame of a `PRF_msg` input is the framed message it was built from. -/
theorem prfFrame_randomizerInput (prf seed : Digest) (framed : Bytes) :
    prfFrame (Hashing.randomizerInput prf seed framed) = framed := by
  unfold prfFrame Hashing.randomizerInput
  rw [List.append_assoc, two_mul, ← List.drop_drop, List.drop_left' (length_bytesBE n prf),
    List.drop_left' (length_bytesBE n seed)]

/-- The signer's `PRF_msg` input at the real seeds is a `PRF_msg` input. -/
theorem isPrfInput_randomizerInput (setup : Setup) (framed : Bytes) :
    IsPrfInput setup (Hashing.randomizerInput setup.prf setup.publicSeed framed) := by
  unfold IsPrfInput
  rw [prfFrame_randomizerInput]

/-- On a good walk, the warm table holds no `PRF_msg` input. -/
theorem warm_randomizerInput (setup : Setup) (hgood : setup.Good) (framed : Bytes) :
    setup.warm (Hashing.randomizerInput setup.prf setup.publicSeed framed) = none := by
  by_contra hsome
  obtain ⟨parent, hparent⟩ := Programming.cacheFrom_empty_canonical setup.publicSeed
    setup.table.1 (fullOutput setup.table.1 setup.table.2) Programming.order _ hsome
  rw [canonicalInput] at hparent
  exact HashSeparation.randomizer_tweakable_ne hgood.1 hparent

open scoped Classical in
/-- **The signer's `PRF_msg` draw is the routed query at its input**, on a good walk. -/
theorem prfAt_eq_route (setup : Setup) (hgood : setup.Good) (state : St) (framed : Bytes) :
    prfAt state framed =
      route true setup state (Hashing.randomizerInput setup.prf setup.publicSeed framed) := by
  classical
  simp [route, warm_randomizerInput setup hgood, isPrfInput_randomizerInput,
    prfFrame_randomizerInput]

/-! ## The real signer, one framed request -/

/-- The setup's warm table is the honest probes' warm cache at its table. -/
theorem warm_eq_warmCache (setup : Setup) :
    setup.warm = HonestProbes.warmCache setup.publicSeed (setup.table.1 Node.secretSeed)
      (fullOutput setup.table.1 setup.table.2) :=
  TableTail.walkOfTable_cache setup.prf setup.publicSeed setup.table

/-- **The real signer at a framed request is two oracle steps and a table read.** -/
theorem real_sign_framed (setup : Setup) (hgood : setup.Good) (request : Message)
    (framed : Bytes) (hframe : request.frame = some framed) (cache : QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom (StrippedGame.strippedSign setup.warm setup.sk request)).run
        cache =
      (KeygenUniform.rom (Sum.inr (Hashing.randomizerInput setup.prf setup.publicSeed framed))).run
          cache >>= fun p =>
        (KeygenUniform.rom (Sum.inr (Hashing.messageInput (Hashing.truncate p.1) setup.pk
            framed))).run p.2 >>= fun q =>
          (pure (some (ShareSigner.cellSig setup.warm setup.sk (Hashing.truncate p.1) q.1).toBytes,
            q.2) : ProbComp (Option Bytes × QueryCache HashSpec)) := by
  have hrand : HonestProbes.warmCache setup.sk.publicKey.seed setup.sk.seed
      (fullOutput setup.table.1 setup.table.2)
      (Hashing.randomizerInput setup.sk.prf setup.sk.publicKey.seed framed) = none := by
    have h := warm_randomizerInput setup hgood framed
    rw [warm_eq_warmCache] at h
    exact h
  have hdigest : ∀ seed : HashOutput, HonestProbes.warmCache setup.sk.publicKey.seed setup.sk.seed
      (fullOutput setup.table.1 setup.table.2)
      (Hashing.messageInput (Hashing.truncate seed) setup.sk.publicKey framed) = none := by
    intro seed
    have h := ShareUntilBad.warm_messageInput setup hgood (Hashing.truncate seed) framed
    rw [warm_eq_warmCache] at h
    exact h
  have hdraw := ShareSigner.strippedSign_eq_draw setup.sk (fullOutput setup.table.1 setup.table.2)
    request framed hframe hrand hdigest
  rw [show HonestProbes.warmCache setup.sk.publicKey.seed setup.sk.seed
      (fullOutput setup.table.1 setup.table.2) = setup.warm from (warm_eq_warmCache setup).symm]
    at hdraw
  rw [hdraw]
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    HasQuery.instOfMonadLift_query, simulateQ_spec_query]
  rfl

/-! ## The lenient handler at the adversary's oracles -/

/-- The lenient adversary handler at a world query is the lenient handler at it. -/
theorem advImpl_world_run (lenient : Bool) (setup : Setup) (world : OracleWorld.Domain)
    (p : St × Bool) :
    ((ShareFlag.advImpl lenient setup) (Sum.inl world)).run p =
      ((handler lenient setup) (worldQuery world)).run p := by
  simp only [ShareFlag.advImpl, QueryImpl.apply_compose, splitter, worldQuery,
    HasQuery.instOfMonadLift_query]
  erw [simulateQ_spec_query]

/-- The lenient adversary handler at a signing request is the handler's request step
followed by its response step. -/
theorem advImpl_sign_run (lenient : Bool) (setup : Setup) (request : Message) (p : St × Bool) :
    ((ShareFlag.advImpl lenient setup) (Sum.inr request)).run p =
      ((handler lenient setup) (Sum.inl (Sum.inl (Sum.inr request)))).run p >>= fun q =>
        ((handler lenient setup) (Sum.inl (Sum.inr (request, q.1)))).run q.2 := by
  simp only [ShareFlag.advImpl, QueryImpl.apply_compose, splitter,
    HasQuery.instOfMonadLift_query, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

/-! ## The relation -/

/-- **The coupling's invariant at the adversary's phase**: the real cache is the view of the
lenient state, the logs agree, and every input the real game records is filed in the lenient
record. -/
structure Rel (setup : Setup) (real : SharePresent.RealState) (lenient : St × Bool) : Prop where
  /-- The real cache is the view of the lenient state. -/
  cache : real.2.2 = realView setup lenient.1
  /-- The real signing log is the lenient one. -/
  log : real.2.1 = lenient.1.log
  /-- Every input the real game records is filed in the lenient record. -/
  record : ∀ input ∈ (Multiplicative.toAdd real.1).2, ∃ entry ∈ lenient.1.record, entry.1 = input

/-- The view ignores the lenient record. -/
theorem realView_with_record (setup : Setup) (state : St)
    (record : List (Bytes × List HashOutput)) :
    realView setup { state with record := record } = realView setup state := rfl

/-! ## One adversary step, coupled -/

/-- The real signer at an unframed request answers `none` and leaves the cache alone. -/
theorem real_sign_unframed (warm : QueryCache HashSpec) (sk : SecretKey) (request : Message)
    (hframe : request.frame = none) (cache : QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom (StrippedGame.strippedSign warm sk request)).run cache =
      (pure (none, cache) : ProbComp (Option Bytes × QueryCache HashSpec)) := by
  unfold StrippedGame.strippedSign Scheme.sign
  simp [hframe]

open scoped Classical in
/-- The lenient handler at a hash query routes it, files it in the record at the current
served digests, and raises the flag on a bad setup or a guess. -/
theorem handler_hash_run (lenient : Bool) (setup : Setup) (input : Bytes) (state : St)
    (flag : Bool) :
    ((handler lenient setup) (Sum.inl (Sum.inl (Sum.inl (Sum.inr input))))).run (state, flag) =
      route lenient setup state input >>= fun step =>
        pure (step.1, ({ step.2 with record := state.record ++ [(input, state.served)] },
          flag || decide (¬ setup.Good ∨ Guess setup state.served input))) := rfl

open scoped Classical in
/-- **A framed signing request, at the lenient handler**: two routed queries, then the table
read. -/
theorem advImpl_sign_framed_run (setup : Setup) (hgood : setup.Good) (request : Message)
    (framed : Bytes) (hframe : request.frame = some framed) (state : St) (flag : Bool) :
    ((ShareFlag.advImpl true setup) (Sum.inr request)).run (state, flag) =
      route true setup state (Hashing.randomizerInput setup.prf setup.publicSeed framed) >>=
        fun seed => route true setup seed.2
            (Hashing.messageInput (Hashing.truncate seed.1) setup.pk framed) >>= fun digest =>
          pure (some (ShareSigner.cellSig setup.warm setup.sk (Hashing.truncate seed.1)
              digest.1).toBytes,
            ({ digest.2 with
                served := digest.2.served ++ [digest.1]
                record := state.record ++
                  [(Hashing.messageInput (Hashing.truncate seed.1) setup.pk framed, state.served)]
                log := digest.2.log ++ [⟨request, some (ShareSigner.cellSig setup.warm setup.sk
                  (Hashing.truncate seed.1) digest.1).toBytes⟩] },
              flag || decide (¬ setup.Good ∨ Guess setup state.served
                (Hashing.messageInput (Hashing.truncate seed.1) setup.pk framed)))) := by
  rw [advImpl_sign_run]
  simp [handler, StateT.run, hframe, ← prfAt_eq_route setup hgood, bind_assoc]

/-- After a hash query, every input of the real record is filed in the lenient record extended
by that query's entry. -/
theorem rel_record_hash (setup : Setup) (real : SharePresent.RealState) (lenient : St × Bool)
    (hrel : Rel setup real lenient) (input : Bytes) :
    ∀ x ∈ (Multiplicative.toAdd (real.1 * Multiplicative.ofAdd
        (RecordedPhase.phaseCost (Sum.inl (Sum.inr input))))).2,
      ∃ entry ∈ (lenient.1.record ++ [(input, lenient.1.served)]), entry.1 = x := by
  intro x hx
  simp only [toAdd_mul, toAdd_ofAdd, Prod.snd_add, RecordedPhase.phaseCost,
    RecordedQueries.recordOf, Multiset.mem_add, Multiset.mem_singleton] at hx
  rcases hx with hold | rfl
  · obtain ⟨entry, hentry, hx⟩ := hrel.record x hold
    exact ⟨entry, List.mem_append_left _ hentry, hx⟩
  · exact ⟨(x, lenient.1.served), List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

/-- **One adversary step, coupled.** -/
theorem couple_adv (setup : Setup) (hgood : setup.Good)
    (queried : (OracleWorld + SigningSpec).Domain)
    (real : SharePresent.RealState) (lenient : St × Bool) (hrel : Rel setup real lenient) :
    RelTriple ((SharePresent.realImpl (StrippedGame.strippedSign setup.warm setup.sk) queried).run
        real)
      ((ShareFlag.advImpl true setup queried).run lenient)
      (fun p q => p.1 = q.1 ∧ Rel setup p.2 q.2) := by
  classical
  obtain ⟨lstate, flag⟩ := lenient
  rcases queried with (coin | input) | request
  · rw [SharePresent.realImpl_world_run, advImpl_world_run, DigestTape.rom_run_inl]
    simp only [map_bind, map_pure]
    change RelTriple _ (($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
      (pure (value, (lstate, flag)) : ProbComp _)) _
    refine relTriple_bind relTriple_uniformSample_refl fun a b hab => ?_
    cases hab
    refine relTriple_pure_pure ⟨rfl, hrel.cache, hrel.log, fun x hx => ?_⟩
    simp only [toAdd_mul, toAdd_ofAdd, Prod.snd_add, RecordedPhase.phaseCost,
      RecordedQueries.recordOf, add_zero] at hx
    exact hrel.record x hx
  · rw [SharePresent.realImpl_world_run, advImpl_world_run]
    simp only [worldQuery]
    erw [handler_hash_run]
    rw [hrel.cache, map_eq_bind_pure_comp]
    refine relTriple_bind (couple_hash setup lstate input) fun a b hab => ?_
    obtain ⟨hout, hcache, hserved, hrecord, hlog⟩ := hab
    refine relTriple_pure_pure ⟨hout, ?_, ?_, ?_⟩
    · simpa [realView_with_record] using hcache
    · simpa [hlog] using hrel.log
    · exact rel_record_hash setup real (lstate, flag) hrel input
  · rw [SharePresent.realImpl_request_run]
    cases hframe : request.frame with
    | none =>
      rw [advImpl_sign_run, real_sign_unframed _ _ request hframe]
      simp only [map_pure, handler, StateT.run, hframe, pure_bind]
      refine relTriple_pure_pure ⟨rfl, hrel.cache, by simp [hrel.log], fun x hx => ?_⟩
      simp only [toAdd_mul, toAdd_ofAdd, Prod.snd_add, RecordedPhase.phaseCost, add_zero] at hx
      exact hrel.record x hx
    | some framed =>
      rw [real_sign_framed setup hgood request framed hframe, hrel.cache]
      rw [advImpl_sign_framed_run setup hgood request framed hframe lstate flag]
      simp only [map_bind, map_pure]
      refine relTriple_bind (couple_hash setup lstate _) fun a b hab => ?_
      obtain ⟨hout, hcache, hserved, hrecord, hlog⟩ := hab
      rw [hcache, hout]
      refine relTriple_bind (couple_hash setup b.2 _) fun a' b' hab' => ?_
      obtain ⟨hout', hcache', hserved', hrecord', hlog'⟩ := hab'
      refine relTriple_pure_pure ⟨by rw [hout'], ?_, ?_, ?_⟩
      · exact hcache'
      · simp only [hlog', hlog, hrel.log, hout']
      · intro x hx
        simp only [toAdd_mul, toAdd_ofAdd, Prod.snd_add, RecordedPhase.phaseCost, add_zero] at hx
        obtain ⟨entry, hentry, hx⟩ := hrel.record x hx
        exact ⟨entry, List.mem_append_left _ hentry, hx⟩

/-! ## One verifier step, coupled -/

/-- The lenient verifier handler at a world query is the lenient handler at it. -/
theorem worldImpl_run (lenient : Bool) (setup : Setup) (world : OracleWorld.Domain)
    (p : St × Bool) :
    ((ShareBound.worldImpl lenient setup) world).run p =
      ((handler lenient setup) (worldQuery world)).run p := by
  change (simulateQ (handler lenient setup) (liftM (ShareSpec.query (worldQuery world)))).run p = _
  rw [simulateQ_spec_query]

/-- **The coupling's invariant at the verifier**: the cache is still the view, the lenient log
and digests are those the adversary's phase left, what that phase recorded is still filed, and
every input the verifier records is filed at those digests. -/
structure RelV (setup : Setup) (log : SigningLog) (served : List HashOutput)
    (adversaryRecord : Multiset Bytes) (real : SharePresent.VerifyState) (lenient : St × Bool) :
    Prop where
  /-- The real cache is the view of the lenient state. -/
  cache : real.2 = realView setup lenient.1
  /-- The lenient log is the one the adversary's phase left. -/
  logEq : lenient.1.log = log
  /-- The lenient served digests are those the adversary's phase left. -/
  servedEq : lenient.1.served = served
  /-- What the adversary's phase recorded is still filed in the lenient record. -/
  adversary : ∀ input ∈ adversaryRecord, ∃ entry ∈ lenient.1.record, entry.1 = input
  /-- Every input the verifier records is filed at the adversary phase's served digests. -/
  verifier : ∀ input ∈ (Multiplicative.toAdd real.1).2,
    ∃ entry ∈ lenient.1.record, entry.1 = input ∧ entry.2 = served

/-- **One verifier step, coupled.** -/
theorem couple_verify (setup : Setup) (log : SigningLog) (served : List HashOutput)
    (adversaryRecord : Multiset Bytes) (queried : OracleWorld.Domain)
    (real : SharePresent.VerifyState) (lenient : St × Bool)
    (hrel : RelV setup log served adversaryRecord real lenient) :
    RelTriple ((SharePresent.realWorldImpl queried).run real)
      ((ShareBound.worldImpl true setup queried).run lenient)
      (fun p q => p.1 = q.1 ∧ RelV setup log served adversaryRecord p.2 q.2) := by
  classical
  obtain ⟨lstate, flag⟩ := lenient
  rcases queried with coin | input
  · rw [SharePresent.realWorldImpl_run, worldImpl_run, DigestTape.rom_run_inl]
    simp only [map_bind, map_pure]
    change RelTriple _ (($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
      (pure (value, (lstate, flag)) : ProbComp _)) _
    refine relTriple_bind relTriple_uniformSample_refl fun a b hab => ?_
    cases hab
    refine relTriple_pure_pure ⟨rfl, hrel.cache, hrel.logEq, hrel.servedEq, hrel.adversary,
      fun x hx => ?_⟩
    simp only [toAdd_mul, toAdd_ofAdd, Prod.snd_add, RecordedQueries.verifierCost,
      RecordedQueries.recordOf, add_zero] at hx
    exact hrel.verifier x hx
  · rw [SharePresent.realWorldImpl_run, worldImpl_run]
    simp only [worldQuery]
    erw [handler_hash_run]
    rw [hrel.cache, map_eq_bind_pure_comp]
    refine relTriple_bind (couple_hash setup lstate input) fun a b hab => ?_
    obtain ⟨hout, hcache, hserved, hrecord, hlog⟩ := hab
    refine relTriple_pure_pure ⟨hout, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [realView_with_record] using hcache
    · simpa [hlog] using hrel.logEq
    · simpa [hserved] using hrel.servedEq
    · intro x hx
      obtain ⟨entry, hentry, hx⟩ := hrel.adversary x hx
      exact ⟨entry, List.mem_append_left _ hentry, hx⟩
    · intro x hx
      simp only [toAdd_mul, toAdd_ofAdd, Prod.snd_add, RecordedQueries.verifierCost,
        RecordedQueries.recordOf, Multiset.mem_add, Multiset.mem_singleton] at hx
      rcases hx with hold | rfl
      · obtain ⟨entry, hentry, hx, hsnap⟩ := hrel.verifier x hold
        exact ⟨entry, List.mem_append_left _ hentry, hx, hsnap⟩
      · exact ⟨(x, lstate.served), List.mem_append_right _ (List.mem_singleton_self _), rfl,
          hrel.servedEq⟩

end SLHDSA.SHAKE128s.ShareCouple
