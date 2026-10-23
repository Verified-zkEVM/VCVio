/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ReplayGate
public import HashSig.SLHDSA.SHAKE128s.Proof.AdversaryQueries
public import HashSig.SLHDSA.SHAKE128s.Proof.CacheProvenance

/-!
# What the signing log holds, and how long it is

`ReplayGate.LogFaithful` is the one thing the replay case still asks of the game: every entry
of the signing log carries the bytes `Scheme.signInternal` produces for its request, read at
the run's *final* cache. This file proves it, and proves alongside it the other property of the
same log the accounting needs — that it is no longer than the signing counter says.

Faithfulness has two steps, and they are different in kind.

* **The log holds what the signer returned.** `Security.signingOracle` is
  `StrippedGame.signingOracleWith (Scheme.sign sk)`: it calls the signer once and appends the
  pair it got. So the entry's answer is what `Scheme.sign sk request` evaluated to against the
  cache in force *at the moment of the request*, and nothing else is recorded.

* **That value is the replay at the final cache.** A cache only ever grows, and a replayed
  query reads whatever entry it finds, so a value a sub-run computed is reproduced by any later
  cache — that is `WarmedSplit.run_eq_replay_of_subset`, already used to recover the generated
  key from the final cache, and used here for the same reason.

The second step is what shapes the induction. Faithfulness *at the current cache* is not
preserved as the cache grows — `Scheme.signInternal` under `replayQuery` of a cache missing its
entries computes something else entirely — so the invariant carried through the adversary's
phase is `FaithfulFrom`, which quantifies over every *later* cache up front. Stated that way it
is monotone by transitivity of `CacheAvailability.Persists` and nothing else, and the signing
step establishes it directly from `run_eq_replay_of_subset`, whose conclusion already has that
universally quantified form.

The length bound is the same induction with a numeric invariant: the signing half appends one
entry and tells one unit of `.signing`, the hash half appends nothing and tells none.

**Which presentation the induction runs over.** The nested one: `WarmedGame.afterSeeds` as the
game writes it, factored by `WarmedSplit.mem_support_counted_bind`, with
`StrippedGame.countedRun` and `countedRun_bind` as the vehicle, and the two handler cases
proved as separate lemmas stated at the *summand's* index and applied at the sum's — the only
shape that survives the semireducible gap between `(OracleWorld + SigningSpec).Range (Sum.inl t)` and
`OracleWorld.Range t`. `LinkedGame`'s `recordedAfterSeedsAt_eq` is the tidier presentation, but
it is about the *stripped* signer `StrippedGame.strippedSign` and reaches the game only through
an equality of laws; a support membership in `WarmedGame.tail` would have to be transported
across that, and transported back to read the log out. The nested route needs none of it.

**The walk is not used.** `logFaithful_tail` takes no hypothesis on the walk: the secret key
the game signed with is recovered from the run's own final cache, exactly as
`WarmedSplit.cases_of_win` recovers the public one, and the walk never enters.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.SigningFaithful

open Security CacheReplay StrippedGame AdversaryQueries

/-- The pair of handlers the adversary's phase runs against. -/
noncomputable def phaseImpl (sk : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) CountedRun :=
  adversaryImpl + Security.signingOracle sk

/-! ## The invariant

`FaithfulFrom sk cache log` says the log is faithful read at *every* cache extending `cache`.
Quantifying the later cache up front is what makes the predicate monotone, and monotone is what
an induction through a growing cache needs. -/

/-- Every entry of the log carries the signer's answer, read at any cache extending this one. -/
def FaithfulFrom (sk : SecretKey) (cache : QueryCache HashSpec) (log : SigningLog) : Prop :=
  ∀ later : QueryCache HashSpec, CacheAvailability.Persists cache later →
    ∀ entry ∈ log, ∀ framed : Bytes, entry.1.frame = some framed →
      entry.2 = some
        (@Scheme.signInternal Id Id.instMonad (replayQuery later) sk framed).toBytes

/-- **The invariant travels along the cache's growth**, by transitivity and nothing else. -/
theorem FaithfulFrom.mono {sk : SecretKey} {cache cache' : QueryCache HashSpec}
    {log : SigningLog} (hfaithful : FaithfulFrom sk cache log)
    (hgrow : CacheAvailability.Persists cache cache') : FaithfulFrom sk cache' log :=
  fun later hlater => hfaithful later (hgrow.trans hlater)

theorem faithfulFrom_nil (sk : SecretKey) (cache : QueryCache HashSpec) :
    FaithfulFrom sk cache ([] : SigningLog) :=
  fun _ _ entry hentry => absurd hentry (List.not_mem_nil (a := entry))

theorem FaithfulFrom.append {sk : SecretKey} {cache : QueryCache HashSpec}
    {log log' : SigningLog} (hleft : FaithfulFrom sk cache log)
    (hright : FaithfulFrom sk cache log') : FaithfulFrom sk cache (log ++ log') := by
  intro later hlater entry hentry
  rcases List.mem_append.mp hentry with hmem | hmem
  · exact hleft later hlater entry hmem
  · exact hright later hlater entry hmem

/-! ## One signing request

The signer is `Scheme.sign`, which is the hash-only signer lifted, so its run is a hash-only
run and `WarmedSplit.run_eq_replay_of_subset` applies to it directly. What comes out is an
equation at every later cache, which is `FaithfulFrom` for the single entry just appended. -/

/-- A signer that accepts its framing returns that framing's signature. -/
theorem sign_eq_map {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]
    (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed) :
    (Scheme.sign sk request : m (Option Bytes)) =
      (fun signature : Signature => some signature.toBytes) <$>
        (Scheme.signInternal sk framed : m Signature) := by
  unfold Scheme.sign
  rw [hframe]
  simp [map_eq_bind_pure_comp]

/-- The replayed signer, at a framing it accepts, returns the replayed signature's bytes. -/
theorem sign_replay_eq (cache : QueryCache HashSpec) (sk : SecretKey) (request : Message)
    (framed : Bytes) (hframe : request.frame = some framed) :
    @Scheme.sign Id Id.instMonad (replayQuery cache) sk request =
      some (@Scheme.signInternal Id Id.instMonad (replayQuery cache) sk framed).toBytes := by
  rw [@sign_eq_map Id Id.instMonad _ (replayQuery cache) sk request framed hframe]
  rfl

/-- **A signing step's answer is the signature every later cache replays.** -/
theorem faithfulFrom_sign (sk : SecretKey) (request : Message) (answer : Option Bytes)
    (cache mid : QueryCache HashSpec)
    (hmem : (answer, mid) ∈ support ((simulateQ KeygenUniform.rom
      (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes))).run cache)) :
    FaithfulFrom sk mid [⟨request, answer⟩] := by
  rw [StrippedGame.sign_lift, StrippedGame.run_liftComp] at hmem
  intro later hlater entry hentry framed hframe
  rw [List.mem_singleton] at hentry
  subst hentry
  rw [show (⟨request, answer⟩ : (t : Message) × Option Bytes).2 = answer from rfl,
    WarmedSplit.run_eq_replay_of_subset _ cache mid later answer hmem hlater,
    @Correctness.Naturality.sign_simulate Id Id.instMonad _ (replay later) (replayQuery later)
      (GameBridge.replay_agrees later) sk request,
    sign_replay_eq later sk request framed hframe]

/-! ## One step of the adversary's phase

Each handler gets its own lemma, stated at the *summand's* index and applied at the sum's. That
is not a stylistic choice: `(OracleWorld + SigningSpec).Range (Sum.inl t)` and
`OracleWorld.Range t` agree only semireducibly, so a rewrite that puts one where the other
stands leaves a term that is not type-correct at `instances` transparency and every later
rewrite silently misses. Applying a summand-indexed lemma at the sum, by contrast, is a single
defeq check at default transparency, which succeeds. -/

/-- A query of the adversary's own leaves the log where it was, so the invariant travels along
the cache's growth alone. -/
theorem faithfulFrom_adversaryImpl (sk : SecretKey) (queried : OracleWorld.Domain)
    (log : SigningLog) (cache : QueryCache HashSpec)
    (step : ((OracleWorld.Range queried × Multiplicative Counts) × SigningLog) ×
      QueryCache HashSpec)
    (hstep : step ∈ support (countedRun (adversaryImpl queried) log cache))
    (hfaithful : FaithfulFrom sk cache log) : FaithfulFrom sk step.2 step.1.2 := by
  have hgrow : CacheAvailability.Persists cache step.2 :=
    fun probe value hvalue => extends_of_mem_support
      ((WriterT.run (adversaryImpl queried)).run log) cache cache (Extends.refl cache) step hstep
      probe value hvalue
  rw [countedRun, run_adversaryImpl, simulateQ_map, StateT.run_map, support_map] at hstep
  obtain ⟨value, -, hvalue⟩ := hstep
  rw [show step.1.2 = log from by rw [← hvalue]]
  exact hfaithful.mono hgrow

/-- A signing request appends the pair the signer produced, and that pair is faithful. -/
theorem faithfulFrom_signingOracle (sk : SecretKey) (request : Message) (log : SigningLog)
    (cache : QueryCache HashSpec)
    (step : ((Option Bytes × Multiplicative Counts) × SigningLog) × QueryCache HashSpec)
    (hstep : step ∈ support (countedRun (Security.signingOracle sk request) log cache))
    (hfaithful : FaithfulFrom sk cache log) : FaithfulFrom sk step.2 step.1.2 := by
  rw [countedRun, StrippedGame.signingOracle_eq, StrippedGame.run_signingOracleWith,
    simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hrest⟩ := hstep
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  rw [show step.1.2 = log ++ [⟨request, inner.1⟩] from by rw [hrest],
    show step.2 = inner.2 from by rw [hrest]]
  exact FaithfulFrom.append
    (hfaithful.mono fun probe value hvalue =>
      GrowthCharge.cache_value_persists _ cache inner.2 inner.1 hinner probe value hvalue)
    (faithfulFrom_sign sk request inner.1 cache inner.2 hinner)

/-! ## The whole phase

The induction is over the adversary's own computation, with the log and the cache generalized,
read at the support. -/

/-- **The adversary's phase leaves a faithful log.** -/
theorem faithfulFrom_countedRun (sk : SecretKey) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (cache : QueryCache HashSpec)
      (result : ((α × Multiplicative Counts) × SigningLog) × QueryCache HashSpec),
      result ∈ support (countedRun (simulateQ (phaseImpl sk) computation) log cache) →
        FaithfulFrom sk cache log → FaithfulFrom sk result.2 result.1.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro log cache result hresult hfaithful
    rw [simulateQ_pure, countedRun, WriterT.run_pure, StateT.run_pure, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    rw [show result.1.2 = log from by rw [hresult], show result.2 = cache from by rw [hresult]]
    exact hfaithful
  | query_bind t next ih =>
    intro log cache result hresult hfaithful
    rw [simulateQ_bind, simulateQ_spec_query, countedRun_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, hrest⟩ := hresult
    rw [support_map] at hrest
    obtain ⟨inner, hinner, hvalue⟩ := hrest
    have hhead : FaithfulFrom sk step.2 step.1.2 := by
      rcases t with world | request
      · exact faithfulFrom_adversaryImpl sk world log cache step hstep hfaithful
      · exact faithfulFrom_signingOracle sk request log cache step hstep hfaithful
    rw [show result.1.2 = inner.1.2 from by rw [← hvalue],
      show result.2 = inner.2 from by rw [← hvalue]]
    exact ih step.1.1.1 step.1.2 step.2 inner hinner hhead

/-! ## What the log's entries left in the cache

Faithfulness says what the log *holds*; it says nothing about what the cache holds, because both
sides of its equation are replayed and `CacheReplay.replay` answers `default` at an absent
input. The disclosure notions need the other thing: that a logged request's own `PRF_msg` entry
is in the cache, so that the randomiser read off it is a drawn value rather than a default.

It is the same induction with the same invariant shape — quantified over every later cache up
front, so that it is monotone by transitivity of `Persists` and nothing else — and the signing
step establishes it from `CacheProvenance.sign_randomizer_cached`, whose conclusion already has
that form. -/

/-- Every logged request's own `PRF_msg` entry is in the cache, and in any cache extending it. -/
def RandomiserCachedFrom (sk : SecretKey) (cache : QueryCache HashSpec) (log : SigningLog) :
    Prop :=
  ∀ later : QueryCache HashSpec, CacheAvailability.Persists cache later →
    ∀ entry ∈ log, ∀ framed : Bytes, entry.1.frame = some framed →
      later (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) ≠ none

theorem RandomiserCachedFrom.mono {sk : SecretKey} {cache cache' : QueryCache HashSpec}
    {log : SigningLog} (hcached : RandomiserCachedFrom sk cache log)
    (hgrow : CacheAvailability.Persists cache cache') : RandomiserCachedFrom sk cache' log :=
  fun later hlater => hcached later (hgrow.trans hlater)

theorem randomiserCachedFrom_nil (sk : SecretKey) (cache : QueryCache HashSpec) :
    RandomiserCachedFrom sk cache ([] : SigningLog) :=
  fun _ _ entry hentry => absurd hentry (List.not_mem_nil (a := entry))

theorem RandomiserCachedFrom.append {sk : SecretKey} {cache : QueryCache HashSpec}
    {log log' : SigningLog} (hleft : RandomiserCachedFrom sk cache log)
    (hright : RandomiserCachedFrom sk cache log') :
    RandomiserCachedFrom sk cache (log ++ log') := by
  intro later hlater entry hentry
  rcases List.mem_append.mp hentry with hmem | hmem
  · exact hleft later hlater entry hmem
  · exact hright later hlater entry hmem

/-- **A signing step leaves its own `PRF_msg` entry behind.** -/
theorem randomiserCachedFrom_sign (sk : SecretKey) (request : Message) (answer : Option Bytes)
    (cache mid : QueryCache HashSpec)
    (hmem : (answer, mid) ∈ support ((simulateQ KeygenUniform.rom
      (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes))).run cache)) :
    RandomiserCachedFrom sk mid [⟨request, answer⟩] := by
  intro later hlater entry hentry framed hframe
  rw [List.mem_singleton] at hentry
  subst hentry
  exact CacheProvenance.sign_randomizer_cached sk request framed hframe cache mid later answer
    hmem fun input output hvalue => hlater input output hvalue

/-- A query of the adversary's own leaves the log where it was. -/
theorem randomiserCachedFrom_adversaryImpl (sk : SecretKey) (queried : OracleWorld.Domain)
    (log : SigningLog) (cache : QueryCache HashSpec)
    (step : ((OracleWorld.Range queried × Multiplicative Counts) × SigningLog) ×
      QueryCache HashSpec)
    (hstep : step ∈ support (countedRun (adversaryImpl queried) log cache))
    (hcached : RandomiserCachedFrom sk cache log) :
    RandomiserCachedFrom sk step.2 step.1.2 := by
  have hgrow : CacheAvailability.Persists cache step.2 :=
    fun probe value hvalue => extends_of_mem_support
      ((WriterT.run (adversaryImpl queried)).run log) cache cache (Extends.refl cache) step hstep
      probe value hvalue
  rw [countedRun, run_adversaryImpl, simulateQ_map, StateT.run_map, support_map] at hstep
  obtain ⟨value, -, hvalue⟩ := hstep
  rw [show step.1.2 = log from by rw [← hvalue]]
  exact hcached.mono hgrow

/-- A signing request appends an entry whose `PRF_msg` answer it has just drawn. -/
theorem randomiserCachedFrom_signingOracle (sk : SecretKey) (request : Message)
    (log : SigningLog) (cache : QueryCache HashSpec)
    (step : ((Option Bytes × Multiplicative Counts) × SigningLog) × QueryCache HashSpec)
    (hstep : step ∈ support (countedRun (Security.signingOracle sk request) log cache))
    (hcached : RandomiserCachedFrom sk cache log) :
    RandomiserCachedFrom sk step.2 step.1.2 := by
  rw [countedRun, StrippedGame.signingOracle_eq, StrippedGame.run_signingOracleWith,
    simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hrest⟩ := hstep
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  rw [show step.1.2 = log ++ [⟨request, inner.1⟩] from by rw [hrest],
    show step.2 = inner.2 from by rw [hrest]]
  exact RandomiserCachedFrom.append
    (hcached.mono fun probe value hvalue =>
      GrowthCharge.cache_value_persists _ cache inner.2 inner.1 hinner probe value hvalue)
    (randomiserCachedFrom_sign sk request inner.1 cache inner.2 hinner)

/-- **The adversary's phase leaves every logged request's `PRF_msg` entry in the cache.** -/
theorem randomiserCachedFrom_countedRun (sk : SecretKey) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (cache : QueryCache HashSpec)
      (result : ((α × Multiplicative Counts) × SigningLog) × QueryCache HashSpec),
      result ∈ support (countedRun (simulateQ (phaseImpl sk) computation) log cache) →
        RandomiserCachedFrom sk cache log → RandomiserCachedFrom sk result.2 result.1.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro log cache result hresult hcached
    rw [simulateQ_pure, countedRun, WriterT.run_pure, StateT.run_pure, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    rw [show result.1.2 = log from by rw [hresult], show result.2 = cache from by rw [hresult]]
    exact hcached
  | query_bind t next ih =>
    intro log cache result hresult hcached
    rw [simulateQ_bind, simulateQ_spec_query, countedRun_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, hrest⟩ := hresult
    rw [support_map] at hrest
    obtain ⟨inner, hinner, hvalue⟩ := hrest
    have hhead : RandomiserCachedFrom sk step.2 step.1.2 := by
      rcases t with world | request
      · exact randomiserCachedFrom_adversaryImpl sk world log cache step hstep hcached
      · exact randomiserCachedFrom_signingOracle sk request log cache step hstep hcached
    rw [show result.1.2 = inner.1.2 from by rw [← hvalue],
      show result.2 = inner.2 from by rw [← hvalue]]
    exact ih step.1.1.1 step.1.2 step.2 inner hinner hhead

/-! ## How long the log is

The answer side needs the number of *signed messages* capped by the `.signing` counter. The two
are the same number up to an inequality, by the same induction: the signing half appends one
entry and tells one unit of `.signing`, the hash half
appends nothing and tells none. -/

/-- A query of the adversary's own appends nothing to the log. -/
theorem length_le_signing_adversaryImpl (queried : OracleWorld.Domain) (log : SigningLog)
    (cache : QueryCache HashSpec)
    (step : ((OracleWorld.Range queried × Multiplicative Counts) × SigningLog) ×
      QueryCache HashSpec)
    (hstep : step ∈ support (countedRun (adversaryImpl queried) log cache)) :
    step.1.2.length ≤ (Multiplicative.toAdd step.1.1.2) .signing + log.length := by
  rw [countedRun, run_adversaryImpl, simulateQ_map, StateT.run_map, support_map] at hstep
  obtain ⟨value, -, hvalue⟩ := hstep
  rw [show step.1.2 = log from by rw [← hvalue]]
  exact Nat.le_add_left _ _

/-- A signing request appends one entry and charges one. -/
theorem length_le_signing_signingOracle (sk : SecretKey) (request : Message) (log : SigningLog)
    (cache : QueryCache HashSpec)
    (step : ((Option Bytes × Multiplicative Counts) × SigningLog) × QueryCache HashSpec)
    (hstep : step ∈ support (countedRun (Security.signingOracle sk request) log cache)) :
    step.1.2.length ≤ (Multiplicative.toAdd step.1.1.2) .signing + log.length := by
  rw [countedRun, StrippedGame.signingOracle_eq, StrippedGame.run_signingOracleWith,
    simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hrest⟩ := hstep
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  rw [show step.1.2 = log ++ [⟨request, inner.1⟩] from by rw [hrest],
    show step.1.1.2 = Multiplicative.ofAdd (Counts.single .signing 1) from by rw [hrest],
    toAdd_ofAdd, Counts.single, List.length_append]
  simp

/-- **The log the adversary's phase leaves is no longer than the requests it was charged.** -/
theorem length_le_signing_countedRun (sk : SecretKey) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (cache : QueryCache HashSpec)
      (result : ((α × Multiplicative Counts) × SigningLog) × QueryCache HashSpec),
      result ∈ support (countedRun (simulateQ (phaseImpl sk) computation) log cache) →
        result.1.2.length ≤ (Multiplicative.toAdd result.1.1.2) .signing + log.length := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro log cache result hresult
    rw [simulateQ_pure, countedRun, WriterT.run_pure, StateT.run_pure, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    rw [show result.1.2 = log from by rw [hresult]]
    exact Nat.le_add_left _ _
  | query_bind t next ih =>
    intro log cache result hresult
    rw [simulateQ_bind, simulateQ_spec_query, countedRun_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, hrest⟩ := hresult
    rw [support_map] at hrest
    obtain ⟨inner, hinner, hvalue⟩ := hrest
    have hhead : step.1.2.length ≤ (Multiplicative.toAdd step.1.1.2) .signing + log.length := by
      rcases t with world | request
      · exact length_le_signing_adversaryImpl world log cache step hstep
      · exact length_le_signing_signingOracle sk request log cache step hstep
    have htail := ih step.1.1.1 step.1.2 step.2 inner hinner
    rw [show result.1.2 = inner.1.2 from by rw [← hvalue],
      show result.1.1.2 = step.1.1.2 * inner.1.1.2 from by rw [← hvalue], toAdd_mul]
    show inner.1.2.length ≤ (Multiplicative.toAdd step.1.1.2) .signing +
      (Multiplicative.toAdd inner.1.1.2) .signing + log.length
    omega

/-! ## The verifier tells no signing requests

The outcome's `counts` is the adversary phase's writer plus the verifier's own `Counts`, and
the verifier's cost function names only `.verification`, so the `.signing` component of the
outcome is the phase's alone. -/

/-- **A `Counts` instrumentation that never charges `.signing` leaves that counter at zero.** -/
theorem signing_countQueries_eq_zero (cost : OracleWorld.Domain → Counts)
    (hcost : ∀ input, cost input .signing = 0) {α : Type}
    (computation : OracleComp OracleWorld α) :
    ∀ (cache : QueryCache HashSpec) (result : (α × Counts) × QueryCache HashSpec),
      result ∈ support ((simulateQ KeygenUniform.rom
        (countQueries cost computation)).run cache) → result.1.2 .signing = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache result hmem
    rw [VerificationBudget.countQueries_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    rw [show result.1.2 = 0 from by rw [hmem]]
    rfl
  | query_bind queried next ih =>
    intro cache result hmem
    rw [WarmedSplit.countQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, -, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have htail := ih step.1 step.2 inner hinner
    rw [show result.1.2 = cost queried + inner.1.2 from by rw [← heq]]
    show cost queried .signing + inner.1.2 .signing = 0
    rw [hcost, htail]

theorem verifierCost_signing (input : OracleWorld.Domain) :
    (Counts.single .verification (hashCost input)) .signing = 0 := by
  simp [Counts.single, Pi.single_eq_of_ne]

/-! ## The game

`WarmedSplit.split_afterSeeds` factors the counted game at key generation and at verification;
the same three applications of `WarmedSplit.mem_support_counted_bind` expose the adversary's
phase in between, which is the piece both inductions speak about. What is read off it is the
log the outcome carries, the growth from the phase's cache to the run's, and the fact that the
outcome's `.signing` count is the phase's own. -/

/-- The replayed secret key is the one `ReplayGate.secretKeyOf` names. -/
theorem keygen_secretKey (secretSeed prfSeed publicSeed : Digest)
    (cache : QueryCache HashSpec) :
    (@Scheme.keygenInternal Id Id.instMonad (replayQuery cache)
        secretSeed prfSeed publicSeed).1 =
      ⟨secretSeed, prfSeed, SplitCharged.generatedKey secretSeed prfSeed publicSeed cache⟩ := by
  rw [SplitCharged.generatedKey]
  rfl

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

/-- **The counted game factors at its adversary phase.** The key is a genuine key-generation
sub-run's value, the log the outcome carries is the phase's final log, the outcome's signing
count is the phase's own, and everything the phase cached is still cached at the end. -/
theorem split_phase (adversary : Adversary) (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec) (result : (Outcome × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (WarmedGame.afterSeeds adversary sds))).run cache)) :
    ∃ (keys : SecretKey × PublicKey) (keyCache advCache : QueryCache HashSpec)
      (value : (Forgery × Multiplicative Counts) × SigningLog),
      (keys, keyCache) ∈ support ((simulateQ KeygenUniform.rom
        (Scheme.keygenInternal sds.1 sds.2.1 sds.2.2)).run cache) ∧
      (∀ (input : Bytes) (output : HashOutput),
        keyCache input = some output → result.2 input = some output) ∧
      (value, advCache) ∈ support (countedRun
        (simulateQ (phaseImpl keys.1) (adversary.main keys.2)) [] keyCache) ∧
      value.2 = result.1.1.signed ∧
      CacheAvailability.Persists advCache result.2 ∧
      result.1.1.counts .signing = (Multiplicative.toAdd value.1.2) .signing := by
  unfold WarmedGame.afterSeeds at hresult
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
  obtain ⟨⟨hvalue, -⟩, hcache⟩ := hrest3
  have hverifyGrow : CacheAvailability.Persists verifyFinal result.2 := by
    rw [hcache]; exact CacheAvailability.Persists.refl _
  have hadvGrow : CacheAvailability.Persists advCache result.2 :=
    fun probe output hentry => hverifyGrow probe output
      (GrowthCharge.cache_value_persists _ advCache verifyFinal _ hverify probe output hentry)
  have hverifierSigning : verified.2 .signing = 0 :=
    signing_countQueries_eq_zero _ verifierCost_signing _ advCache (verified, verifyFinal) hverify
  refine ⟨(sk, pk), keyCache, advCache, value, hkeys, ?_, hadv, ?_, hadvGrow, ?_⟩
  · intro input output hentry
    exact hadvGrow input output
      (GrowthCharge.cache_value_persists _ keyCache advCache _ hadv input output hentry)
  · rw [hvalue]
  · rw [hvalue]
    show (Multiplicative.toAdd value.1.2) .signing + verified.2 .signing =
      (Multiplicative.toAdd value.1.2) .signing
    rw [hverifierSigning, Nat.add_zero]

attribute [local irreducible] WarmedGame.afterSeeds

/-- **Every logged request carries the signer's own answer.** -/
theorem logFaithful_tail (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk)) :
    ReplayGate.LogFaithful ((walk.1, result.1), result.2) := by
  unfold WarmedGame.tail at hresult
  obtain ⟨keys, keyCache, advCache, value, hkeys, hpersist, hadv, hlog, hgrow, -⟩ :=
    split_phase adversary walk.1.1 walk.2 result hresult
  rw [WarmedSplit.keygenInternal_liftM, WarmedSplit.run_rom_liftM] at hkeys
  have hkeyreplay : keys = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
      walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 :=
    WarmedSplit.keygenInternal_eq_replay_of_subset _ _ _ walk.2 keyCache result.2 keys hkeys
      hpersist
  have hsk : keys.1 = ReplayGate.secretKeyOf ((walk.1, result.1), result.2) := by
    rw [hkeyreplay, keygen_secretKey]
    rfl
  have hfaithful : FaithfulFrom keys.1 advCache result.1.1.signed :=
    hlog ▸ faithfulFrom_countedRun keys.1 (adversary.main keys.2) [] keyCache (value, advCache)
      hadv (faithfulFrom_nil keys.1 keyCache)
  intro entry hentry framed hframe
  exact hsk ▸ hfaithful result.2 hgrow entry hentry framed hframe

/-- **Every logged request's own `PRF_msg` entry is in the run's cache.** The companion to
`logFaithful_tail`: that one says what the log holds, this says what the signer left behind, and
the disclosure notions need both. -/
theorem randomiserCached_tail (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (entry : (_ : Message) × Option Bytes) (hentry : entry ∈ result.1.1.signed)
    (framed : Bytes) (hframe : entry.1.frame = some framed) :
    result.2 (Hashing.randomizerInput
      (ReplayGate.secretKeyOf ((walk.1, result.1), result.2)).prf
      (ReplayGate.secretKeyOf ((walk.1, result.1), result.2)).publicKey.seed framed) ≠
      none := by
  unfold WarmedGame.tail at hresult
  obtain ⟨keys, keyCache, advCache, value, hkeys, hpersist, hadv, hlog, hgrow, -⟩ :=
    split_phase adversary walk.1.1 walk.2 result hresult
  rw [WarmedSplit.keygenInternal_liftM, WarmedSplit.run_rom_liftM] at hkeys
  have hkeyreplay : keys = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
      walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 :=
    WarmedSplit.keygenInternal_eq_replay_of_subset _ _ _ walk.2 keyCache result.2 keys hkeys
      hpersist
  have hsk : keys.1 = ReplayGate.secretKeyOf ((walk.1, result.1), result.2) := by
    rw [hkeyreplay, keygen_secretKey]
    rfl
  have hcached : RandomiserCachedFrom keys.1 advCache result.1.1.signed :=
    hlog ▸ randomiserCachedFrom_countedRun keys.1 (adversary.main keys.2) [] keyCache
      (value, advCache) hadv (randomiserCachedFrom_nil keys.1 keyCache)
  exact hsk ▸ hcached result.2 hgrow entry hentry framed hframe

/-- **The outcome's log is no longer than its signing count.** -/
theorem signed_length_le_signing (adversary : Adversary) (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec) (result : (Outcome × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (WarmedGame.afterSeeds adversary sds))).run cache)) :
    result.1.1.signed.length ≤ result.1.1.counts .signing := by
  obtain ⟨keys, keyCache, advCache, value, -, -, hadv, hlog, -, hcounts⟩ :=
    split_phase adversary sds cache result hresult
  rw [← hlog, hcounts]
  have hphase := length_le_signing_countedRun keys.1 (adversary.main keys.2) [] keyCache
    (value, advCache) hadv
  simpa using hphase

/-- **The outcome's log is no longer than its signing count**, read on a warmed tail. -/
theorem signed_length_le_signing_tail (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk)) :
    result.1.1.signed.length ≤ result.1.1.counts .signing := by
  unfold WarmedGame.tail at hresult
  exact signed_length_le_signing adversary walk.1.1 walk.2 result hresult

/-! ## The split, with nothing left to assume

`ReplayGate.cases_of_win_charged` composes the whole split and takes the log's faithfulness as
its only remaining hypothesis about the game. Discharging it here leaves a statement about a
supported tail alone, which is the shape the target's `hsplit` reads. -/

/-- **A win on a good walk is the answer side or the input side**, with nothing assumed about
the log. -/
theorem cases_of_win_charged (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (hwin : Wins result.1.1) :
    RoutedSplit.AnswerBad ((walk.1, result.1), result.2) ∨
      RoutedSplit.InputBad ((walk.1, result.1), result.2) :=
  ReplayGate.cases_of_win_charged adversary hwalk hresult
    (logFaithful_tail adversary hresult) hwin

end SlhDsaSecurity.SigningFaithful
