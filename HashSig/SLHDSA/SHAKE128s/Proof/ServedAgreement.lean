/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ServingCarrier
public import HashSig.SLHDSA.SHAKE128s.Proof.PhaseFusion
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedQueries
public import HashSig.SLHDSA.SHAKE128s.Proof.ServedBridge
public import HashSig.SLHDSA.SHAKE128s.Proof.SignerRandomiser
public import HashSig.SLHDSA.SHAKE128s.Proof.StrippedGame
public import HashSig.SLHDSA.SHAKE128s.Proof.RedrawCell
public import HashSig.SLHDSA.SHAKE128s.Proof.SharedJoin
public import HashSig.SLHDSA.SHAKE128s.Proof.KeygenValue
public import HashSig.SLHDSA.SHAKE128s.Proof.ChargedProbe

/-!
# The carrier's served set and the log's, at a run of the serving phase

`ServingCarrier.AgreesWithLog` says that the carrier serves exactly the digest inputs the log
names. `servingPhaseWith` is the serving phase over any signer: the framing is set across a
signing step and clear everywhere else. This file is the run-level proof of the agreement, and
`record_length_le_cap` feeds the cap on the disclosing recording.

**The two directions are proved apart, because they rest on different things.** That the log is
below the carrier rests on what the signer *asks*: its second query is its own digest input, made
while its framing is set, so the handler files it and filing persists. That the carrier is below
the log rests on what the handler *files*: nothing is filed at a clear framing, so every served
input has the shape of some logged request's digest input.

**The signer's two queries are the whole of it.** `sign_shape` cuts `Scheme.sign` at them: the
randomiser's input, then the digest's, whose input carries the randomiser the first answer
truncates to. Everything after is the tail, which this file never looks at.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.ServedAgreement

variable {α β : Type}

open Security OpenCache CanonicalGraph RecordedQueries

variable (publicSeed : Digest)

/-! ## What the agreement asks of a handler

The chain below reads its handler through six named facts, so it is parameterised over any
handler satisfying them. The state is `HandlerCarrier.State × τ` for an arbitrary `τ`: the
serving program carries a probe list and a counter beside its carrier, the recorder carries two
recordings, and neither the chain nor these laws look at either. -/

/-- **A handler that files**: the six facts the agreement reads it through. Both directions of
"served implies queried" and "queried implies cached" are available from `hashCached` and
`runPersists`. -/
structure Files (pk : PublicKey) {τ : Type}
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp)) : Prop where
  /-- A hash query leaves its own input cached, the framing where it was, the carrier grown, and
  the input served if the framing admitted it — stated with the continuation, so a chain of
  queries is a chain of applications. -/
  queryStep : ∀ {α : Type} (input : Bytes)
    (next : OracleWorld.Range (Sum.inr input) → OracleComp OracleWorld α)
    (state : HandlerCarrier.State × τ) (result : α × (HandlerCarrier.State × τ)),
    result ∈ support ((simulateQ impl
      ((query (spec := OracleWorld) (Sum.inr input) :
        OracleComp OracleWorld (OracleWorld.Range (Sum.inr input))) >>= next)).run state) →
    ∃ (answer : HashOutput) (mid : HandlerCarrier.State × τ),
      mid.1.cache input = some answer ∧ mid.1.framing = state.1.framing ∧
        HandlerCarrier.Grows state.1 mid.1 ∧
        (HandlerCarrier.FilesLeft pk state.1 input → HandlerCarrier.Served mid.1 input) ∧
        result ∈ support ((simulateQ impl (next answer)).run mid)
  /-- A run keeps every cache entry and everything served. -/
  runPersists : ∀ {α : Type} (computation : OracleComp OracleWorld α)
    (state : HandlerCarrier.State × τ) (z : α × (HandlerCarrier.State × τ)),
    z ∈ support ((simulateQ impl computation).run state) → HandlerCarrier.Grows state.1 z.2.1
  /-- A property closed under caching and under filing-where-admitted survives a run. -/
  invariant : ∀ (Inv : HandlerCarrier.State → Prop),
    (∀ (carrier : HandlerCarrier.State) (input : Bytes) (answer : HashOutput),
      Inv carrier → Inv (HandlerCarrier.cacheAnswer carrier input answer)) →
    (∀ (carrier : HandlerCarrier.State) (input : Bytes),
      Inv carrier → HandlerCarrier.FilesLeft pk carrier input →
        Inv (HandlerCarrier.file carrier input)) →
    ∀ {α : Type} (computation : OracleComp OracleWorld α),
      ∀ (state : HandlerCarrier.State × τ) (result : α × (HandlerCarrier.State × τ)),
        result ∈ support ((simulateQ impl computation).run state) → Inv state.1 → Inv result.2.1
  /-- A run leaves the framing alone: only the signing side writes it. -/
  runFraming : ∀ {α : Type} (computation : OracleComp OracleWorld α)
    (state : HandlerCarrier.State × τ) (z : α × (HandlerCarrier.State × τ)),
    z ∈ support ((simulateQ impl computation).run state) → z.2.1.framing = state.1.framing
  /-- A hash step leaves its own input cached, holding what it answered. -/
  hashCached : ∀ (input : Bytes) (state : HandlerCarrier.State × τ)
    (step : OracleWorld.Range (Sum.inr input) × (HandlerCarrier.State × τ)),
    step ∈ support ((impl (Sum.inr input)).run state) → step.2.1.cache input = some step.1
  /-- A step grows the carrier. Stated at the step and not only at the run, because an
  interface that only speaks of runs cannot be transported through a wrapper: `queryStep` for a
  wrapped handler is rebuilt from the step facts, and a run fact will not rebuild it. -/
  stepGrows : ∀ (queried : OracleWorld.Domain) (state : HandlerCarrier.State × τ)
    (step : OracleWorld.Range queried × (HandlerCarrier.State × τ)),
    step ∈ support ((impl queried).run state) → HandlerCarrier.Grows state.1 step.2.1
  /-- And leaves the framing alone. -/
  stepFraming : ∀ (queried : OracleWorld.Domain) (state : HandlerCarrier.State × τ)
    (step : OracleWorld.Range queried × (HandlerCarrier.State × τ)),
    step ∈ support ((impl queried).run state) → step.2.1.framing = state.1.framing
  /-- A hash step serves nothing but its own input. -/
  hashServed : ∀ (input : Bytes) (state : HandlerCarrier.State × τ)
    (step : OracleWorld.Range (Sum.inr input) × (HandlerCarrier.State × τ)),
    step ∈ support ((impl (Sum.inr input)).run state) → ∀ probe : Bytes,
      HandlerCarrier.Served step.2.1 probe →
        HandlerCarrier.Served state.1 probe ∨ probe = input

/-- Raising the framing, at any state that carries a carrier. -/
@[expose] def startServingOn {τ : Type} (request : Message) (state : HandlerCarrier.State × τ) :
    HandlerCarrier.State × τ :=
  match request.frame with
  | none => state
  | some framed => (HandlerCarrier.setFraming state.1 framed, state.2)

/-- And lowering it. -/
@[expose]
def stopServingOn {τ : Type} (state : HandlerCarrier.State × τ) : HandlerCarrier.State × τ :=
  (HandlerCarrier.clearFraming state.1, state.2)

/-- Stopping serving clears the framing. -/
@[simp] theorem framing_stopServingOn {τ : Type} (state : HandlerCarrier.State × τ) :
    (stopServingOn state).1.framing = none := rfl

/-! ## The phase, over any signer

Everything the agreement proves about the serving phase uses the signer in exactly two places,
the two queries it makes first and which randomiser a query of digest shape can carry, so the
phase is taken over an arbitrary signer and those two places become hypotheses:

* `SignerShape` — it asks its randomiser and then its digest. This is what the filing argument
  chains along.
* `SignerPins` — it is the lift of a hash-only computation in which the only query of a
  framing's digest shape carries the randomiser the cache replays. This is the half that needs
  the walk to be good, and it is where `ServedBridge.sign_messageShape_randomizer` enters.

Both hold of `Scheme.sign sk`: `signerShape_sign`, `signerPins_sign`. -/

/-- The serving phase at an arbitrary signer. -/
@[expose] noncomputable def servingPhaseWith {τ : Type}
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (signer : Message → OracleComp OracleWorld (Option Bytes)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ)) ProbComp) :=
  PhaseFusion.fuseServing impl
    (recordedAdversaryImpl + recordedSigningOracle signer) startServingOn stopServingOn

/-- **What the filing argument asks of a signer**: it asks its randomiser and then its digest. -/
@[expose] def SignerShape (sk : SecretKey)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) : Prop :=
  ∀ (request : Message) (framed : Bytes), request.frame = some framed →
    ∃ rest : HashOutput → HashOutput → OracleComp OracleWorld (Option Bytes),
      signer request =
        (query (spec := OracleWorld)
            (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed framed)) :
          OracleComp OracleWorld HashOutput) >>= fun seed =>
            (query (spec := OracleWorld)
                (Sum.inr (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)) :
              OracleComp OracleWorld HashOutput) >>= rest seed

/-- **What the containment asks of a signer**: it is the lift of a hash-only computation whose
only query of a framing's digest shape carries the randomiser the cache replays. -/
@[expose] def SignerPins (sk : SecretKey) (warm : QueryCache HashSpec)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) : Prop :=
  ∃ hashSigner : Message → OracleComp HashSpec (Option Bytes),
    (∀ request : Message, signer request =
      OracleComp.liftComp (hashSigner request) OracleWorld) ∧
      ∀ (request : Message) (framed : Bytes), request.frame = some framed →
        ∀ later : QueryCache HashSpec,
          (∀ (input : Bytes) (value : HashOutput), warm input = some value →
            later input = some value) →
          ∀ randomizer : Digest,
            CacheReplay.QueriesUnder later (hashSigner request)
                (Hashing.messageInput randomizer sk.publicKey framed) →
              randomizer = HonestProbes.replayRandomizer later sk framed

/-! ## The signer's first two queries -/

/-- **The rest of the signer begins with its digest query.** The tail is whatever follows, and
nothing here looks at it. -/
theorem signInternalAt_shape (randomizer : Digest) (sk : SecretKey) (message : Bytes) :
    ∃ rest : HashOutput → OracleComp OracleWorld Signature,
      SignerRandomiser.signInternalAt (m := OracleComp OracleWorld) randomizer sk message =
        (query (spec := OracleWorld)
            (Sum.inr (Hashing.messageInput randomizer sk.publicKey message)) :
          OracleComp OracleWorld HashOutput) >>= rest :=
  ⟨_, rfl⟩

open scoped Classical in
/-- **The signer asks its randomiser and then its digest.** The tail is left existential: no
statement here looks past the second query, and naming the tail would mean transcribing
`SignerRandomiser.signInternalAt`'s body. -/
theorem sign_shape (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed) :
    ∃ rest : HashOutput → HashOutput → OracleComp OracleWorld (Option Bytes),
      Scheme.sign (m := OracleComp OracleWorld) sk request =
        (query (spec := OracleWorld)
            (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed framed)) :
          OracleComp OracleWorld HashOutput) >>= fun seed =>
            (query (spec := OracleWorld)
                (Sum.inr (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)) :
              OracleComp OracleWorld HashOutput) >>= rest seed := by
  classical
  refine ⟨fun seed digest =>
    (signInternalAt_shape (Hashing.truncate seed) sk framed).choose digest >>=
      fun signature => (pure (some signature.toBytes) : OracleComp OracleWorld (Option Bytes)),
    ?_⟩
  simp only [Scheme.sign, hframe, SignerRandomiser.signInternal_eq, Hashing.randomizer,
    Hashing.shortHash, Hashing.hash, bind_assoc, pure_bind]
  refine congrArg (Bind.bind _) (funext fun seed => ?_)
  have hchoose := (signInternalAt_shape (Hashing.truncate seed) sk framed).choose_spec
  generalize (signInternalAt_shape (Hashing.truncate seed) sk framed).choose = rest at hchoose ⊢
  rw [hchoose, bind_assoc]
  rfl

/-! ## The log is below the carrier

A request the log names was served, and the step that served it ran with its framing set. The
digest query is therefore filed in the step that answers it, and both the filing and the
randomiser's own cache entry persist to the end of the run. -/

/-- **A served request leaves its own digest input filed**, with the randomiser its first answer
truncates to, and leaves that first answer cached. Both are what the end of the run reads. -/
theorem served_of_signer (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey)
    (hpk : sk.publicKey = pk) (hshape : SignerShape sk signer)
    (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed) (state : (HandlerCarrier.State × τ))
    (hframing : state.1.framing = some framed) (result : Option Bytes × (HandlerCarrier.State × τ))
    (hresult : result ∈ support ((simulateQ impl
      (signer request)).run state)) :
    ∃ seed : HashOutput,
      result.2.1.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed ∧
        HandlerCarrier.Served result.2.1
          (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) := by
  obtain ⟨rest, hrest⟩ := hshape request framed hframe
  rw [hrest] at hresult
  obtain ⟨seed, mid, hseedCached, hmidFraming, hmidGrows, -, hrest⟩ :=
    hfiles.queryStep
      (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) _ state result hresult
  obtain ⟨digest, final, -, -, hfinalGrows, hfinalServed, htail⟩ :=
    hfiles.queryStep
      (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) _ mid result hrest
  have hlast := hfiles.runPersists _ final result htail
  refine ⟨seed, hlast.1 _ _ (hfinalGrows.1 _ _ hseedCached), hlast.2 _ (hfinalServed ?_)⟩
  exact ⟨framed, hmidFraming.trans hframing, Hashing.truncate seed, by rw [hpk]⟩

/-! ## The step, at the phase

Two facts about a step of `servingPhaseWith`: the carrier only grows, and a signing request files
its own digest input. Everything run-level below is these two under an induction. -/

/-- **Dropping a pure tail does not change the state a run leaves.** The signing oracle's own
sub-run is the signer followed by a log append, and the append is pure. -/
theorem state_of_bind_pure {α β : Type} (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (_hfiles : Files pk impl)
    (computation : OracleComp OracleWorld α) (tail : α → β) (state : (HandlerCarrier.State × τ))
    (result : β × (HandlerCarrier.State × τ))
    (hresult : result ∈ support ((simulateQ impl
      (computation >>= fun value => (pure (tail value) : OracleComp OracleWorld β))).run
      state)) :
    ∃ inner : α × (HandlerCarrier.State × τ), inner ∈ support
      ((simulateQ impl computation).run state) ∧
        result = (tail inner.1, inner.2) := by
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨inner, hinner, hrest⟩ := hresult
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  exact ⟨inner, hinner, hrest⟩

open scoped Classical in
/-- **A step of the phase grows the carrier.** -/
theorem servingPhaseWith_persists (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (signer : Message → OracleComp OracleWorld (Option Bytes))
    (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ))
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ)))
    (hstep : step ∈ support (((servingPhaseWith impl signer) queried).run
      state)) : HandlerCarrier.Grows state.2.2.1 step.2.2.2.1 := by
  classical
  rcases queried with world | request
  · have hrun : step ∈ support
        ((simulateQ impl
          (((recordedAdversaryImpl world).run).run state.2.1)).run state.2.2 >>=
          fun inner =>
            (pure (inner.1.1.1, (state.1 * inner.1.1.2, inner.1.2, inner.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ))))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.2.2 = inner.2 from by rw [hpure]]
    exact hfiles.runPersists _ state.2.2 inner hinner
  · have hrun : step ∈ support
        ((simulateQ impl
          (((recordedSigningOracle signer request).run).run state.2.1)).run
            (startServingOn request state.2.2) >>= fun inner =>
          (pure (inner.1.1.1,
            (state.1 * inner.1.1.2, inner.1.2, stopServingOn inner.2)) :
            ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
              (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ))))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.2.2 = stopServingOn inner.2 from by rw [hpure]]
    refine HandlerCarrier.Grows.trans ?_
      (hfiles.runPersists _
        (startServingOn request state.2.2) inner hinner)
    cases hframe : request.frame with
    | none =>
      rw [show startServingOn request state.2.2 = state.2.2 from by rw [startServingOn, hframe]]
      exact HandlerCarrier.Grows.refl _
    | some framed =>
      rw [show startServingOn request state.2.2 =
        (HandlerCarrier.setFraming state.2.2.1 framed, state.2.2.2) from by
          rw [startServingOn, hframe]]
      exact HandlerCarrier.grows_setFraming state.2.2.1 framed

open scoped Classical in
/-- **A step of the phase leaves the framing clear**, at any signer. The serving phase's own
invariant at any signer — neither half of it looks at what the signer
does: the bracket clears the framing whatever the sub-run did, and outside a request the handler
never writes it. -/
theorem framing_clear_step_with (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (signer : Message → OracleComp OracleWorld (Option Bytes))
    (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ))
    (hclear : state.2.2.1.framing = none)
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ)))
    (hstep : step ∈ support (((servingPhaseWith impl signer)
      queried).run state)) : step.2.2.2.1.framing = none := by
  classical
  rcases queried with world | request
  · have hrun : step ∈ support
        ((simulateQ impl
          (((recordedAdversaryImpl world).run).run state.2.1)).run state.2.2 >>=
          fun inner =>
            (pure (inner.1.1.1, (state.1 * inner.1.1.2, inner.1.2, inner.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ))))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.2.2 = inner.2 from by rw [hpure],
      hfiles.runFraming _ state.2.2 inner hinner]
    exact hclear
  · have hrun : step ∈ support
        ((simulateQ impl
          (((recordedSigningOracle signer request).run).run state.2.1)).run
            (startServingOn request state.2.2) >>= fun inner =>
          (pure (inner.1.1.1,
            (state.1 * inner.1.1.2, inner.1.2, stopServingOn inner.2)) :
            ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
              (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ))))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, -, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.2.2 = stopServingOn inner.2 from by rw [hpure]]
    exact framing_stopServingOn inner.2

/-! ## What the invariant says about the log's own reading

`ServingCarrier.logServed` names the digest input through `HonestProbes.replayRandomizer`, which
reads the randomiser back off the cache. The invariant's cached clause is what makes that
reading the one the signer used. -/

/-- The randomiser a cache replays is the answer it holds. -/
theorem replayRandomizer_of_cached (cache : QueryCache HashSpec) (sk : SecretKey)
    (framed : Bytes) (seed : HashOutput)
    (hcached : cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed) :
    HonestProbes.replayRandomizer cache sk framed = Hashing.truncate seed := by
  rw [HonestProbes.replayRandomizer]
  simp [CacheReplay.replay, hcached]

/-! ## The signature the signer publishes

`ServedLog.servedLog` names a served input by the randomiser in the **published signature**; the
agreement names it by the randomiser the **cache** replays. They are the same randomiser, which
is log faithfulness. The pure half is `randomizer_of_signInternalAt`: the signer's result carries
the randomiser it was given, whatever its queries answered. Everything else is the first query's
answer being cached and persisting, which the query step already gives. -/

/-- **The signer's result carries the randomiser it was handed.** A fact about the shape of
`signInternalAt`'s return, independent of what anything answered. -/
theorem randomizer_of_signInternalAt {σ : Type} (impl : QueryImpl OracleWorld (StateT σ ProbComp))
    (randomizer : Digest) (sk : SecretKey) (message : Bytes) (state : σ)
    (result : Signature × σ)
    (hresult : result ∈ support ((simulateQ impl
      (SignerRandomiser.signInternalAt (m := OracleComp OracleWorld) randomizer sk message)).run
      state)) : result.1.randomizer = randomizer := by
  rw [SignerRandomiser.signInternalAt] at hresult
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨a, -, b, -, c, -, d, -, h⟩ := hresult
  rw [h]

/-- **What the log's own reading asks of a signer**: it answers with a signature whose
randomiser the final cache replays. -/
@[expose] def SignerFaithful (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (_hfiles : Files pk impl)
    (sk : SecretKey) (signer : Message → OracleComp OracleWorld (Option Bytes)) : Prop :=
  ∀ (request : Message) (framed : Bytes), request.frame = some framed →
    ∀ (state : (HandlerCarrier.State × τ)) (result : Option Bytes × (HandlerCarrier.State × τ)),
      result ∈ support ((simulateQ impl
        (signer request)).run state) →
      ∃ signature : Signature, result.1 = some signature.toBytes ∧
        signature.randomizer = HonestProbes.replayRandomizer result.2.1.cache sk framed

open scoped Classical in
/-- **And `Scheme.sign` is faithful.** The randomiser it publishes is the one it derived, and
the derivation's answer is in the cache and stays there. -/
theorem signerFaithful_sign (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (sk : SecretKey) : SignerFaithful pk impl hfiles sk (Scheme.sign sk) := by
  classical
  intro request framed hframe state result hresult
  have hshape : Scheme.sign (m := OracleComp OracleWorld) sk request =
      (query (spec := OracleWorld)
          (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed framed)) :
        OracleComp OracleWorld HashOutput) >>= fun seed =>
          (SignerRandomiser.signInternalAt (m := OracleComp OracleWorld)
              (Hashing.truncate seed) sk framed >>= fun signature =>
            (pure (some signature.toBytes) : OracleComp OracleWorld (Option Bytes))) := by
    simp only [Scheme.sign, hframe, SignerRandomiser.signInternal_eq, Hashing.randomizer,
      Hashing.shortHash, Hashing.hash, bind_assoc, pure_bind]
    rfl
  rw [hshape] at hresult
  obtain ⟨seed, mid, hseedCached, -, -, -, htail⟩ :=
    hfiles.queryStep
      (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) _ state result hresult
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at htail
  obtain ⟨inner, hinner, hpure⟩ := htail
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  have hgrow := hfiles.runPersists _ mid inner hinner
  have hcached : result.2.1.cache
      (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed := by
    rw [show result.2 = inner.2 from by rw [hpure]]
    exact hgrow.1 _ _ hseedCached
  refine ⟨inner.1, by rw [hpure], ?_⟩
  rw [replayRandomizer_of_cached result.2.1.cache sk framed seed hcached]
  exact randomizer_of_signInternalAt impl
    (Hashing.truncate seed) sk framed mid inner hinner

/-! ## The log is below the carrier, at a run

The invariant is stated at the log and the carrier together: every logged request that has a
framing has its randomiser's answer in the cache and its digest input in the served set. Both
clauses are needed. The served one is the conclusion; the cached one is what keeps the *input*
from moving as the run goes on, since the input names the randomiser and the randomiser is read
back off the cache. -/

/-- **What a run leaves true of its log and its carrier.** -/
@[expose]
def LogFiled (sk : SecretKey) (log : SigningLog) (carrier : HandlerCarrier.State) : Prop :=
  ∀ entry ∈ log, ∀ framed : Bytes, entry.1.frame = some framed →
    ∃ (seed : HashOutput) (signature : Signature),
      carrier.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed ∧
        entry.2 = some signature.toBytes ∧
        signature.randomizer = Hashing.truncate seed ∧
        HandlerCarrier.Served carrier
          (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)

/-- **It survives growth**, both clauses for the same reason: a carrier that grows keeps its
entries and keeps what it serves. -/
theorem LogFiled.mono {sk : SecretKey} {log : SigningLog} {left right : HandlerCarrier.State}
    (hinv : LogFiled sk log left) (hgrow : HandlerCarrier.Grows left right) :
    LogFiled sk log right := by
  intro entry hentry framed hframe
  obtain ⟨seed, signature, hcached, hanswer, hrandomizer, hserved⟩ :=
    hinv entry hentry framed hframe
  exact ⟨seed, signature, hgrow.1 _ _ hcached, hanswer, hrandomizer, hgrow.2 _ hserved⟩

/-- **And it survives a log that only grows.** -/
theorem LogFiled.append {sk : SecretKey} {log : SigningLog} {carrier : HandlerCarrier.State}
    (hinv : LogFiled sk log carrier) (entry : (_ : Message) × Option Bytes)
    (hentry : ∀ framed : Bytes, entry.1.frame = some framed →
      ∃ (seed : HashOutput) (signature : Signature),
        carrier.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed ∧
          entry.2 = some signature.toBytes ∧
          signature.randomizer = Hashing.truncate seed ∧
          HandlerCarrier.Served carrier
            (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)) :
    LogFiled sk (log ++ [entry]) carrier := by
  intro probe hprobe framed hframe
  rcases List.mem_append.mp hprobe with hold | hnew
  · exact hinv probe hold framed hframe
  · obtain rfl := List.mem_singleton.mp hnew
    exact hentry framed hframe

open scoped Classical in
/-- **A step of the phase preserves it.** The adversary's step changes no log and only grows the
carrier; a signing step appends one entry and files exactly that entry's digest input. -/
theorem logFiled_step_with (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey)
    (hpk : sk.publicKey = pk)
    (hshape : SignerShape sk signer)
    (hfaithful : SignerFaithful pk impl hfiles sk signer)
    (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ))
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ)))
    (hstep : step ∈ support (((servingPhaseWith impl signer) queried).run
      state)) (hinv : LogFiled sk state.2.1 state.2.2.1) :
    LogFiled sk step.2.2.1 step.2.2.2.1 := by
  classical
  have hgrow := servingPhaseWith_persists pk impl hfiles signer queried state step hstep
  rcases queried with world | request
  · have hrun : step ∈ support
        ((simulateQ impl
          (((recordedAdversaryImpl world).run).run state.2.1)).run state.2.2 >>=
          fun inner =>
            (pure (inner.1.1.1, (state.1 * inner.1.1.2, inner.1.2, inner.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ))))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [run_recordedAdversaryImpl, simulateQ_map, StateT.run_map, support_map] at hinner
    obtain ⟨raw, -, hinnerEq⟩ := hinner
    have hlog : step.2.2.1 = state.2.1 := by rw [hpure, ← hinnerEq]
    rw [hlog]
    exact hinv.mono hgrow
  · have hrun : step ∈ support
        ((simulateQ impl
          (((recordedSigningOracle signer request).run).run state.2.1)).run
            (startServingOn request state.2.2) >>= fun inner =>
          (pure (inner.1.1.1,
            (state.1 * inner.1.1.2, inner.1.2, stopServingOn inner.2)) :
            ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
              (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ))))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [run_recordedSigningOracle] at hinner
    obtain ⟨signStep, hsign, hvalue⟩ := state_of_bind_pure pk impl hfiles
      (signer request) _ (startServingOn request state.2.2) inner hinner
    have hlog : step.2.2.1 = state.2.1 ++ [⟨request, signStep.1⟩] := by
      rw [hpure]
      exact congrArg (fun z => z.1.2) hvalue
    have hcarrier : step.2.2.2.1 = HandlerCarrier.clearFraming signStep.2.1 := by
      rw [hpure]
      exact congrArg (fun z => HandlerCarrier.clearFraming z.2.1) hvalue
    rw [hlog]
    refine LogFiled.append (hinv.mono hgrow) _ ?_
    intro framed hframe
    obtain ⟨seed, hcached, hserved⟩ := served_of_signer pk impl hfiles signer sk
      hpk hshape request framed hframe (startServingOn request state.2.2)
      (by simp only [startServingOn, hframe]; rfl) signStep hsign
    obtain ⟨signature, hanswer, hrandomizer⟩ := hfaithful request framed hframe
      (startServingOn request state.2.2) signStep hsign
    rw [hcarrier]
    refine ⟨seed, signature, hcached, hanswer, ?_, hserved⟩
    rw [hrandomizer, replayRandomizer_of_cached signStep.2.1.cache sk framed seed hcached]

open scoped Classical in
/-- **And therefore a whole run of the phase.** -/
theorem logFiled_run_with (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey)
    (hpk : sk.publicKey = pk)
    (hshape : SignerShape sk signer)
    (hfaithful : SignerFaithful pk impl hfiles sk signer) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ)),
      LogFiled sk state.2.1 state.2.2.1 →
      ∀ z ∈ support ((simulateQ (servingPhaseWith impl signer)
        computation).run state), LogFiled sk z.2.2.1 z.2.2.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state hinv z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
    exact hinv
  | query_bind queried next ih =>
    intro state hinv z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact ih step.1 step.2
      (logFiled_step_with pk impl hfiles signer sk hpk hshape hfaithful queried state step hstep
        hinv) z hrest

/-- **Nothing is logged at the start**, so the invariant holds there for free. -/
theorem logFiled_nil (sk : SecretKey) (carrier : HandlerCarrier.State) :
    LogFiled sk [] carrier := by
  intro entry hentry
  exact absurd hentry (List.not_mem_nil)

/-- **The log is below the carrier.** Half of `ServingCarrier.AgreesWithLog`, and the half the
carrier's own blindness argument needs: a request the log names has had its digest input filed,
so the signer's own reads are available at the carrier. -/
theorem logServed_subset_served (sk : SecretKey) (log : SigningLog)
    (carrier : HandlerCarrier.State) (hinv : LogFiled sk log carrier)
    (later : QueryCache HashSpec)
    (hlater : ∀ (input : Bytes) (value : HashOutput), carrier.cache input = some value →
      later input = some value)
    (input : Bytes) (hlog : ServingCarrier.logServed sk later log input) :
    HandlerCarrier.Served carrier input := by
  obtain ⟨entry, hentry, framed, hframe, rfl⟩ := hlog
  obtain ⟨seed, -, hcached, -, -, hserved⟩ := hinv entry hentry framed hframe
  rw [replayRandomizer_of_cached later sk framed seed (hlater _ seed hcached)]
  exact hserved

/-! ## The carrier is below the log, as far as the handler decides it

The other direction asks what the carrier serves that the log does not. The handler settles most
of it by itself: it files only where `HandlerCarrier.FilesLeft` holds, and that test reads the
framing, which is set only across a signing step and names that step's own request. So every
served input has the shape of some logged request's digest input, with *some* randomiser.

Which randomiser is not the handler's to settle: pinning the filed input to the one the cache
replays is a statement about what the signer *asks*, namely
`ServedBridge.sign_messageShape_randomizer`, stated along `CacheReplay.QueriesUnder`.
`served_queriesUnder` crosses between the two readings and `servedLog_signer` puts the shape and
the crossing together. -/

/-! ## What the handler files is what the computation consults

Closing the randomiser question means getting from "the handler filed this while running the
signer" to "the signer consults this", which is the crossing
`ServedBridge.sign_messageShape_randomizer` is stated on the far side of:
`CacheReplay.QueriesUnder`, the replay path, against a run of `Scheme.sign` at a different
instantiation of its monad.

`StrippedGame.sign_lift` does the instantiation: signing in the game's monad is the lift of
signing in the hash-only one. `served_queriesUnder` does the crossing by induction on the run:
the run's answer is cached and persists, so at any later cache the replayed answer is the one the
run took, and the continuations agree. It is read at a later cache because that is the only cache
at which they do agree. -/

/-- **An input a run files is one the computation consults**, read at any cache the run's own
extends. -/
theorem served_queriesUnder {α : Type} (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (computation : OracleComp HashSpec α) :
    ∀ (state : (HandlerCarrier.State × τ)) (z : α × (HandlerCarrier.State × τ)),
      z ∈ support ((simulateQ impl
        (OracleComp.liftComp computation OracleWorld)).run state) →
      ∀ later : QueryCache HashSpec,
        (∀ (input : Bytes) (value : HashOutput), z.2.1.cache input = some value →
          later input = some value) →
        ∀ probe : Bytes, HandlerCarrier.Served z.2.1 probe →
          HandlerCarrier.Served state.1 probe ∨ CacheReplay.QueriesUnder later computation probe
      := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz later _ probe hserved
    rw [OracleComp.liftComp_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]] at hserved
    exact Or.inl hserved
  | query_bind input next ih =>
    intro state z hz later hlater probe hserved
    have hz' : z ∈ support ((simulateQ impl
        (liftM (OracleWorld.query (Sum.inr input)) >>=
          fun answer : HashOutput =>
            OracleComp.liftComp (next answer) OracleWorld)).run state) := hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz'
    obtain ⟨step, hstepRun, hrest⟩ := hz'
    have hcached : step.2.1.cache input = some step.1 :=
      hfiles.hashCached input state step hstepRun
    have hpersists : HandlerCarrier.Grows step.2.1 z.2.1 :=
      hfiles.runPersists _ step.2 z hrest
    have hreplay : CacheReplay.replay later input = step.1 := by
      simp [CacheReplay.replay, hlater input step.1 (hpersists.1 input step.1 hcached)]
    rcases ih step.1 step.2 z hrest later hlater probe hserved with hstep | htail
    · rcases hfiles.hashServed input state step hstepRun
        probe hstep with hbefore | rfl
      · exact Or.inl hbefore
      · exact Or.inr (CacheReplay.QueriesUnder.head _ _)
    · exact Or.inr (CacheReplay.QueriesUnder.tail input probe next (by rw [hreplay]; exact htail))

/-- **An input a run of the signer files is one the signer consults.** The signer is taken as a
lift of a hash-only computation, which is the only thing the crossing needs. -/
theorem served_queriesUnder_lift (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (signer : Message → OracleComp OracleWorld (Option Bytes))
    (hashSigner : Message → OracleComp HashSpec (Option Bytes))
    (hlift : ∀ request : Message,
      signer request = OracleComp.liftComp (hashSigner request) OracleWorld)
    (request : Message) (state : (HandlerCarrier.State × τ))
    (z : Option Bytes × (HandlerCarrier.State × τ))
    (hz : z ∈ support ((simulateQ impl
      (signer request)).run state))
    (later : QueryCache HashSpec)
    (hlater : ∀ (input : Bytes) (value : HashOutput), z.2.1.cache input = some value →
      later input = some value)
    (probe : Bytes) (hserved : HandlerCarrier.Served z.2.1 probe) :
    HandlerCarrier.Served state.1 probe ∨
      CacheReplay.QueriesUnder later (hashSigner request) probe := by
  rw [hlift] at hz
  exact served_queriesUnder pk impl hfiles _ state z hz later hlater probe
    hserved

/-! ## The exact containment, at one request

Two readings of a filed input, put together. The carrier says it has the shape of the framing in
flight — that is the filing rule, and it needs no run. The run says the signer consults it, by
`served_queriesUnder`. Only the second pins the randomiser, and only through
`ServedBridge.sign_messageShape_randomizer`: of all the inputs of its framing's digest shape the
signer asks only its own digest's. The shape says *which framing*, the run says *which
randomiser*. -/

/-- **A run under a set framing serves nothing but that framing's shape.** -/
theorem servedFramed_run {α : Type} (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (framed : Bytes) (computation : OracleComp OracleWorld α) (state : (HandlerCarrier.State × τ))
    (hframing : state.1.framing = some framed) (result : α × (HandlerCarrier.State × τ))
    (hresult : result ∈ support ((simulateQ impl
      computation).run state))
    (probe : Bytes) (hserved : HandlerCarrier.Served result.2.1 probe) :
    HandlerCarrier.Served state.1 probe ∨
      ∃ randomizer : Digest, probe = Hashing.messageInput randomizer pk framed := by
  refine (hfiles.invariant
    (fun carrier => carrier.framing = some framed ∧
      ∀ p : Bytes, HandlerCarrier.Served carrier p →
        HandlerCarrier.Served state.1 p ∨
          ∃ randomizer : Digest, p = Hashing.messageInput randomizer pk framed)
    (fun carrier input answer hinv => ⟨hinv.1, hinv.2⟩)
    (fun carrier input hinv hfiles => ⟨by rw [HandlerCarrier.framing_file]; exact hinv.1,
      fun p hp => ?_⟩)
    computation state result hresult ⟨hframing, fun p hp => Or.inl hp⟩).2 probe hserved
  rcases Multiset.mem_cons.mp hp with rfl | hrest
  · obtain ⟨witness, hwitness, randomizer, hinput⟩ := hfiles
    rw [hinv.1] at hwitness
    rw [← Option.some.inj hwitness] at hinput
    exact Or.inr ⟨randomizer, hinput⟩
  · exact hinv.2 p hrest

/-- **A served request serves exactly its own digest input.** The randomiser is the one the
cache replays, which is what `ServingCarrier.logServed` names it by. The shape says which
framing and the crossing says which randomiser; neither alone would do. -/
theorem servedLog_signer (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey)
    (hpk : sk.publicKey = pk) (_hshape : SignerShape sk signer)
    (warm : QueryCache HashSpec) (hpins : SignerPins sk warm signer)
    (request : Message) (framed : Bytes) (hframe : request.frame = some framed)
    (state : (HandlerCarrier.State × τ)) (hframing : state.1.framing = some framed)
    (z : Option Bytes × (HandlerCarrier.State × τ))
    (hz : z ∈ support ((simulateQ impl
      (signer request)).run state))
    (later : QueryCache HashSpec)
    (hwarm : ∀ (input : Bytes) (value : HashOutput), warm input = some value →
      later input = some value)
    (hlater : ∀ (input : Bytes) (value : HashOutput), z.2.1.cache input = some value →
      later input = some value)
    (probe : Bytes) (hserved : HandlerCarrier.Served z.2.1 probe) :
    HandlerCarrier.Served state.1 probe ∨
      probe = Hashing.messageInput (HonestProbes.replayRandomizer later sk framed)
        sk.publicKey framed := by
  subst hpk
  obtain ⟨hashSigner, hlift, hpin⟩ := hpins
  rcases served_queriesUnder_lift sk.publicKey impl hfiles signer hashSigner
    hlift request state z hz later hlater probe hserved with hbefore | hquery
  · exact Or.inl hbefore
  rcases servedFramed_run sk.publicKey impl hfiles framed (signer request) state
    hframing z hz probe hserved with hbefore | ⟨randomizer, rfl⟩
  · exact Or.inl hbefore
  exact Or.inr (congrArg (fun value => Hashing.messageInput value sk.publicKey framed)
    (hpin request framed hframe later hwarm randomizer hquery))

/-! ## The carrier is below the log, at a run

The invariant is quantified over the cache it will be read at, because the cache a run ends with
is not known while the run is going on, and the randomiser the log names is read back off it.
Quantifying instead of fixing is what lets one statement serve every step.

The adversary's step needs nothing but `servedClear_run`: with the framing clear nothing is
filed, so the served set does not move and the invariant is carried across unchanged. That is
the whole of the adversary's contribution to this direction, and it is the property the cache
proxy could not have had. -/

/-- **A run under a clear framing serves nothing new.** -/
theorem servedClear_run {α : Type} (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (computation : OracleComp OracleWorld α) (state : (HandlerCarrier.State × τ))
    (hclear : state.1.framing = none) (result : α × (HandlerCarrier.State × τ))
    (hresult : result ∈ support ((simulateQ impl
      computation).run state))
    (probe : Bytes) (hserved : HandlerCarrier.Served result.2.1 probe) :
    HandlerCarrier.Served state.1 probe :=
  (hfiles.invariant
    (fun carrier => carrier.framing = none ∧
      ∀ p : Bytes, HandlerCarrier.Served carrier p → HandlerCarrier.Served state.1 p)
    (fun _ _ _ hinv => ⟨hinv.1, hinv.2⟩)
    (fun carrier input hinv hfiles =>
      absurd hfiles (HandlerCarrier.not_filesLeft_of_clear pk carrier hinv.1 input))
    computation state result hresult ⟨hclear, fun _ hp => hp⟩).2 probe hserved

/-- **What a run leaves true of its carrier and its log**, read at any cache the carrier's own
extends. -/
@[expose] def CarrierLogged (sk : SecretKey) (warm : QueryCache HashSpec) (log : SigningLog)
    (carrier : HandlerCarrier.State) : Prop :=
  ∀ later : QueryCache HashSpec,
    (∀ (input : Bytes) (value : HashOutput), carrier.cache input = some value →
      later input = some value) →
    (∀ (input : Bytes) (value : HashOutput), warm input = some value →
      later input = some value) →
    ∀ input : Bytes, HandlerCarrier.Served carrier input →
      ServingCarrier.logServed sk later log input

/-- An input the log serves is still served once the log is extended. -/
theorem logServed_append (sk : SecretKey) (cache : QueryCache HashSpec) (log : SigningLog)
    (entry : (_ : Message) × Option Bytes) (input : Bytes)
    (hlog : ServingCarrier.logServed sk cache log input) :
    ServingCarrier.logServed sk cache (log ++ [entry]) input := by
  obtain ⟨probe, hprobe, framed, hframe, hinput⟩ := hlog
  exact ⟨probe, List.mem_append.mpr (Or.inl hprobe), framed, hframe, hinput⟩

open scoped Classical in
/-- **A step of the phase preserves it.** -/
theorem carrierLogged_step_with (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey)
    (hpk : sk.publicKey = pk) (hshape : SignerShape sk signer)
    (warm : QueryCache HashSpec) (hpins : SignerPins sk warm signer)
    (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ))
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ)))
    (hstep : step ∈ support (((servingPhaseWith impl signer) queried).run
      state)) (hclear : state.2.2.1.framing = none)
    (hinv : CarrierLogged sk warm state.2.1 state.2.2.1) :
    CarrierLogged sk warm step.2.2.1 step.2.2.2.1 := by
  classical
  have hgrow := servingPhaseWith_persists pk impl hfiles signer queried state step hstep
  rcases queried with world | request
  · have hrun : step ∈ support
        ((simulateQ impl
          (((recordedAdversaryImpl world).run).run state.2.1)).run state.2.2 >>=
          fun inner =>
            (pure (inner.1.1.1, (state.1 * inner.1.1.2, inner.1.2, inner.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ))))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    have hlog : step.2.2.1 = state.2.1 := by
      have hmapped := hinner
      rw [run_recordedAdversaryImpl, simulateQ_map, StateT.run_map, support_map] at hmapped
      obtain ⟨raw, -, hinnerEq⟩ := hmapped
      rw [hpure, ← hinnerEq]
    have hcarrier : step.2.2.2 = inner.2 := by rw [hpure]
    rw [hlog]
    intro later hlater hwarm input hserved
    refine hinv later (fun probe value hvalue => hlater probe value (hgrow.1 probe value hvalue))
      hwarm input ?_
    rw [hcarrier] at hserved
    exact servedClear_run pk impl hfiles _ state.2.2 hclear inner hinner input
      hserved
  · have hrun : step ∈ support
        ((simulateQ impl
          (((recordedSigningOracle signer request).run).run state.2.1)).run
            (startServingOn request state.2.2) >>= fun inner =>
          (pure (inner.1.1.1,
            (state.1 * inner.1.1.2, inner.1.2, stopServingOn inner.2)) :
            ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
              (Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ))))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [run_recordedSigningOracle] at hinner
    obtain ⟨signStep, hsign, hvalue⟩ := state_of_bind_pure pk impl hfiles
      (signer request) _ (startServingOn request state.2.2) inner hinner
    have hlog : step.2.2.1 = state.2.1 ++ [⟨request, signStep.1⟩] := by
      rw [hpure]
      exact congrArg (fun y => y.1.2) hvalue
    have hcarrier : step.2.2.2.1 = HandlerCarrier.clearFraming signStep.2.1 := by
      rw [hpure]
      exact congrArg (fun y => HandlerCarrier.clearFraming y.2.1) hvalue
    rw [hlog]
    intro later hlater hwarm input hserved
    have hlaterSign : ∀ (probe : Bytes) (value : HashOutput),
        signStep.2.1.cache probe = some value → later probe = some value :=
      fun probe value hvalue => hlater probe value (by rw [hcarrier]; exact hvalue)
    have hservedSign : HandlerCarrier.Served signStep.2.1 input := by
      rw [hcarrier] at hserved
      exact hserved
    have hold : HandlerCarrier.Served (startServingOn request state.2.2).1 input →
        ServingCarrier.logServed sk later (state.2.1 ++ [⟨request, signStep.1⟩]) input := by
      intro hbefore
      refine logServed_append sk later state.2.1 _ input
        (hinv later (fun probe value hvalue => hlater probe value (hgrow.1 probe value hvalue))
          hwarm input ?_)
      cases hframe : request.frame with
      | none =>
        rw [show startServingOn request state.2.2 = state.2.2 from by
          simp only [startServingOn, hframe]] at hbefore
        exact hbefore
      | some framed =>
        rw [show (startServingOn request state.2.2).1 =
          HandlerCarrier.setFraming state.2.2.1 framed from by
            simp only [startServingOn, hframe]] at hbefore
        exact hbefore
    cases hframe : request.frame with
    | none =>
      refine hold ?_
      exact servedClear_run pk impl hfiles
        (signer request) (startServingOn request state.2.2)
        (by simp only [startServingOn, hframe]; exact hclear) signStep hsign input hservedSign
    | some framed =>
      rcases servedLog_signer pk impl hfiles signer sk hpk hshape warm hpins
        request framed hframe
        (startServingOn request state.2.2) (by simp only [startServingOn, hframe]; rfl) signStep
        hsign
        later hwarm hlaterSign input hservedSign with hbefore | hinput
      · exact hold hbefore
      · exact ⟨⟨request, signStep.1⟩,
          List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)), framed, hframe, hinput⟩

open scoped Classical in
/-- **And therefore a whole run of the phase.** -/
theorem carrierLogged_run_with (pk : PublicKey)
    {τ : Type} (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (hfiles : Files pk impl)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey)
    (hpk : sk.publicKey = pk) (hshape : SignerShape sk signer)
    (warm : QueryCache HashSpec) (hpins : SignerPins sk warm signer)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : Multiplicative Tally × SigningLog × (HandlerCarrier.State × τ)),
      state.2.2.1.framing = none → CarrierLogged sk warm state.2.1 state.2.2.1 →
      ∀ z ∈ support ((simulateQ (servingPhaseWith impl signer)
        computation).run state), CarrierLogged sk warm z.2.2.1 z.2.2.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state hclear hinv z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
    exact hinv
  | query_bind queried next ih =>
    intro state hclear hinv z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact ih step.1 step.2
      (framing_clear_step_with pk impl hfiles signer queried state hclear step hstep)
      (carrierLogged_step_with pk impl hfiles signer sk hpk hshape warm hpins queried state step
        hstep hclear hinv) z hrest

/-! ## How long the disclosing recording is

The disclosing recording is a list of **fresh** queries passing the carrier's served-set test, so
its length is bounded by the number of *distinct* served inputs. The agreement says what those
are: the image of the log under one map, one input per logged request that has a framing. Hence
the recording is no longer than the signing count, and the cap it has to meet is `signingLimit`.

**Freshness is what makes "distinct" the right word**: a recorded query is not cached when it is
recorded and is cached forever after, so no input is recorded twice.

**The headroom is a factor of five over four.** The concentration holds up to `5 * 2 ^ 62`;
`signingLimit` is `2 ^ 64 = 4 * 2 ^ 62`, which fits, and `2 * signingLimit` does not. So an extra
entry per served request would have to be excluded rather than paid for. It is excluded by the
filing test: a request's own `PRF_msg` query is `Hashing.randomizerInput` at the framing in
flight, and `ServedBridge.randomizerInput_ne_messageInput` says that is never
`Hashing.messageInput` at the same framing, since the format identity inserts `PK.root` before the
message. `HandlerCarrier.FilesLeft` compares against the framing in flight and nothing else, so it
is false there. -/

/-- The digest input a logged entry serves, when it has a framing. -/
@[expose] def servedOf (sk : SecretKey) (cache : QueryCache HashSpec)
    (entry : (_ : Message) × Option Bytes) : Option Bytes :=
  (entry.1.frame).map fun framed =>
    Hashing.messageInput (HonestProbes.replayRandomizer cache sk framed) sk.publicKey framed

/-- **The log's served inputs are the image of the log**, which is what bounds how many there
are. -/
theorem mem_map_servedOf (sk : SecretKey) (cache : QueryCache HashSpec) (log : SigningLog)
    (input : Bytes) (hlog : ServingCarrier.logServed sk cache log input) :
    some input ∈ log.map (servedOf sk cache) := by
  obtain ⟨entry, hentry, framed, hframe, hinput⟩ := hlog
  refine List.mem_map.mpr ⟨entry, hentry, ?_⟩
  rw [servedOf, hframe, Option.map_some, hinput]

/-- **A list of distinct served inputs is no longer than the log.** -/
theorem length_le_log_of_served (sk : SecretKey) (log : SigningLog)
    (carrier : HandlerCarrier.State)
    (hagree : ServingCarrier.AgreesWithLog sk log carrier)
    (inputs : List Bytes) (hnodup : inputs.Nodup)
    (hserved : ∀ input ∈ inputs, HandlerCarrier.Served carrier input) :
    inputs.length ≤ log.length := by
  have hsub : inputs.map some ⊆ log.map (servedOf sk carrier.cache) := by
    intro value hvalue
    obtain ⟨input, hinput, rfl⟩ := List.mem_map.mp hvalue
    exact mem_map_servedOf sk carrier.cache log input ((hagree input).mp (hserved input hinput))
  have hnodupMap : (inputs.map some).Nodup :=
    hnodup.map (fun _ _ h => Option.some.inj h)
  simpa using (hnodupMap.subperm hsub).length_le

/-- **The disclosing recording is no longer than the signing count.** The recorder's own
freshness guard supplies the distinctness; the agreement supplies everything else. -/
theorem record_length_le_log (sk : SecretKey) (log : SigningLog)
    (carrier : HandlerCarrier.State)
    (hagree : ServingCarrier.AgreesWithLog sk log carrier)
    (record : List (Bytes × HashOutput)) (hnodup : (record.map Prod.fst).Nodup)
    (hserved : ∀ entry ∈ record, HandlerCarrier.Served carrier entry.1) :
    record.length ≤ log.length := by
  have hbound := length_le_log_of_served sk log carrier hagree (record.map Prod.fst) hnodup
    (fun input hinput => by
      obtain ⟨entry, hentry, hvalue⟩ := List.mem_map.mp hinput
      rw [← hvalue]
      exact hserved entry hentry)
  simpa using hbound

/-- **And therefore inside the concentration's cap.** `signingLimit` is `4 * 2 ^ 62` and the
concentration holds to `5 * 2 ^ 62`, so the disclosing cap is met with a quarter to spare. -/
theorem record_length_le_cap (sk : SecretKey) (log : SigningLog)
    (carrier : HandlerCarrier.State)
    (hagree : ServingCarrier.AgreesWithLog sk log carrier)
    (record : List (Bytes × HashOutput)) (hnodup : (record.map Prod.fst).Nodup)
    (hserved : ∀ entry ∈ record, HandlerCarrier.Served carrier entry.1)
    (hlimit : log.length ≤ signingLimit) : record.length ≤ 5 * 2 ^ 62 :=
  le_trans (le_trans (record_length_le_log sk log carrier hagree record hnodup hserved) hlimit)
    (by norm_num [signingLimit])

/-! ## The coldness of a message-digest input

A canonical input is a tweakable input at a structural address, and `HashSeparation` keeps a
message-digest input apart from tweakable inputs under the one coincidence a good walk excludes.
So the open cache is silent at it. -/

/-- **And at a message-digest input**, the key being no coincidence. -/
theorem openCache_messageInput_eq_none (publicSeed randomizer : Digest) (pk : PublicKey)
    (message : Bytes) (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (available : CanonicalGraph.Node → Prop)
    (table : CanonicalGraph.Cells × CanonicalGraph.Padding) :
    OpenCache.openCache publicSeed available table
      (Hashing.messageInput randomizer pk message) = none :=
  OpenCache.openCache_eq_none_of_not_canonical (publicSeed := publicSeed)
    (available := available) table _
    (fun parent => Ne.symm
      (HashSeparation.message_tweakable_ne hpublic (withinBounds_structural parent)))

/-- **`Scheme.sign` asks its randomiser and then its digest.** -/
theorem signerShape_sign (sk : SecretKey) : SignerShape sk (Scheme.sign sk) :=
  fun request framed hframe => sign_shape sk request framed hframe

/-- **And its digest query is the only one of its framing's shape**, on a good walk. Nothing is
stripped, so the pin holds at every cache and the table is empty. -/
theorem signerPins_sign (sk : SecretKey)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root)) :
    SignerPins sk ∅ (Scheme.sign sk) :=
  ⟨fun request => Scheme.sign (m := OracleComp HashSpec) sk request,
    fun request => StrippedGame.sign_lift sk request,
    fun request framed hframe later _ randomizer hquery =>
      ServedBridge.sign_messageShape_randomizer later sk request framed hframe hpublic randomizer
        hquery⟩

/-! ## The log's two readings of a served input

`ServedLog.servedLog` names a served input by the randomiser in the published signature;
`ServingCarrier.logServed` by the one the cache replays. The two readings meet at `LogFiled`'s
own clauses: the invariant carries the signature the log kept and the cache entry the replay
reads, and says they agree. `Signature.fromBytes_toBytes` does the rest. -/

/-- **The log's two readings of a served input are one.** -/
theorem servedLog_iff_logServed (sk : SecretKey) (pk : PublicKey) (hpk : sk.publicKey = pk)
    (log : SigningLog) (carrier : HandlerCarrier.State) (hinv : LogFiled sk log carrier)
    (later : QueryCache HashSpec)
    (hlater : ∀ (input : Bytes) (value : HashOutput), carrier.cache input = some value →
      later input = some value)
    (result : (Outcome × Nat) × QueryCache HashSpec) (hsigned : result.1.1.signed = log)
    (input : Bytes) :
    ServedLog.servedLog pk result input ↔ ServingCarrier.logServed sk later log input := by
  subst hpk
  constructor
  · rintro ⟨entry, hentry, framed, bytes, parsed, hframe, hanswer, hparsed, rfl⟩
    rw [hsigned] at hentry
    obtain ⟨seed, signature, hcached, hsigAnswer, hrandomizer, -⟩ := hinv entry hentry framed hframe
    have hbytes : bytes = signature.toBytes := Option.some.inj (hanswer.symm.trans hsigAnswer)
    have hparse : parsed = signature := by
      rw [hbytes, Signature.fromBytes_toBytes] at hparsed
      exact (Option.some.inj hparsed).symm
    refine ⟨entry, hentry, framed, hframe, ?_⟩
    rw [hparse, hrandomizer,
      replayRandomizer_of_cached later sk framed seed (hlater _ seed hcached)]
  · rintro ⟨entry, hentry, framed, hframe, rfl⟩
    obtain ⟨seed, signature, hcached, hsigAnswer, hrandomizer, -⟩ := hinv entry hentry framed hframe
    refine ⟨entry, by rw [hsigned]; exact hentry, framed, signature.toBytes, signature, hframe,
      hsigAnswer, Signature.fromBytes_toBytes signature, ?_⟩
    rw [hrandomizer, replayRandomizer_of_cached later sk framed seed (hlater _ seed hcached)]

end SLHDSA.SHAKE128s.ServedAgreement
