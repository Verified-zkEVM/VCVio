/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierTail
public import HashSig.SLHDSA.SHAKE128s.Proof.FusedCover
public import HashSig.SLHDSA.SHAKE128s.Proof.AnswerCarrier

/-!
# The cover, reached through three stages

`NoticingCover.mem_recordOf_of_cache_reaches` says a query the run ends holding is recorded on
one side or the other, at one run of the recorder that notices.
`FusedCover.mem_recordOf_of_cache_reaches` says it at a bracketed phase. The carrier tail is
neither: it is three of those in sequence, under a handler that also carries a counter.

This file closes both gaps, in that order.

## The counter comes off first

The two cover lemmas are stated at `RecorderView.noticingRecorderOf`, whose state is
`StateOf σ`; the tail's handler is that recorder with a counter beside it. The counter is not a
difficulty, because `CountedHandler.forgetsAlong_withCount` already says the counted handler
forgets to the one underneath — at `π = id`, which is the instance nobody had taken. So a
supported result of the tail's stage is a supported result of the bare recorder's, with the same
carrier and the same two recordings, and every cover fact is asked of the latter.

**The brackets survive the same way.** `ServingForget.run_fuseServing_conj` carries a bracketed
phase to a bracketed phase along any map the brackets commute with, and dropping a counter
commutes with brackets that write the framing — one `cases` on the request's frame, exactly as
summing two counter slots did.

## Then the stages chain, and the chaining is a case split per boundary

At each sequencing point the input is either still fresh — carry the freshness forward — or
already answered, in which case `cache_value_persists` says the value it was answered with is
the value the tail ends holding, the cover at *that* stage files it, and `recordOf_prefix`
carries the entry to the end. Two boundaries, two case splits, and nothing else.

`reaches` is threaded by `NoticingCover.reaches_run` across the two plain stages. Across the
phase it is a hypothesis, `hphaseReaches`, because `FusedCover` proves no propagation for it and
inventing one here would be guessing at what a future `reaches` needs. At the carrier's own
`reaches` — which is satisfied everywhere, the cover being discharged with a frame in flight as
well as without — it is immediate.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierCover

variable {α : Type}

open Security RecorderView CarriedWitness PhaseFusion RecordedQueries BracketedRun
open CarrierTail ServedAgreement

variable (pk : PublicKey)

/-- The tail's state, with the counter dropped. -/
def dropCount (state : HandlerCarrier.State ×
    ((DigestTape.Record × DigestTape.Record) × Nat)) :
    RecorderView.StateOf HandlerCarrier.State :=
  (state.1, state.2.1)

/-- **The counted carrier recorder forgets to the recorder that notices**, which is
`CountedHandler.forgetsAlong_withCount` at the identity. -/
theorem forgetsAlong_dropCount (rightKeep : Bytes → HandlerCarrier.State → Prop) :
    ServingForget.ForgetsAlong dropCount (CarrierFiles.countedCarrierRecorder pk rightKeep)
      (@noticingRecorderOf HandlerCarrier.State (servingView pk) (disclosingKeep pk) rightKeep) :=
  CountedHandler.forgetsAlong_withCount (fun state : RecorderView.StateOf HandlerCarrier.State =>
      state) _ _ (fun computation state => by
    rw [show (fun z : _ × RecorderView.StateOf HandlerCarrier.State => (z.1, z.2)) = id from
      funext fun z => rfl, id_map])

/-- **A stage of the tail is a run of the recorder that notices.** -/
theorem mem_support_dropCount_run {α : Type}
    (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (computation : OracleComp OracleWorld α)
    (state : HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Nat))
    (result : α × (HandlerCarrier.State ×
      ((DigestTape.Record × DigestTape.Record) × Nat)))
    (hmem : result ∈ support
      ((simulateQ (CarrierFiles.countedCarrierRecorder pk rightKeep) computation).run state)) :
    (result.1, dropCount result.2) ∈ support
      ((simulateQ (@noticingRecorderOf HandlerCarrier.State (servingView pk)
        (disclosingKeep pk) rightKeep) computation).run (dropCount state)) := by
  rw [← forgetsAlong_dropCount pk rightKeep computation state, support_map]
  exact ⟨result, hmem, rfl⟩

/-- Dropping the counter commutes with opening a signing bracket. -/
theorem dropCount_startServingOn (request : Message)
    (state : HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Nat)) :
    dropCount (startServingOn request state) = startServingOn request (dropCount state) := by
  rw [startServingOn, startServingOn]
  cases request.frame with
  | none => rfl
  | some framed => rfl

/-- Dropping the counter commutes with closing a signing bracket. -/
theorem dropCount_stopServingOn
    (state : HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Nat)) :
    dropCount (stopServingOn state) = stopServingOn (dropCount state) := rfl

/-- **And the tail's bracketed stage is a bracketed phase of the recorder that notices.** -/
theorem mem_support_dropCount_phase {α : Type} {ω : Type} [Monoid ω]
    (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (phase : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : ω) (log : SigningLog)
    (state : HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Nat))
    (result : α × (ω × SigningLog × (HandlerCarrier.State ×
      ((DigestTape.Record × DigestTape.Record) × Nat))))
    (hmem : result ∈ support ((simulateQ
      (fuseServing (CarrierFiles.countedCarrierRecorder pk rightKeep) inner
        startServingOn stopServingOn) phase).run (accumulated, log, state))) :
    (result.1, (result.2.1, result.2.2.1, dropCount result.2.2.2)) ∈ support
      ((simulateQ (fuseServing (@noticingRecorderOf HandlerCarrier.State (servingView pk)
        (disclosingKeep pk) rightKeep) inner startServingOn stopServingOn) phase).run
        (accumulated, log, dropCount state)) := by
  rw [← ServingForget.run_fuseServing_conj dropCount
      (CarrierFiles.countedCarrierRecorder pk rightKeep) _ inner
      startServingOn stopServingOn startServingOn stopServingOn
      dropCount_startServingOn dropCount_stopServingOn
      (forgetsAlong_dropCount pk rightKeep) phase accumulated log state,
    support_map]
  exact ⟨result, hmem, rfl⟩

/-! ## The chain

`reaches` is gone from the statement, and that is deliberate rather than a simplification.
The carrier's cover holds at **every** view — `CarrierDemand.cover_inFlight` is what makes that
true, the forgery's digest input being left-kept at a view with a request in flight just as it
is at one without — so threading a predicate to the views the run can be in would buy nothing
and would need a propagation across the phase that `FusedCover` does not prove. A future cover
that did *not* hold in flight would need `reaches` back, and the phase propagation is the one
piece that would then be missing; it is named here so nobody has to rediscover that.

With the cover unconditional, `FusedCover`'s signing obligation `hsub` is discharged inside:
a signing sub-run is a plain noticing run at the view the opening bracket produced, and the
bracket keeps the cache, so `NoticingCover.mem_recordOf_of_cache_reaches` answers it. -/

set_option maxHeartbeats 400000 in
-- The three-stage case split unfolds the fused handler's state tuple at every stage.
open scoped Classical in
/-- **A query the carrier tail ends holding is recorded on one side or the other.** The cover
lemma, reached through all three stages. -/
theorem cover_carrierTail
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (inClass : Bytes → Prop) (adversary : Adversary) (walk : Walk)
    (hcover : ∀ (probe : Bytes) (view : HandlerCarrier.State), inClass probe →
      @CacheView.cacheOf HandlerCarrier.State (servingView (keyAt walk)) view probe = none →
        disclosingKeep (keyAt walk) probe view ∨ rightKeep walk probe view)
    (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hresult : result ∈ support (carrierTail rightKeep adversary walk))
    (input : Bytes) (answer : HashOutput) (hclass : inClass input)
    (hfresh : walk.2 input = none)
    (hfinal : result.2.1 input = some answer) :
    (input, answer) ∈ result.2.2.1 ∨ (input, answer) ∈ result.2.2.2 := by
  classical
  let : CacheView HandlerCarrier.State := servingView (keyAt walk)
  have hbeforeRecord : ∀ (request : Message)
      (state : RecorderView.StateOf HandlerCarrier.State),
      (startServingOn request state).2 = state.2 := by
    intro request state
    rw [startServingOn]
    cases request.frame with
    | none => rfl
    | some framed => rfl
  have hcover' : ∀ (probe : Bytes) (view : HandlerCarrier.State), inClass probe →
      (fun _ : HandlerCarrier.State => True) view →
      @CacheView.cacheOf HandlerCarrier.State (servingView (keyAt walk)) view probe = none →
        disclosingKeep (keyAt walk) probe view ∨ rightKeep walk probe view :=
    fun probe view hc _ hf => hcover probe view hc hf
  rw [carrierTail, mem_support_bind_iff] at hresult
  obtain ⟨keys, hkeys, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨middle, hmiddle, hrest⟩ := hrest
  rw [mem_support_bind_iff] at hrest
  obtain ⟨final, hlast, hpure⟩ := hrest
  rw [support_pure, Set.mem_singleton_iff] at hpure
  have h1 := mem_support_dropCount_run (keyAt walk) (rightKeep walk) _ _ keys hkeys
  have h2 := mem_support_dropCount_phase (keyAt walk) (rightKeep walk)
    (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1)) _ 1 [] keys.2 middle
    hmiddle
  have h3 := mem_support_dropCount_run (keyAt walk) (rightKeep walk) _ _ final hlast
  have hgoalRecord : result.2.2 = (dropCount final.2).2 := by rw [hpure]; rfl
  have hgoalCache : @CacheView.cacheOf HandlerCarrier.State (servingView (keyAt walk))
      (dropCount final.2).1 input = some answer := by
    rw [← hfinal, hpure]
    rfl
  rw [hgoalRecord]
  -- the signing obligation, at the unconditional cover
  have hsub : ∀ (request : Message) (log : SigningLog)
      (state : RecorderView.StateOf HandlerCarrier.State)
      (z : (((OracleWorld + SigningSpec).Range (Sum.inr request) × Multiplicative Tally) ×
          SigningLog) × RecorderView.StateOf HandlerCarrier.State),
      z ∈ support ((simulateQ (@noticingRecorderOf HandlerCarrier.State (servingView (keyAt walk))
        (disclosingKeep (keyAt walk)) (rightKeep walk))
        ((((recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          (Sum.inr request)).run).run log)).run (startServingOn request state)) →
      (fun _ : HandlerCarrier.State => True) state.1 →
      @CacheView.cacheOf HandlerCarrier.State (servingView (keyAt walk)) state.1 input = none →
      @CacheView.cacheOf HandlerCarrier.State (servingView (keyAt walk)) z.2.1 input =
        some answer →
        (input, answer) ∈ z.2.2.1 ∨ (input, answer) ∈ z.2.2.2 := by
    intro request log state z hz _ hstateFresh hzFinal
    refine NoticingCover.mem_recordOf_of_cache_reaches (disclosingKeep (keyAt walk))
      (rightKeep walk) inClass (fun _ => True) hcover' (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial) _ (startServingOn request state) z hz input answer hclass trivial
      ?_ hzFinal
    rw [show @CacheView.cacheOf HandlerCarrier.State (servingView (keyAt walk))
        (startServingOn request state).1 =
      @CacheView.cacheOf HandlerCarrier.State (servingView (keyAt walk)) state.1 from by
        rw [startServingOn]; cases request.frame with
        | none => rfl
        | some framed => rfl]
    exact hstateFresh
  have hbeforeCache : ∀ (request : Message) (state : RecorderView.StateOf HandlerCarrier.State),
      @CacheView.cacheOf HandlerCarrier.State (servingView (keyAt walk))
          (startServingOn request state).1 =
        @CacheView.cacheOf HandlerCarrier.State (servingView (keyAt walk)) state.1 := by
    intro request state
    rw [startServingOn]
    cases request.frame with
    | none => rfl
    | some framed => rfl
  by_cases hone : @CacheView.cacheOf HandlerCarrier.State (servingView (keyAt walk))
      (dropCount keys.2).1 input = none
  · by_cases htwo : @CacheView.cacheOf HandlerCarrier.State (servingView (keyAt walk))
        (dropCount middle.2.2.2).1 input = none
    · exact NoticingCover.mem_recordOf_of_cache_reaches (disclosingKeep (keyAt walk))
        (rightKeep walk) inClass (fun _ => True) hcover' (fun _ _ _ _ => trivial)
        (fun _ _ _ => trivial) _ (dropCount middle.2.2.2) (final.1, dropCount final.2) h3
        input answer hclass trivial htwo hgoalCache
    · obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp htwo
      have hsame : value = answer := by
        have := NoticingCover.cache_value_persists (disclosingKeep (keyAt walk)) (rightKeep walk)
          _ (dropCount middle.2.2.2) (final.1, dropCount final.2) h3 input value hvalue
        rw [this] at hgoalCache
        exact Option.some_injective _ hgoalCache
      subst hsame
      have hmem := FusedCover.mem_recordOf_of_cache_reaches (disclosingKeep (keyAt walk))
        (rightKeep walk) (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
        startServingOn stopServingOn inClass (fun _ => True) input value hclass hcover'
        (fun _ _ _ _ => trivial) (fun _ _ _ => trivial)
        hbeforeRecord (fun _ => rfl) hbeforeCache (fun _ => rfl) (fun _ => trivial) hsub _
        (1, [], dropCount keys.2)
        (middle.1, (middle.2.1, middle.2.2.1, dropCount middle.2.2.2)) h2 trivial hone hvalue
      obtain ⟨hleftPrefix, hrightPrefix⟩ := NoticingCover.recordOf_prefix
        (disclosingKeep (keyAt walk)) (rightKeep walk) _ (dropCount middle.2.2.2)
        (final.1, dropCount final.2) h3
      exact hmem.imp (fun h => hleftPrefix.subset h) (fun h => hrightPrefix.subset h)
  · obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hone
    have htwo := FusedCover.cache_value_persists (disclosingKeep (keyAt walk)) (rightKeep walk)
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      startServingOn stopServingOn hbeforeCache (fun _ => rfl) _ (1, [], dropCount keys.2)
      (middle.1, (middle.2.1, middle.2.2.1, dropCount middle.2.2.2)) h2 input value hvalue
    have hthree := NoticingCover.cache_value_persists (disclosingKeep (keyAt walk))
      (rightKeep walk) _ (dropCount middle.2.2.2) (final.1, dropCount final.2) h3 input value htwo
    have hsame : value = answer := by
      rw [hthree] at hgoalCache
      exact Option.some_injective _ hgoalCache
    subst hsame
    have hmem := NoticingCover.mem_recordOf_of_cache_reaches (disclosingKeep (keyAt walk))
      (rightKeep walk) inClass (fun _ => True) hcover' (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial) _ (dropCount (startAt walk.2, (([], []), 0)))
      (keys.1, dropCount keys.2) h1 input value hclass trivial hfresh hvalue
    obtain ⟨hleftPhase, hrightPhase⟩ := FusedCover.recordOf_prefix (disclosingKeep (keyAt walk))
      (rightKeep walk) (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      startServingOn stopServingOn hbeforeRecord (fun _ => rfl) _ (1, [], dropCount keys.2)
      (middle.1, (middle.2.1, middle.2.2.1, dropCount middle.2.2.2)) h2
    obtain ⟨hleftLast, hrightLast⟩ := NoticingCover.recordOf_prefix (disclosingKeep (keyAt walk))
      (rightKeep walk) _ (dropCount middle.2.2.2) (final.1, dropCount final.2) h3
    exact hmem.imp (fun h => hleftLast.subset (hleftPhase.subset h))
      (fun h => hrightLast.subset (hrightPhase.subset h))

/-! ## The cover's hypothesis, at the carrier's own two tests

`cover_carrierTail` takes the cover as a hypothesis. Here it is discharged, and it turns out to
need **no case on the framing and no cache hypothesis at all** — which is worth saying, because
the in-flight branch (`CarrierDemand.cover_inFlight`) looked like it would be the work.

The reason is that `AnswerCarrier.FilesRandomiser` *is* a membership of the PRF class, read at
one frame: it says the input is `randomizerInput prfSeed pk.seed framed` for the frame in
flight, and that is already `RandomizerGate.PrfClass prfSeed input` with `seed := pk.seed` and
`message := framed`. So at the narrowed class the clause is refuted outright, with the frame
never inspected. `CarrierDemand.prfClass_of_inFlight_coincidence` is the same observation
pointed the other way, and it is why the narrowing is the right one.

**This is where the unconditional cover's price is paid.** Dropping `reaches` from
`cover_carrierTail` did not make the residue disappear; it moved it into the class, exactly
where the cache route already keeps it. The narrowed class is the invoice. -/

/-- **A randomiser the carrier would file is of the PRF class.** -/
theorem not_filesRandomiser_of_not_prfClass (prfSeed : Digest) (publicKey : PublicKey)
    (state : HandlerCarrier.State) (input : Bytes)
    (hprf : ¬ RandomizerGate.PrfClass prfSeed input) :
    ¬ AnswerCarrier.FilesRandomiser prfSeed publicKey state input := by
  rintro ⟨framed, -, hinput⟩
  exact hprf ⟨publicKey.seed, framed, hinput⟩

open scoped Classical in
/-- **The cover at the carrier's two tests**, at the narrowed class and at every view. -/
theorem cover_carrierRightKeep (walk : Walk) (probe : Bytes) (view : HandlerCarrier.State)
    (hclass : CombinedCharge.IsMessageInput (keyAt walk) probe)
    (hprf : ¬ RandomizerGate.PrfClass walk.1.1.2.1 probe) :
    disclosingKeep (keyAt walk) probe view ∨ AnswerCarrier.carrierRightKeep walk probe view := by
  classical
  by_cases hleft : disclosingKeep (keyAt walk) probe view
  · exact Or.inl hleft
  · exact Or.inr ⟨⟨hclass,
      not_filesRandomiser_of_not_prfClass walk.1.1.2.1 (keyAt walk) view probe hprf⟩, hleft⟩

/-! ## And at the run the answer side names

`AnswerCarrier.answerCarrierRun` is `AnswerShape.forgetRecord` over the tail, and that map
**drops the record from the value and keeps the whole recorder state** — the same fact that let
`hcoverage` transport free. So the cover arrives here by `support_map` and nothing else. -/

end SlhDsaSecurity.CarrierCover
