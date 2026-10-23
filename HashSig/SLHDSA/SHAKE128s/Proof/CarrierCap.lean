/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierClearFraming
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierRecord

/-!
# The disclosing cap at the carrier tail

`leftRecord_length_le_cap_carrierTail` bounds the disclosing recording of `CarrierTail.carrierTail`
at `5 * 2 ^ 62`, the cap the load concentration needs, and it does so **structurally**: the
carrier files on served requests, so the recording holds one entry per request by construction.
The tail's middle stage starts from the carrier key generation left behind and its other two
stages are not serving phases at all.

**The shape of the argument is forced by where the recording can grow.**
`HandlerCarrier.FilesLeft` compares an input against the framing in flight, so with nothing in
flight it is false, the notice is the identity, the left test never fires, and the disclosing
recording cannot grow. `CarrierClearFraming` says every stage of the tail is entered and left
with nothing in flight. So key generation and verification contribute nothing to the recording,
and the whole of it is the adversary's phase's.

Two invariants do the work:

* `Quiet` — nothing in flight and nothing served — is a `ServedAgreement.Files.invariant`, since
  the filing clause is discharged by the framing being clear rather than by anything about the
  carrier's history. It is what makes the middle stage's start as good as an empty carrier for
  the agreement, even though its cache is not empty.
* `leftFixed_step` is the same observation at the recording instead of the carrier, and it
  needs a step law rather than a carrier invariant because the recording lives beside the
  carrier and `Files.invariant` does not see it.

The length of the signing log is a budget fact and is taken as a hypothesis; nothing in this
file bounds the adversary's signing queries.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierCap

variable {α : Type}

open Security BracketedRun CarrierFiles CarrierTail PhaseFusion RecordInvariant
open RecordedQueries RecorderView CarriedWitness HandlerCarrier

/-! ## Nothing in flight, nothing served -/

/-- The carrier invariant the middle stage is entered with. -/
def Quiet (carrier : HandlerCarrier.State) : Prop :=
  carrier.framing = none ∧ carrier.served = 0

theorem quiet_startAt (cache : QueryCache HashSpec) : Quiet (startAt cache) := ⟨rfl, rfl⟩

theorem quiet_cacheAnswer (carrier : HandlerCarrier.State) (input : Bytes)
    (answer : HashOutput) (hquiet : Quiet carrier) :
    Quiet (HandlerCarrier.cacheAnswer carrier input answer) :=
  ⟨by rw [HandlerCarrier.framing_cacheAnswer]; exact hquiet.1,
    by rw [HandlerCarrier.served_cacheAnswer]; exact hquiet.2⟩

/-- **A run under the tail's handler keeps it.** The filing clause of `Files.invariant` is
vacuous: with nothing in flight there is nothing `HandlerCarrier.FilesLeft` can match. -/
theorem quiet_run (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α) (state : CountedState)
    (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hquiet : Quiet state.1) : Quiet result.2.1 :=
  (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)).invariant Quiet
    quiet_cacheAnswer
    (fun carrier input hinv hfiles =>
      absurd hfiles (HandlerCarrier.not_filesLeft_of_clear (keyAt walk) carrier hinv.1 input))
    computation state result hresult hquiet

/-! ## And so the disclosing recording cannot grow

The carrier invariant is not enough on its own: `Files.invariant` quantifies over the carrier
and the recording rides beside it. What the recording needs is the step equation, and at a clear
view all three of its branches leave the left component alone. -/

open scoped Classical in
/-- **The left component of an append is untouched when the left test fails.** -/
theorem left_appendedOf_of_not_left {σ : Type} [CacheView σ]
    (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes) (state : StateOf σ)
    (answer : HashOutput) (hleft : ¬ leftKeep input state.1) :
    (appendedOf leftKeep rightKeep input state answer).1 = state.2.1 := by
  classical
  rw [appendedOf, if_neg (fun hboth => hleft hboth.2)]
  split_ifs <;> rfl

open scoped Classical in
/-- **A step at a view with nothing in flight leaves the disclosing recording where it was.** -/
theorem leftFixed_step (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support (((handlerAt rightKeep walk) queried).run state))
    (hclear : state.1.framing = none) : step.2.2.1.1 = state.2.1.1 := by
  classical
  obtain ⟨inner, hinner, _, _, hrecord⟩ :=
    CountedHandler.withCount_step
      (@noticingRecorderOf HandlerCarrier.State (servingView (keyAt walk))
        (disclosingKeep (keyAt walk)) (rightKeep walk)) queried state step hstep
  rw [hrecord]
  rcases queried with coin | input
  · rw [@noticingRecorderOf_run_inl HandlerCarrier.State (servingView (keyAt walk))
        (disclosingKeep (keyAt walk)) (rightKeep walk) coin (state.1, state.2.1),
      @recorderOf_run_inl HandlerCarrier.State (servingView (keyAt walk))
        (disclosingKeep (keyAt walk)) (rightKeep walk) coin (state.1, state.2.1),
      mem_support_bind_iff] at hinner
    obtain ⟨value, _, hpure⟩ := hinner
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
  · have hnotice :
        @CacheView.onQuery HandlerCarrier.State (servingView (keyAt walk)) state.1 input =
          state.1 := by
      show servingNotice (keyAt walk) state.1 input = state.1
      rw [servingNotice,
        if_neg (HandlerCarrier.not_filesLeft_of_clear (keyAt walk) state.1 hclear input)]
    set view : StateOf HandlerCarrier.State :=
      (@CacheView.onQuery HandlerCarrier.State (servingView (keyAt walk))
        (state.1, state.2.1).1 input, (state.1, state.2.1).2) with hview
    have hleft : ¬ disclosingKeep (keyAt walk) input view.1 := by
      rw [hview]
      show ¬ disclosingKeep (keyAt walk) input
        (@CacheView.onQuery HandlerCarrier.State (servingView (keyAt walk)) state.1 input)
      rw [hnotice]
      exact HandlerCarrier.not_filesLeft_of_clear (keyAt walk) state.1 hclear input
    rw [@noticingRecorderOf_run_inr HandlerCarrier.State (servingView (keyAt walk))
      (disclosingKeep (keyAt walk)) (rightKeep walk) input (state.1, state.2.1)] at hinner
    have hsame : view.2.1 = state.2.1.1 := by rw [hview]
    rcases hcached :
        @CacheView.cacheOf HandlerCarrier.State (servingView (keyAt walk)) view.1 input with
      _ | cached
    · rw [@recorderOf_run_inr_none HandlerCarrier.State (servingView (keyAt walk))
          (disclosingKeep (keyAt walk)) (rightKeep walk) input view hcached,
        support_map] at hinner
      obtain ⟨answer, _, hvalue'⟩ := hinner
      rw [← hvalue', ← hsame]
      exact left_appendedOf_of_not_left _ _ input view answer hleft
    · rw [@recorderOf_run_inr_some HandlerCarrier.State (servingView (keyAt walk))
          (disclosingKeep (keyAt walk)) (rightKeep walk) input view cached hcached,
        support_pure, Set.mem_singleton_iff] at hinner
      rw [hinner, ← hsame]
      exact left_appendedOf_of_not_left _ _ input view cached hleft

/-! ## The disclosing recording's shape, one step at a time

`CarrierRecordings.step_right_shape` reads a step at the target recording; this reads the same
step at the disclosing one. The mirror is exact and the asymmetry of `appendedOf` — the left
test is tried first — makes the left case the shorter of the two. -/

open scoped Classical in
/-- **The disclosing recording after an append**: unchanged, or this query's own entry added,
and in the second case the query was fresh and the left test held. -/
theorem appendedOf_left_shape {σ : Type} [CacheView σ] (leftKeep rightKeep : Bytes → σ → Prop)
    (input : Bytes) (state : StateOf σ) (answer : HashOutput) :
    (appendedOf leftKeep rightKeep input state answer).1 = state.2.1 ∨
      ((appendedOf leftKeep rightKeep input state answer).1 = state.2.1 ++ [(input, answer)] ∧
        CacheView.cacheOf state.1 input = none ∧ leftKeep input state.1) := by
  classical
  cases hcached : CacheView.cacheOf state.1 input with
  | some cached =>
    exact Or.inl (by rw [appendedOf_of_cached leftKeep rightKeep input state answer cached
      hcached])
  | none =>
    by_cases hleft : leftKeep input state.1
    · exact Or.inr ⟨by rw [appendedOf_of_left leftKeep rightKeep input state answer hcached
        hleft], rfl, hleft⟩
    · exact Or.inl (left_appendedOf_of_not_left leftKeep rightKeep input state answer hleft)

open scoped Classical in
/-- **The disclosing recording after a step of the tail's handler.** -/
theorem step_left_shape (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support (((handlerAt rightKeep walk) queried).run state)) :
    step.2.2.1.1 = state.2.1.1 ∨
      ∃ (input : Bytes) (answer : HashOutput), queried = Sum.inr input ∧
        step.2.2.1.1 = state.2.1.1 ++ [(input, answer)] ∧
          state.1.cache input = none ∧
            disclosingKeep (keyAt walk) input (servingNotice (keyAt walk) state.1 input) ∧
              step.2.1.cache input = some answer := by
  classical
  obtain ⟨inner, hinner, hvalue, -, hcarried⟩ :=
    CountedHandler.withCount_step
      (@noticingRecorderOf HandlerCarrier.State (servingView (keyAt walk))
        (disclosingKeep (keyAt walk)) (rightKeep walk)) queried state step hstep
  rcases queried with coin | input
  · refine Or.inl ?_
    rw [hcarried, show inner.2.2 = (state.1, state.2.1).2 from
      congrArg Prod.snd (@recorderOf_step_inl HandlerCarrier.State (servingView (keyAt walk))
        (disclosingKeep (keyAt walk)) (rightKeep walk) coin (state.1, state.2.1) inner
        (by rw [← @noticingRecorderOf_run_inl HandlerCarrier.State
          (servingView (keyAt walk))]; exact hinner))]
  · have hinr := hinner
    rw [@noticingRecorderOf_run_inr HandlerCarrier.State (servingView (keyAt walk))
      (disclosingKeep (keyAt walk)) (rightKeep walk) input (state.1, state.2.1)] at hinr
    rw [hcarried, @recorderOf_step_record HandlerCarrier.State (servingView (keyAt walk))
      (disclosingKeep (keyAt walk)) (rightKeep walk) input _ inner hinr]
    rcases @appendedOf_left_shape HandlerCarrier.State (servingView (keyAt walk))
      (disclosingKeep (keyAt walk)) (rightKeep walk) input _ inner.1 with
      hsame | ⟨hshape, hfresh, hleft⟩
    · exact Or.inl hsame
    · refine Or.inr ⟨input, inner.1, rfl, hshape, ?_, hleft, ?_⟩
      · show HandlerCarrier.cacheOf state.1 input = none
        rw [← cacheOf_servingNotice (keyAt walk) state.1 input]
        exact hfresh
      · rw [← hvalue]
        exact (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)).hashCached input
          state step hstep

/-! ## Cached, once each, and served

Three invariants over the same recording, each the mirror of a target-side one. The brackets
keep all three for the same reason they keep everything else: they write the framing and return
the rest of the state untouched. -/

/-- Every disclosing-recorded input is cached. -/
def LeftCached (state : CountedState) : Prop :=
  ∀ entry ∈ state.2.1.1, state.1.cache entry.1 ≠ none

/-- And the recording holds each input once. -/
def LeftFreshNodup (state : CountedState) : Prop :=
  LeftCached state ∧ (state.2.1.1.map Prod.fst).Nodup

/-- Every disclosing-recorded input was served. -/
def LeftServed (state : CountedState) : Prop :=
  ∀ entry ∈ state.2.1.1, HandlerCarrier.Served state.1 entry.1

theorem leftFreshNodup_startAt (cache : QueryCache HashSpec) :
    LeftFreshNodup (startAt cache, (([], []), 0)) :=
  ⟨fun entry hentry => absurd hentry (by simp), by simp⟩

theorem leftServed_startAt (cache : QueryCache HashSpec) :
    LeftServed (startAt cache, (([], []), 0)) := fun entry hentry => absurd hentry (by simp)

theorem leftFreshNodup_bracket {f : CountedState → CountedState} (hf : Bracket f)
    (state : CountedState) (hinv : LeftFreshNodup state) : LeftFreshNodup (f state) := by
  refine ⟨fun entry hentry => ?_, ?_⟩
  · rw [(hf state).1]
    exact hinv.1 entry (by rw [← (hf state).2]; exact hentry)
  · rw [(hf state).2]
    exact hinv.2

open scoped Classical in
theorem step_leftCached (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support (((handlerAt rightKeep walk) queried).run state))
    (hinv : LeftCached state) : LeftCached step.2 := by
  classical
  have hgrows := (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)).stepGrows queried
    state step hstep
  rcases step_left_shape rightKeep walk queried state step hstep with
    hsame | ⟨input, answer, -, hshape, -, -, hcached⟩
  · intro entry hentry
    rw [hsame] at hentry
    rcases Option.ne_none_iff_exists'.mp (hinv entry hentry) with ⟨value, hvalue⟩
    rw [hgrows.1 entry.1 value hvalue]
    exact Option.some_ne_none value
  · intro entry hentry
    rw [hshape, List.mem_append] at hentry
    rcases hentry with hprior | hself
    · rcases Option.ne_none_iff_exists'.mp (hinv entry hprior) with ⟨value, hvalue⟩
      rw [hgrows.1 entry.1 value hvalue]
      exact Option.some_ne_none value
    · rw [List.mem_singleton.mp hself]
      show step.2.1.cache input ≠ none
      rw [hcached]
      exact Option.some_ne_none answer

open scoped Classical in
theorem step_leftFreshNodup (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support (((handlerAt rightKeep walk) queried).run state))
    (hinv : LeftFreshNodup state) : LeftFreshNodup step.2 := by
  classical
  refine ⟨step_leftCached rightKeep walk queried state step hstep hinv.1, ?_⟩
  rcases step_left_shape rightKeep walk queried state step hstep with
    hsame | ⟨input, answer, -, hshape, hfresh, -, -⟩
  · rw [hsame]
    exact hinv.2
  · rw [hshape, List.map_append]
    refine List.Nodup.append hinv.2 (by simp) ?_
    intro probe hprobe hself
    rw [List.mem_singleton.mp hself] at hprobe
    obtain ⟨entry, hentry, hinput⟩ := List.mem_map.mp hprobe
    exact hinv.1 entry hentry (by rw [hinput]; exact hfresh)

open scoped Classical in
/-- **Servedness is the recorder's own law**, and a step is a run of one query. -/
theorem step_leftServed (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support (((handlerAt rightKeep walk) queried).run state))
    (hinv : LeftServed state) : LeftServed step.2 := by
  classical
  obtain ⟨inner, hinner, -, hcarrier, hcarried⟩ :=
    CountedHandler.withCount_step
      (@noticingRecorderOf HandlerCarrier.State (servingView (keyAt walk))
        (disclosingKeep (keyAt walk)) (rightKeep walk)) queried state step hstep
  have hrun : inner ∈ support ((simulateQ
      (@noticingRecorderOf HandlerCarrier.State (servingView (keyAt walk))
        (disclosingKeep (keyAt walk)) (rightKeep walk))
      (liftM (OracleWorld.query queried) :
        OracleComp OracleWorld (OracleWorld.Range queried))).run (state.1, state.2.1)) := by
    rwa [show simulateQ (@noticingRecorderOf HandlerCarrier.State (servingView (keyAt walk))
      (disclosingKeep (keyAt walk)) (rightKeep walk))
        (liftM (OracleWorld.query queried) :
          OracleComp OracleWorld (OracleWorld.Range queried)) =
      (@noticingRecorderOf HandlerCarrier.State (servingView (keyAt walk))
        (disclosingKeep (keyAt walk)) (rightKeep walk)) queried from by simp]
  have hserved := mem_served_of_mem_leftRecord (keyAt walk) (rightKeep walk) _
    (state.1, state.2.1) inner hrun hinv
  intro entry hentry
  rw [hcarrier]
  exact hserved entry (by rw [← hcarried]; exact hentry)

theorem leftServed_bracket {f : CountedState → CountedState} (hf : Bracket f)
    (hframing : ∀ state : CountedState, (f state).1.served = state.1.served)
    (state : CountedState) (hinv : LeftServed state) : LeftServed (f state) := by
  intro entry hentry
  show entry.1 ∈ (f state).1.served
  rw [hframing state]
  exact hinv entry (by rw [← (hf state).2]; exact hentry)

theorem served_startServingOn (request : Message) (state : CountedState) :
    (ServedAgreement.startServingOn request state).1.served = state.1.served := by
  rw [ServedAgreement.startServingOn]
  cases request.frame with
  | none => rfl
  | some framed => rfl

theorem served_stopServingOn (state : CountedState) :
    (ServedAgreement.stopServingOn state).1.served = state.1.served := rfl

/-! ## The agreement, from a carrier that is quiet rather than empty

The agreement is read at the tail's middle stage, which starts from the carrier key generation
left behind, whose cache is not empty. Nothing in the argument wants an empty *cache*; it wants
an empty **served set**, which is what makes `ServedAgreement.CarrierLogged` hold at the start
for the only reason it ever holds there: there is nothing served to be logged.

`ServedAgreement.carrierLogged_run_with` and `logFiled_run_with` are general in the starting
state, so this is their composition at a quiet start. -/

theorem carrierLogged_of_quiet (sk : SecretKey) (warm : QueryCache HashSpec)
    (log : SigningLog) (carrier : HandlerCarrier.State) (hquiet : Quiet carrier) :
    ServedAgreement.CarrierLogged sk warm log carrier := by
  intro _ _ _ input hserved
  exact absurd (show input ∈ carrier.served from hserved)
    (by rw [hquiet.2]; simp)

set_option maxHeartbeats 1000000 in
/-- **The agreement at the tail's middle stage.** -/
theorem agreesWithLog_quiet (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) (sk : SecretKey) (hpk : sk.publicKey = keyAt walk)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (carrier : CountedState) (hquiet : Quiet carrier.1)
    (z : α × (Multiplicative Tally × SigningLog × CountedState))
    (hz : z ∈ support ((simulateQ (ServedAgreement.servingPhaseWith
      (handlerAt rightKeep walk) (Scheme.sign sk)) computation).run
        (accumulated, [], carrier))) :
    ServingCarrier.AgreesWithLog sk z.2.2.1 z.2.2.2.1 := by
  intro input
  constructor
  · exact ServedAgreement.carrierLogged_run_with (keyAt walk) (handlerAt rightKeep walk)
      (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)) (Scheme.sign sk) sk hpk
      (ServedAgreement.signerShape_sign sk) ∅
      (ServedAgreement.signerPins_sign sk hpublic) computation (accumulated, [], carrier)
      hquiet.1 (carrierLogged_of_quiet sk ∅ [] carrier.1 hquiet) z hz
      z.2.2.2.1.cache (fun _ _ hvalue => hvalue)
      (fun _ _ hvalue => absurd hvalue (by simp)) input
  · exact ServedAgreement.logServed_subset_served sk z.2.2.1 z.2.2.2.1
      (ServedAgreement.logFiled_run_with (keyAt walk) (handlerAt rightKeep walk)
        (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)) (Scheme.sign sk) sk hpk
        (ServedAgreement.signerShape_sign sk)
        (ServedAgreement.signerFaithful_sign (keyAt walk) (handlerAt rightKeep walk)
          (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)) sk)
        computation (accumulated, [], carrier) (ServedAgreement.logFiled_nil sk carrier.1) z hz)
      z.2.2.2.1.cache (fun _ _ hvalue => hvalue) input

/-! ## The cap at the tail

Three stages. Key generation leaves the carrier quiet and the recording empty, so the middle
stage is entered as good as empty; the middle stage is a serving phase, where the agreement
holds and the recording is capped; verification adds nothing to the recording, because with
nothing in flight the left test cannot fire.

**The signing log's length is not bounded here.** It is a budget fact about the adversary and it
is a hypothesis, read at the outcome the tail returns — which is where the log ends up, so a
consumer can discharge it without reaching into a stage. -/

set_option maxHeartbeats 1000000 in
/-- **The disclosing recording of the carrier tail is inside the concentration's cap.** -/
theorem leftRecord_length_le_cap_carrierTail
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (adversary : Adversary) (walk : Walk)
    (hpublic : ¬ HashSeparation.Possible ((keyAt walk).seed, (keyAt walk).root))
    (hkey : ∀ keys ∈ support ((simulateQ (handlerAt rightKeep walk)
        (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
        (startAt walk.2, (([], []), 0))),
      keys.1.1.publicKey = keyAt walk)
    (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hresult : result ∈ support (carrierTail rightKeep adversary walk))
    (hlimit : result.1.1.1.signed.length ≤ signingLimit) :
    result.2.2.1.length ≤ 5 * 2 ^ 62 := by
  classical
  rw [carrierTail, mem_support_bind_iff] at hresult
  obtain ⟨keys, hkeys, hrest1⟩ := hresult
  rw [mem_support_bind_iff] at hrest1
  obtain ⟨middle, hmiddle, hrest2⟩ := hrest1
  rw [mem_support_bind_iff] at hrest2
  obtain ⟨final, hfinal, hpure⟩ := hrest2
  rw [support_pure, Set.mem_singleton_iff] at hpure
  -- the three stage boundaries, with nothing in flight
  obtain ⟨-, hclearKeys, hclearMiddle, -⟩ :=
    CarrierClearFraming.clear_stages rightKeep adversary walk keys hkeys middle hmiddle final
      hfinal
  -- key generation leaves the carrier quiet
  have hquiet := quiet_run rightKeep walk _ _ keys hkeys (quiet_startAt walk.2)
  -- the recording is cached, nodup and served at the end of the middle stage
  have hnodupKeys := run_invariant (Inv := LeftFreshNodup) (handlerAt rightKeep walk)
    (fun queried state step hstep hinv =>
      step_leftFreshNodup rightKeep walk queried state step hstep hinv)
    _ (startAt walk.2, (([], []), 0)) keys hkeys (leftFreshNodup_startAt walk.2)
  have hnodupMiddle := phase_invariant (Inv := LeftFreshNodup) (handlerAt rightKeep walk) _
    ServedAgreement.startServingOn ServedAgreement.stopServingOn
    (fun queried state step hstep hinv =>
      step_leftFreshNodup rightKeep walk queried state step hstep hinv)
    (fun request state hinv =>
      leftFreshNodup_bracket (bracket_startServingOn request) state hinv)
    (fun state hinv => leftFreshNodup_bracket bracket_stopServingOn state hinv)
    _ (1 : Multiplicative Tally) [] keys.2 middle hmiddle hnodupKeys
  have hservedKeys := run_invariant (Inv := LeftServed) (handlerAt rightKeep walk)
    (fun queried state step hstep hinv =>
      step_leftServed rightKeep walk queried state step hstep hinv)
    _ (startAt walk.2, (([], []), 0)) keys hkeys (leftServed_startAt walk.2)
  have hservedMiddle := phase_invariant (Inv := LeftServed) (handlerAt rightKeep walk) _
    ServedAgreement.startServingOn ServedAgreement.stopServingOn
    (fun queried state step hstep hinv =>
      step_leftServed rightKeep walk queried state step hstep hinv)
    (fun request state hinv =>
      leftServed_bracket (bracket_startServingOn request) (served_startServingOn request) state
        hinv)
    (fun state hinv => leftServed_bracket bracket_stopServingOn served_stopServingOn state hinv)
    _ (1 : Multiplicative Tally) [] keys.2 middle hmiddle hservedKeys
  -- the agreement, at a carrier that is quiet rather than empty
  have hagree := agreesWithLog_quiet rightKeep walk keys.1.1
    (hkey keys hkeys) (by rw [hkey keys hkeys]; exact hpublic) (adversary.main keys.1.2)
    (1 : Multiplicative Tally) keys.2 hquiet middle hmiddle
  -- verification adds nothing to the recording
  have hverify := run_invariant (Inv := fun state : CountedState =>
      state.1.framing = none ∧ state.2.1.1 = middle.2.2.2.2.1.1)
    (handlerAt rightKeep walk)
    (fun queried state step hstep hinv =>
      ⟨by rw [CarrierClearFraming.clear_step rightKeep walk queried state step hstep hinv.1],
        by rw [leftFixed_step rightKeep walk queried state step hstep hinv.1]; exact hinv.2⟩)
    _ middle.2.2.2 final hfinal ⟨hclearMiddle, rfl⟩
  -- and so the tail's recording is the middle stage's, which the agreement caps
  have hsigned : middle.2.2.1 = result.1.1.1.signed := by rw [hpure]
  have hstate : result.2.2.1 = final.2.2.1.1 := by rw [hpure]; rfl
  rw [hstate, hverify.2]
  exact ServedAgreement.record_length_le_cap keys.1.1 middle.2.2.1 middle.2.2.2.1 hagree
    middle.2.2.2.2.1.1 hnodupMiddle.2 hservedMiddle (by rw [hsigned]; exact hlimit)

set_option maxHeartbeats 1000000 in
/-- **The cap in the form a consumer wants it**: quantified over the support of the tail. -/
theorem leftRecord_le_cap_carrierTail
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (adversary : Adversary) (walk : Walk)
    (hpublic : ¬ HashSeparation.Possible ((keyAt walk).seed, (keyAt walk).root))
    (hkey : ∀ keys ∈ support ((simulateQ (handlerAt rightKeep walk)
        (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
        (startAt walk.2, (([], []), 0))),
      keys.1.1.publicKey = keyAt walk)
    (hlimit : ∀ result ∈ support (carrierTail rightKeep adversary walk),
      result.1.1.1.signed.length ≤ signingLimit) :
    ∀ result ∈ support (carrierTail rightKeep adversary walk),
      result.2.2.1.length ≤ 5 * 2 ^ 62 :=
  fun result hresult =>
    leftRecord_length_le_cap_carrierTail rightKeep adversary walk hpublic hkey result hresult
      (hlimit result hresult)

attribute [local irreducible] WarmedGame.afterSeeds

end SlhDsaSecurity.CarrierCap
