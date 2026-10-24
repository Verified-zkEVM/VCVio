/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SplitPrefix
public import HashSig.SLHDSA.SHAKE128s.Proof.HandlerCarrier

/-!
# The recorder's state, as a parameter

`SplitPrefix.recorder` keeps two recordings beside a **cache**, and decides which recording an
answer joins by testing the input against that cache. That is exactly what the disclosing test
cannot be: an adversary that knows `SK.prf` makes any cache-readable "the signer served this"
test true with no request behind it. The test has to read the **carrier**, whose served set is
written only by the signing oracle.

So the state becomes a parameter. The recorder asks one thing of it and one thing only:

    cacheOf (update state input answer) = (cacheOf state).cacheQuery input answer

— enough to see whether a query is fresh and to install an answer, and nothing more, so that
every future instantiation pays for exactly this much. At `σ := QueryCache HashSpec` the two
fields are `id` and `cacheQuery` and `recorderOf_cache` says the generalised recorder **is**
`SplitPrefix.recorder`, so everything already proved about that one stands untouched. At
`σ := HandlerCarrier.State` they are `cacheOf` and `cacheAnswer`, and the disclosing test can be
the carrier's served set.

**The freshness rule and the served set stay different objects**, which is the thing to keep
checking. Freshness lives in `appendedOf`'s guard on `cacheOf state.1`, where it always was; the
served set lives in the carrier's own field. Instantiating the left test at the latter leaves the
former exactly where it is, so no instantiation can collapse the two even by accident.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.RecorderView

open SplitPrefix DigestTape

/-- What a recorder's state must provide, and the two laws it must satisfy.

**Filing is not installing, which is why there are two operations and not one.** `update` runs
on a miss, because that is where an answer is installed. `onQuery` runs at *every* hash query,
because what a state may want to record about a query — that the signer was serving it, say —
is true of a cache hit exactly as much as of a miss. Tying the two together would mean a state
could only ever notice the queries the run itself drew; and the failure is not a missing entry
but a silent one, because an input is installed once and is never fresh again, so a notice
missed at a hit can never be taken later.

A view that notices nothing takes `onQuery` to be the identity, so the recorder that notices is
`recorderOf` there. This is a widening: `recorderOf` below is untouched, and everything proved
about it stands.

Both laws are about the cache alone, which is what keeps `recorderOf_forget_step` true: whatever
else a view carries rides along and the forgetting never sees it. -/
class CacheView (σ : Type) where
  /-- The cache the freshness test is read against. -/
  cacheOf : σ → QueryCache HashSpec
  /-- How an answer is installed, on a miss. -/
  update : σ → Bytes → HashOutput → σ
  /-- What the state does at **every** query, hit or miss. The identity, for a view with
  nothing to notice. -/
  onQuery : σ → Bytes → σ := fun state _ => state
  /-- Installing an answer caches it, and says nothing else. -/
  cache_update : ∀ (state : σ) (input : Bytes) (answer : HashOutput),
    cacheOf (update state input answer) = (cacheOf state).cacheQuery input answer
  /-- Noticing a query does not touch the cache. -/
  cache_onQuery : ∀ (state : σ) (input : Bytes),
    cacheOf (onQuery state input) = cacheOf state := by intros; rfl

/-- The cache is its own view, and notices nothing. -/
instance : CacheView (QueryCache HashSpec) where
  cacheOf := id
  update := fun cache input answer => cache.cacheQuery input answer
  cache_update := fun _ _ _ => rfl

/-- And so is the handler's carrier, at the operations it already has. A view that *does*
notice its queries is `CarriedWitness.servingView`; this one carries the carrier along. -/
instance : CacheView HandlerCarrier.State where
  cacheOf := HandlerCarrier.cacheOf
  update := HandlerCarrier.cacheAnswer
  cache_update := fun _ _ _ => rfl

variable {σ : Type} [CacheView σ]

/-- Noticing a query leaves the view's cache unchanged. -/
theorem cacheOf_onQuery (state : σ) (input : Bytes) :
    CacheView.cacheOf (CacheView.onQuery state input) = CacheView.cacheOf state :=
  CacheView.cache_onQuery state input

/-- The state at a general view: the carrier and the two recordings. -/
abbrev StateOf (σ : Type) := σ × Record × Record

open scoped Classical in
/-- What the two recordings become when a query is answered. The guard is freshness, read at
the view's cache, exactly as `SplitPrefix.appended` reads it at the cache itself. -/
@[expose] noncomputable def appendedOf (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput) : Record × Record :=
  if CacheView.cacheOf state.1 input = none ∧ leftKeep input state.1 then
    (state.2.1 ++ [(input, answer)], state.2.2)
  else if CacheView.cacheOf state.1 input = none ∧ rightKeep input state.1 then
    (state.2.1, state.2.2 ++ [(input, answer)])
  else state.2

/-- A step only extends the disclosing recording: the old one is a prefix of the new. -/
theorem left_prefix_appendedOf (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput) :
    state.2.1 <+: (appendedOf leftKeep rightKeep input state answer).1 := by
  classical
  rw [appendedOf]
  split
  · exact List.prefix_append _ _
  · split
    · exact List.prefix_rfl
    · exact List.prefix_rfl

/-- A step only extends the target recording: the old one is a prefix of the new. -/
theorem right_prefix_appendedOf (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput) :
    state.2.2 <+: (appendedOf leftKeep rightKeep input state answer).2 := by
  classical
  rw [appendedOf]
  split
  · exact List.prefix_rfl
  · split
    · exact List.prefix_append _ _
    · exact List.prefix_rfl

/-! ### Reading the two tests -/

open scoped Classical in
/-- A cached query leaves both recordings unchanged. -/
theorem appendedOf_of_cached (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer cached : HashOutput)
    (hcached : CacheView.cacheOf state.1 input = some cached) :
    appendedOf leftKeep rightKeep input state answer = state.2 := by
  classical
  rw [appendedOf, ite_eq_right (by rw [hcached]; simp), ite_eq_right (by rw [hcached]; simp)]

open scoped Classical in
/-- A fresh query passing the left test is appended to the disclosing recording. -/
theorem appendedOf_of_left (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput)
    (hfresh : CacheView.cacheOf state.1 input = none) (hleft : leftKeep input state.1) :
    appendedOf leftKeep rightKeep input state answer =
      (state.2.1 ++ [(input, answer)], state.2.2) := by
  classical
  rw [appendedOf, ite_eq_left ⟨hfresh, hleft⟩]

open scoped Classical in
/-- A fresh query failing the left test and passing the right one is appended to the target
recording. -/
theorem appendedOf_of_right (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput)
    (hfresh : CacheView.cacheOf state.1 input = none) (hleft : ¬ leftKeep input state.1)
    (hright : rightKeep input state.1) :
    appendedOf leftKeep rightKeep input state answer =
      (state.2.1, state.2.2 ++ [(input, answer)]) := by
  classical
  rw [appendedOf, ite_eq_right (fun hboth => hleft hboth.2), ite_eq_left ⟨hfresh, hright⟩]

open scoped Classical in
/-- A query passing neither test leaves both recordings unchanged. -/
theorem appendedOf_of_neither (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput) (hleft : ¬ leftKeep input state.1)
    (hright : ¬ rightKeep input state.1) :
    appendedOf leftKeep rightKeep input state answer = state.2 := by
  classical
  rw [appendedOf, ite_eq_right (fun hboth => hleft hboth.2),
    ite_eq_right (fun hboth => hright hboth.2)]

open scoped Classical in
/-- **The target recording after a step, as a list**: unchanged, or this query's own entry
appended — and in the second case the query was fresh and the right test held. The four
`appendedOf` cases in one place rather than four.

Stated at the list and not at membership, because an invariant about *order or multiplicity* —
that the recording holds each input once, say — cannot be had from membership, and the proof
knows the list. -/
theorem appendedOf_right_shape (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput) :
    (appendedOf leftKeep rightKeep input state answer).2 = state.2.2 ∨
      ((appendedOf leftKeep rightKeep input state answer).2 = state.2.2 ++ [(input, answer)] ∧
        CacheView.cacheOf state.1 input = none ∧ rightKeep input state.1) := by
  classical
  cases hcached : CacheView.cacheOf state.1 input with
  | some cached =>
    refine Or.inl ?_
    rw [appendedOf_of_cached leftKeep rightKeep input state answer cached hcached]
  | none =>
    by_cases hleft : leftKeep input state.1
    · refine Or.inl ?_
      rw [appendedOf_of_left leftKeep rightKeep input state answer hcached hleft]
    · by_cases hright : rightKeep input state.1
      · refine Or.inr ⟨?_, rfl, hright⟩
        rw [appendedOf_of_right leftKeep rightKeep input state answer hcached hleft hright]
      · refine Or.inl ?_
        rw [appendedOf_of_neither leftKeep rightKeep input state answer hleft hright]

open scoped Classical in
/-- **An entry of the disclosing recording after a step is one that was there, or this step's
own**, filed fresh and on the left test. The mirror of `appendedOf_right_mem`. -/
theorem appendedOf_left_mem (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput) (entry : Bytes × HashOutput)
    (hentry : entry ∈ (appendedOf leftKeep rightKeep input state answer).1) :
    entry ∈ state.2.1 ∨ (entry = (input, answer) ∧
      CacheView.cacheOf state.1 input = none ∧ leftKeep input state.1) := by
  classical
  rw [appendedOf] at hentry
  split_ifs at hentry with hleft hright
  · rcases List.mem_append.mp hentry with hprior | hself
    · exact Or.inl hprior
    · exact Or.inr ⟨List.mem_singleton.mp hself, hleft.1, hleft.2⟩
  · exact Or.inl hentry
  · exact Or.inl hentry

open scoped Classical in
/-- **A step appends at most this query's own entry to the target recording**, and when it does,
the query was fresh and the right test held. The membership reading of the shape above. -/
theorem appendedOf_right_mem (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput) (entry : Bytes × HashOutput)
    (hentry : entry ∈ (appendedOf leftKeep rightKeep input state answer).2) :
    entry ∈ state.2.2 ∨ (entry = (input, answer) ∧
      CacheView.cacheOf state.1 input = none ∧ rightKeep input state.1) := by
  classical
  rcases appendedOf_right_shape leftKeep rightKeep input state answer with
    hsame | ⟨hshape, hfresh, hright⟩
  · rw [hsame] at hentry
    exact Or.inl hentry
  · rw [hshape] at hentry
    rcases List.mem_append.mp hentry with hprior | hself
    · exact Or.inl hprior
    · exact Or.inr ⟨List.mem_singleton.mp hself, hfresh, hright⟩

open scoped Classical in
/-- **The recorder at a general view.** See `noticingRecorderOf` for the widening that tells the
view about *every* query rather than only the ones it drew; a view with something to record
about a cache hit needs that one, and at a view that notices nothing the two are the same query
implementation.

The two branches are the shared oracle's own — a hit
returns the cached answer and leaves the state, a miss draws and installs — so at the cache this
is `SplitPrefix.recorder` and not merely something with its law. -/
@[expose] noncomputable def recorderOf (leftKeep rightKeep : Bytes → σ → Prop) :
    QueryImpl OracleWorld (StateT (StateOf σ) ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input =>
        match CacheView.cacheOf state.1 input with
        | some cached =>
            (pure (cached, (state.1, appendedOf leftKeep rightKeep input state cached)) :
              ProbComp _)
        | none =>
            (fun answer => (answer,
              (CacheView.update state.1 input answer,
                appendedOf leftKeep rightKeep input state answer))) <$>
              ($ᵗ HashOutput : ProbComp _)

open scoped Classical in
/-- A coin query draws a uniform value and leaves the state unchanged. -/
theorem recorderOf_run_inl (leftKeep rightKeep : Bytes → σ → Prop) (coin : unifSpec.Domain)
    (state : StateOf σ) :
    ((recorderOf leftKeep rightKeep) (Sum.inl coin)).run state =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, state) : ProbComp _) := rfl

open scoped Classical in
/-- A cached hash query returns the cached answer and updates only the recordings. -/
theorem recorderOf_run_inr_some (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (cached : HashOutput)
    (hcached : CacheView.cacheOf state.1 input = some cached) :
    ((recorderOf leftKeep rightKeep) (Sum.inr input)).run state =
      (pure (cached, (state.1, appendedOf leftKeep rightKeep input state cached)) :
        ProbComp (OracleWorld.Range (Sum.inr input) × StateOf σ)) := by
  classical
  change (match CacheView.cacheOf state.1 input with
    | some cached => (pure (cached, (state.1, appendedOf leftKeep rightKeep input state cached)) :
        ProbComp _)
    | none => _) = _
  rw [hcached]

open scoped Classical in
/-- A fresh hash query draws an answer, installs it, and updates the recordings. -/
theorem recorderOf_run_inr_none (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (hfresh : CacheView.cacheOf state.1 input = none) :
    ((recorderOf leftKeep rightKeep) (Sum.inr input)).run state =
      (((fun answer => (answer,
        (CacheView.update state.1 input answer,
          appendedOf leftKeep rightKeep input state answer))) <$>
        ($ᵗ HashOutput : ProbComp _)) :
          ProbComp (OracleWorld.Range (Sum.inr input) × StateOf σ)) := by
  classical
  change (match CacheView.cacheOf state.1 input with
    | some cached => (pure (cached, (state.1, appendedOf leftKeep rightKeep input state cached)) :
        ProbComp _)
    | none => _) = _
  rw [hfresh]

/-! ## At the cache, it is the recorder `SplitPrefix` already has

So nothing proved there has to move, and the generalisation is a widening rather than a
replacement. -/

open scoped Classical in
/-- At the cache itself, `appendedOf` is `SplitPrefix.appended`. -/
theorem appendedOf_cache (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) (answer : HashOutput) :
    appendedOf leftKeep rightKeep input state answer =
      appended leftKeep rightKeep input state answer := rfl

open scoped Classical in
/-- **The generalised recorder at the cache is `SplitPrefix.recorder`.** -/
theorem recorderOf_cache (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) :
    recorderOf leftKeep rightKeep = recorder leftKeep rightKeep := by
  classical
  funext queried state
  rcases queried with coin | input
  · rfl
  · change ((recorderOf leftKeep rightKeep) (Sum.inr input)).run state =
      ((recorder leftKeep rightKeep) (Sum.inr input)).run state
    rw [SplitPrefix.recorder_run_inr]
    cases hcached : state.1 input with
    | some cached =>
      rw [recorderOf_run_inr_some leftKeep rightKeep input state cached hcached,
        QueryImpl.withCaching_run_some _ hcached, pure_bind]
      rfl
    | none =>
      rw [recorderOf_run_inr_none leftKeep rightKeep input state hcached,
        QueryImpl.withCaching_run_none _ hcached]
      simp only [uniformSampleImpl, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_def]
      rfl

/-! ## What the law buys

The law is read in exactly two ways, and every proof below goes through those two readings
rather than through `CacheView.update` itself. That is the point of keeping the law single: a
second one would have to be paid for here and again at every instantiation. -/

/-- After installing an answer, the view's cache holds it at that input. -/
theorem cacheOf_update_self (state : σ) (input : Bytes) (answer : HashOutput) :
    CacheView.cacheOf (CacheView.update state input answer) input = some answer := by
  rw [CacheView.cache_update, QueryCache.cacheQuery_self]

/-- Installing an answer leaves the view's cache unchanged at every other input. -/
theorem cacheOf_update_of_ne (state : σ) (input probe : Bytes) (answer : HashOutput)
    (hne : probe ≠ input) :
    CacheView.cacheOf (CacheView.update state input answer) probe =
      CacheView.cacheOf state probe := by
  rw [CacheView.cache_update, QueryCache.cacheQuery_of_ne _ _ hne]

/-! ## One step, read several ways

Below this point nothing mentions `CacheView.update` again. A hash query does one of two things
to the state, and these lemmas are everything the inductions need to know about which. -/

open scoped Classical in
/-- **A private sample leaves the state alone.** -/
theorem recorderOf_step_inl (leftKeep rightKeep : Bytes → σ → Prop) (coin : unifSpec.Domain)
    (state : StateOf σ) (step : OracleWorld.Range (Sum.inl coin) × StateOf σ)
    (hstep : step ∈ support (((recorderOf leftKeep rightKeep) (Sum.inl coin)).run state)) :
    step.2 = state := by
  rw [recorderOf_run_inl, mem_support_bind_iff] at hstep
  obtain ⟨value, -, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  exact congrArg Prod.snd hpure

open scoped Classical in
/-- **The two shapes a hash query's step can have.** Either the input was cached, and the state
is untouched; or it was fresh, and the answer is installed. Either way the recordings take that
answer's appending. Because `recorderOf` is written as the shared oracle's own two cases, this
is the whole of a step, and the three readings that follow are its consequences. -/
theorem recorderOf_step (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (step : OracleWorld.Range (Sum.inr input) × StateOf σ)
    (hstep : step ∈ support (((recorderOf leftKeep rightKeep) (Sum.inr input)).run state)) :
    (CacheView.cacheOf state.1 input = some step.1 ∧
        step.2 = (state.1, appendedOf leftKeep rightKeep input state step.1)) ∨
      (CacheView.cacheOf state.1 input = none ∧
        step.2 = (CacheView.update state.1 input step.1,
          appendedOf leftKeep rightKeep input state step.1)) := by
  classical
  cases hcached : CacheView.cacheOf state.1 input with
  | some cached =>
    rw [recorderOf_run_inr_some leftKeep rightKeep input state cached hcached, support_pure,
      Set.mem_singleton_iff] at hstep
    subst hstep
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    rw [recorderOf_run_inr_none leftKeep rightKeep input state hcached, support_map] at hstep
    obtain ⟨answer, -, hpair⟩ := hstep
    subst hpair
    exact Or.inr ⟨rfl, rfl⟩

open scoped Classical in
/-- **A step appends exactly what `appendedOf` says.** -/
theorem recorderOf_step_record (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (step : OracleWorld.Range (Sum.inr input) × StateOf σ)
    (hstep : step ∈ support (((recorderOf leftKeep rightKeep) (Sum.inr input)).run state)) :
    step.2.2 = appendedOf leftKeep rightKeep input state step.1 := by
  rcases recorderOf_step leftKeep rightKeep input state step hstep with
    ⟨-, hshape⟩ | ⟨-, hshape⟩ <;> rw [hshape]

open scoped Classical in
/-- **After its own query the answer is in the cache**, whichever branch the step took: a hit
reads the entry that was already there, a miss installs one. -/
theorem recorderOf_step_cache_self (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (step : OracleWorld.Range (Sum.inr input) × StateOf σ)
    (hstep : step ∈ support (((recorderOf leftKeep rightKeep) (Sum.inr input)).run state)) :
    CacheView.cacheOf step.2.1 input = some step.1 := by
  rcases recorderOf_step leftKeep rightKeep input state step hstep with
    ⟨hcached, hshape⟩ | ⟨-, hshape⟩
  · rw [show step.2.1 = state.1 from by rw [hshape]]
    exact hcached
  · rw [show step.2.1 = CacheView.update state.1 input step.1 from by rw [hshape]]
    exact cacheOf_update_self state.1 input step.1

open scoped Classical in
/-- **A step never loses an entry.** -/
theorem recorderOf_step_persists (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (step : OracleWorld.Range (Sum.inr input) × StateOf σ)
    (hstep : step ∈ support (((recorderOf leftKeep rightKeep) (Sum.inr input)).run state))
    (probe : Bytes) (value : HashOutput) (hentry : CacheView.cacheOf state.1 probe = some value) :
    CacheView.cacheOf step.2.1 probe = some value := by
  classical
  rcases recorderOf_step leftKeep rightKeep input state step hstep with
    ⟨-, hshape⟩ | ⟨hfresh, hshape⟩
  · rw [show step.2.1 = state.1 from by rw [hshape]]
    exact hentry
  · rw [show step.2.1 = CacheView.update state.1 input step.1 from by rw [hshape]]
    have hne : probe ≠ input := by
      intro hsame
      rw [hsame, hfresh] at hentry
      simp at hentry
    rw [cacheOf_update_of_ne state.1 input probe step.1 hne]
    exact hentry

/-! ## Recordings only grow over a whole run

This is `SplitPrefix`'s prefix fact with the cache replaced by the view. -/

open scoped Classical in
/-- **Both recordings only grow.** -/
theorem recordOf_prefix {α : Type} (leftKeep rightKeep : Bytes → σ → Prop)
    (computation : OracleComp OracleWorld α) (state : StateOf σ) (result : α × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf leftKeep rightKeep) computation).run state)) :
    state.2.1 <+: result.2.2.1 ∧ state.2.2 <+: result.2.2.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    obtain ⟨hleft, hright⟩ := ih step.1 step.2 result hrest
    have hstepPrefix : state.2.1 <+: step.2.2.1 ∧ state.2.2 <+: step.2.2.2 := by
      rcases queried with coin | input
      · rw [recorderOf_step_inl leftKeep rightKeep coin state step hstep]
        exact ⟨List.prefix_rfl, List.prefix_rfl⟩
      · rw [recorderOf_step_record leftKeep rightKeep input state step hstep]
        exact ⟨left_prefix_appendedOf leftKeep rightKeep input state step.1,
          right_prefix_appendedOf leftKeep rightKeep input state step.1⟩
    exact ⟨hstepPrefix.1.trans hleft, hstepPrefix.2.trans hright⟩

/-! ## The instrumentation is invisible, at any view

`recorderOf_forget_step` is the one place where the single law does the whole of the work: the
cached branch leaves the view alone and the fresh branch installs, and the law says installing is
what the shared oracle's own caching does. Anything else the view carries (a served set, a flag)
is dropped by the forgetting and never seen. -/

open scoped Classical in
/-- **One step of the recorder, with the recordings dropped, is one step of the shared
oracle.** The single law is the whole of it: a hit leaves the view alone, a miss installs, and
installing is by definition what the shared oracle's caching does. Whatever else the view
carries — a served set, a flag — is dropped here and never seen again. -/
theorem recorderOf_forget_step (leftKeep rightKeep : Bytes → σ → Prop)
    (queried : OracleWorld.Domain) (state : StateOf σ) :
    (fun z : OracleWorld.Range queried × StateOf σ => (z.1, CacheView.cacheOf z.2.1)) <$>
        ((recorderOf leftKeep rightKeep) queried).run state =
      (KeygenUniform.rom queried).run (CacheView.cacheOf state.1) := by
  classical
  rcases queried with coin | input
  · rw [recorderOf_run_inl, DigestTape.rom_run_inl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  · rw [DigestTape.rom_run_inr]
    cases hcached : CacheView.cacheOf state.1 input with
    | some cached =>
      rw [recorderOf_run_inr_some leftKeep rightKeep input state cached hcached,
        QueryImpl.withCaching_run_some _ hcached, map_pure]
    | none =>
      rw [recorderOf_run_inr_none leftKeep rightKeep input state hcached,
        QueryImpl.withCaching_run_none _ hcached]
      simp only [uniformSampleImpl, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_def, CacheView.cache_update]
      rfl

/-! ## The recorder that notices every query

`recorderOf` hands the view an answer only on a miss, because a miss is where an answer is
installed. A view that wants to record something about the *query* — that the signer was
serving it — needs telling on a hit as well, and this is that recorder: the view is notified
first, and then the step proceeds exactly as before.

It is a wrapper and not a second design. At a view that notices nothing the two are the same
query implementation, and the extra notice cannot disturb the recordings or the freshness test,
because the law says it leaves the cache alone. -/

open scoped Classical in
/-- The recorder, with the view told about each hash query before it is answered. -/
@[expose] noncomputable def noticingRecorderOf (leftKeep rightKeep : Bytes → σ → Prop) :
    QueryImpl OracleWorld (StateT (StateOf σ) ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => ((recorderOf leftKeep rightKeep) (Sum.inl coin)).run state
    | Sum.inr input =>
        ((recorderOf leftKeep rightKeep) (Sum.inr input)).run
          (CacheView.onQuery state.1 input, state.2)

open scoped Classical in
/-- At a coin query, the noticing recorder is `recorderOf`. -/
theorem noticingRecorderOf_run_inl (leftKeep rightKeep : Bytes → σ → Prop)
    (coin : unifSpec.Domain) (state : StateOf σ) :
    ((noticingRecorderOf leftKeep rightKeep) (Sum.inl coin)).run state =
      ((recorderOf leftKeep rightKeep) (Sum.inl coin)).run state := rfl

open scoped Classical in
/-- At a hash query, the noticing recorder notices the query and then runs `recorderOf`. -/
theorem noticingRecorderOf_run_inr (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) :
    ((noticingRecorderOf leftKeep rightKeep) (Sum.inr input)).run state =
      ((recorderOf leftKeep rightKeep) (Sum.inr input)).run
        (CacheView.onQuery state.1 input, state.2) := rfl

/-! ### The two step laws of the recorder that notices

These are the cached and the fresh branch of the recorder that notices, in closed form. The only
difference from `recorderOf`'s is in the **cached** one: where that oracle returns the state
untouched, this one returns the noticed state. -/

open scoped Classical in
/-- A cached hash query to the noticing recorder returns the cached answer, notices the
query, and updates the recordings. -/
theorem noticingRecorderOf_run_inr_some (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (cached : HashOutput)
    (hcached : CacheView.cacheOf state.1 input = some cached) :
    ((noticingRecorderOf leftKeep rightKeep) (Sum.inr input)).run state =
      (pure (cached, (CacheView.onQuery state.1 input,
        appendedOf leftKeep rightKeep input (CacheView.onQuery state.1 input, state.2) cached)) :
        ProbComp (OracleWorld.Range (Sum.inr input) × StateOf σ)) := by
  classical
  rw [noticingRecorderOf_run_inr]
  exact recorderOf_run_inr_some leftKeep rightKeep input
    (CacheView.onQuery state.1 input, state.2) cached (by rw [cacheOf_onQuery]; exact hcached)

open scoped Classical in
/-- A fresh hash query to the noticing recorder notices the query, then draws, installs and
records an answer. -/
theorem noticingRecorderOf_run_inr_none (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (hfresh : CacheView.cacheOf state.1 input = none) :
    ((noticingRecorderOf leftKeep rightKeep) (Sum.inr input)).run state =
      (((fun answer => (answer,
        (CacheView.update (CacheView.onQuery state.1 input) input answer,
          appendedOf leftKeep rightKeep input
            (CacheView.onQuery state.1 input, state.2) answer))) <$>
        ($ᵗ HashOutput : ProbComp _)) :
          ProbComp (OracleWorld.Range (Sum.inr input) × StateOf σ)) := by
  classical
  rw [noticingRecorderOf_run_inr]
  exact recorderOf_run_inr_none leftKeep rightKeep input
    (CacheView.onQuery state.1 input, state.2) (by rw [cacheOf_onQuery]; exact hfresh)

/-! ### What its recordings satisfy at the end

**The filing test and the disclosure it records are two predicates, not one.** A test that is
read at the state a query is made from can be a flag the signing oracle holds up while it
serves, which is the only kind of disclosing test an adversary cannot forge, since a
cache-readable one it can make true by holding `SK.prf`. Such a flag is *false again* by the
end of the run, so it cannot also be the predicate the entries satisfy at the end.

So `endKeep` is separate, and the two are joined by what a step does: filing an answer puts the
input into whatever the end predicate reads, and no later step takes it out. The filing test is
read at the state the notice has already reached: `hfile` is about `CacheView.onQuery view
input`, so a view may make the test true *by* noticing and still answer for it. -/

open scoped Classical in
/-- **Every entry of the disclosing recording satisfies the end predicate at the end of the
run**, for the recorder that notices. -/
theorem noticing_left_recordOf_endKeep_final {α : Type}
    (leftKeep rightKeep endKeep : Bytes → σ → Prop)
    (hfile : ∀ (input : Bytes) (view : σ),
      leftKeep input (CacheView.onQuery view input) →
        endKeep input (CacheView.onQuery view input))
    (hkeepsQuery : ∀ (input probe : Bytes) (view : σ),
      endKeep input view → endKeep input (CacheView.onQuery view probe))
    (hkeepsUpdate : ∀ (input probe : Bytes) (view : σ) (answer : HashOutput),
      CacheView.cacheOf view probe = none → endKeep input view →
        endKeep input (CacheView.update view probe answer))
    (computation : OracleComp OracleWorld α) (state : StateOf σ) (result : α × StateOf σ)
    (hmem : result ∈
      support ((simulateQ (noticingRecorderOf leftKeep rightKeep) computation).run state))
    (hstart : ∀ entry ∈ state.2.1, endKeep entry.1 state.1) :
    ∀ entry ∈ result.2.2.1, endKeep entry.1 result.2.1 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem] at *
    exact hstart
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine ih step.1 step.2 result hrest ?_
    rcases queried with coin | input
    · rw [noticingRecorderOf_run_inl] at hstep
      rw [recorderOf_step_inl leftKeep rightKeep coin state step hstep]
      exact hstart
    · rw [noticingRecorderOf_run_inr] at hstep
      set noticed : StateOf σ := (CacheView.onQuery state.1 input, state.2) with hnoticed
      have hcarry : ∀ entry ∈ noticed.2.1, endKeep entry.1 noticed.1 := by
        intro entry hentry
        exact hkeepsQuery entry.1 input state.1 (hstart entry hentry)
      have hrecStep := recorderOf_step_record leftKeep rightKeep input noticed step hstep
      cases hcached : CacheView.cacheOf noticed.1 input with
      | some cached =>
        rcases recorderOf_step leftKeep rightKeep input noticed step hstep with
          ⟨-, hshape⟩ | ⟨hbad, -⟩
        · rw [show step.2.1 = noticed.1 from by rw [hshape],
            show step.2.2 = noticed.2 from by
              rw [hshape,
                appendedOf_of_cached leftKeep rightKeep input noticed step.1 cached hcached]]
          exact hcarry
        · rw [hcached] at hbad
          simp at hbad
      | none =>
        have hinstalled : step.2.1 = CacheView.update noticed.1 input step.1 := by
          rcases recorderOf_step leftKeep rightKeep input noticed step hstep with
            ⟨hbad, -⟩ | ⟨-, hshape⟩
          · rw [hcached] at hbad
            simp at hbad
          · rw [hshape]
        have hcarry' : ∀ entry ∈ noticed.2.1, endKeep entry.1 step.2.1 := by
          intro entry hentry
          rw [hinstalled]
          exact hkeepsUpdate entry.1 input noticed.1 step.1 hcached (hcarry entry hentry)
        by_cases hleft : leftKeep input noticed.1
        · rw [hrecStep, appendedOf_of_left leftKeep rightKeep input noticed step.1 hcached hleft]
          intro entry hentry
          rcases List.mem_append.mp hentry with hold | hnew
          · exact hcarry' entry hold
          · rw [List.mem_singleton.mp hnew, hinstalled]
            exact hkeepsUpdate input input noticed.1 step.1 hcached
              (hfile input state.1 hleft)
        · by_cases hright : rightKeep input noticed.1
          · rw [hrecStep,
              appendedOf_of_right leftKeep rightKeep input noticed step.1 hcached hleft hright]
            exact hcarry'
          · rw [hrecStep,
              appendedOf_of_neither leftKeep rightKeep input noticed step.1 hleft hright]
            exact hcarry'

end SLHDSA.SHAKE128s.RecorderView
