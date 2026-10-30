/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.DigestTape

/-!
# A random oracle keeping two recordings

The coverage charge needs its disclosing digests to occupy a fixed *index block* of the tape
and its targets to occupy the rest, because the leave-one-out resampling needs the disclosure
set to be a function of the index rather than of the run. A single recording cannot supply
that: the two kinds of query interleave, so their positions are run-dependent. Two recordings
can, each padded to its own length and laid end to end.

`recorder` is the shared random oracle of `DigestTape` with its state doubled: alongside the
cache it keeps a left and a right recording of fresh answers. The decision to record is taken
on the input *and the cache in force* (`appended`). That generality is free — the decision is
made before the answer is drawn, so it is a function of the past — and it is what lets "the
signer randomised this input" be the left-hand test, since that is a question about the cache
rather than about bytes. The two tests are made exclusive by priority rather than assumed
disjoint, so one fresh answer never advances both recordings at once.

The lemmas here read the instrumented run back:

* `appended_of_cached`, `appended_of_left`, `appended_of_right` and `appended_of_neither` say
  which recording a single answer goes to;
* `mem_support_rom` says the recordings are invisible: dropping them lands in the support of the
  plain run;
* `recorder_cache_value_persists` says cache entries persist along a recorded run;
* `right_record_class` and `right_record_suffix` describe what the right recording holds, and
  the cache at which each of its entries was filed.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.SplitPrefix

open DigestTape

/-- The cache together with the two recordings so far. -/
abbrev SplitState := QueryCache HashSpec × Record × Record

open scoped Classical in
/-- What the two recordings become when a query is answered: the left one takes the entry if
the query is fresh and passes the left test, otherwise the right one takes it if it passes the
right test, otherwise neither. The tests are tried in order, so a single answer is recorded
once. -/
@[expose] noncomputable def appended (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) (answer : HashOutput) : Record × Record :=
  if state.1 input = none ∧ leftKeep input state.1 then
    (state.2.1 ++ [(input, answer)], state.2.2)
  else if state.1 input = none ∧ rightKeep input state.1 then
    (state.2.1, state.2.2 ++ [(input, answer)])
  else state.2

open scoped Classical in
/-- The shared random oracle, keeping two recordings. -/
@[expose] noncomputable def recorder (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) :
    QueryImpl OracleWorld (StateT SplitState ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input => do
        let step ← (randomOracle input).run state.1
        pure (step.1, (step.2, appended leftKeep rightKeep input state step.1))

/-- A coin query to the recorder samples uniformly and leaves the state untouched. -/
theorem recorder_run_inl (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (coin : unifSpec.Domain) (state : SplitState) :
    ((recorder leftKeep rightKeep) (Sum.inl coin)).run state =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, state) : ProbComp _) := rfl

/-- A hash query to the recorder runs the caching random oracle and files the answer with
`appended`. -/
theorem recorder_run_inr (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) :
    ((recorder leftKeep rightKeep) (Sum.inr input)).run state =
      (((randomOracle input).run state.1 >>= fun step =>
        pure (step.1, (step.2, appended leftKeep rightKeep input state step.1))) :
          ProbComp (OracleWorld.Range (Sum.inr input) × SplitState)) := rfl

/-! ## Reading the two tests -/

/-- A cached input is recorded nowhere. -/
theorem appended_of_cached (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) (answer cached : HashOutput)
    (hcached : state.1 input = some cached) :
    appended leftKeep rightKeep input state answer = state.2 := by
  classical
  rw [appended, ite_eq_right (by rw [hcached]; simp), ite_eq_right (by rw [hcached]; simp)]

/-- A fresh input passing the left test goes to the left recording. -/
theorem appended_of_left (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) (answer : HashOutput)
    (hfresh : state.1 input = none) (hleft : leftKeep input state.1) :
    appended leftKeep rightKeep input state answer =
      (state.2.1 ++ [(input, answer)], state.2.2) := by
  classical
  rw [appended, ite_eq_left ⟨hfresh, hleft⟩]

/-- A fresh input failing the left test and passing the right one goes to the right recording.
-/
theorem appended_of_right (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) (answer : HashOutput)
    (hfresh : state.1 input = none) (hleft : ¬ leftKeep input state.1)
    (hright : rightKeep input state.1) :
    appended leftKeep rightKeep input state answer =
      (state.2.1, state.2.2 ++ [(input, answer)]) := by
  classical
  rw [appended, ite_eq_right (fun hboth => hleft hboth.2), ite_eq_left ⟨hfresh, hright⟩]

/-- An input passing neither test is recorded nowhere. -/
theorem appended_of_neither (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) (answer : HashOutput)
    (hleft : ¬ leftKeep input state.1) (hright : ¬ rightKeep input state.1) :
    appended leftKeep rightKeep input state answer = state.2 := by
  classical
  rw [appended, ite_eq_right (fun hboth => hleft hboth.2),
    ite_eq_right (fun hboth => hright hboth.2)]

/-! ## The instrumentation is invisible

Both recordings are write-only components of the state: neither ever influences an answer, so
the instrumented run and the plain run of the shared oracle agree on every event that does not
mention them. -/

/-- Every recorded run is a run: dropping both recordings lands in the support of the plain run
of the shared oracle. -/
theorem mem_support_rom {α : Type} (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (computation : OracleComp OracleWorld α) (state : SplitState) (result : α × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder leftKeep rightKeep) computation).run state)) :
    (result.1, result.2.1) ∈ support ((simulateQ KeygenUniform.rom computation).run state.1) := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, hmem]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    refine ⟨(step.1, step.2.1), ?_, ih step.1 step.2 result hrest⟩
    rcases queried with coin | input
    · rw [recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, hvalue, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [DigestTape.rom_run_inl, mem_support_bind_iff]
      refine ⟨value, hvalue, ?_⟩
      rw [support_pure, Set.mem_singleton_iff, hpure]
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, hinner, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [DigestTape.rom_run_inr]
      have hshape : (step.1, step.2.1) = inner := by
        rw [hpure]
        rfl
      rw [hshape]
      exact hinner

/-! ## The cache along a recorded run -/

/-- **Cache entries persist along a recorded run.** -/
theorem recorder_cache_value_persists {α : Type}
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (computation : OracleComp OracleWorld α) (state : SplitState) (result : α × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder leftKeep rightKeep) computation).run state))
    (input : Bytes) (answer : HashOutput) (hentry : state.1 input = some answer) :
    result.2.1 input = some answer := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hentry
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine ih step.1 step.2 result hrest ?_
    rcases queried with coin | queried
    · rw [recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact hentry
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, hinner, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      cases hqueried : state.1 queried with
      | none =>
        rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hinner
        obtain ⟨sampled, -, hpair⟩ := hinner
        have hmid : inner.2 = state.1.cacheQuery queried sampled :=
          (Prod.ext_iff.mp hpair).2.symm
        change inner.2 input = some answer
        rw [hmid]
        have hne : input ≠ queried := by
          intro hsame
          rw [hsame, hqueried] at hentry
          simp at hentry
        rw [QueryCache.cacheQuery_of_ne state.1 sampled hne]
        exact hentry
      | some cached =>
        rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
          Set.mem_singleton_iff] at hinner
        change inner.2 input = some answer
        rw [hinner]
        exact hentry

/-! ## What each recording holds

A charge reads the two recordings as two sets of cache entries, so it needs to know what their
entries satisfy at the end of the run. The left test is checked at the cache in force, so what
survives to the final cache is what the test is monotone in; the right test's byte part survives
unconditionally. -/

/-- **Every right-recorded input is in the class the right test implies**, provided the
starting recording already was. -/
theorem right_record_class {α : Type}
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) (inClass : Bytes → Prop)
    (hrightClass : ∀ (input : Bytes) (cache : QueryCache HashSpec),
      rightKeep input cache → inClass input)
    (computation : OracleComp OracleWorld α) (state : SplitState) (result : α × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder leftKeep rightKeep) computation).run state))
    (hstart : ∀ entry ∈ state.2.2, inClass entry.1) :
    ∀ entry ∈ result.2.2.2, inClass entry.1 := by
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
    · rw [recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      have hsame : step.2 = state := congrArg Prod.snd hpure
      rw [hsame]
      exact hstart
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, hinner, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      cases hcached : state.1 input with
      | some cached =>
        rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
          Set.mem_singleton_iff] at hinner
        have hstate : step.2 = state := by
          rw [hpure, hinner]
          exact Prod.ext rfl (appended_of_cached leftKeep rightKeep input state cached cached
            hcached)
        rw [hstate]
        exact hstart
      | none =>
        rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hinner
        obtain ⟨answer, -, hpair⟩ := hinner
        have hinnerAnswer : inner.1 = answer := (Prod.ext_iff.mp hpair).1.symm
        have hrecStep : step.2.2 = appended leftKeep rightKeep input state answer := by
          rw [hpure, ← hinnerAnswer]
        by_cases hleft : leftKeep input state.1
        · rw [hrecStep, appended_of_left leftKeep rightKeep input state answer hcached hleft]
          exact hstart
        · by_cases hright : rightKeep input state.1
          · rw [hrecStep,
              appended_of_right leftKeep rightKeep input state answer hcached hleft hright]
            intro entry hentry
            rcases List.mem_append.mp hentry with hold | hnew
            · exact hstart entry hold
            · rw [List.mem_singleton.mp hnew]
              exact hrightClass input state.1 hright
          · rw [hrecStep, appended_of_neither leftKeep rightKeep input state answer hleft hright]
            exact hstart

/-! ## When a right-recorded entry was recorded

The right test is checked at the cache in force, and what it said there is the only thing the
recording remembers about the order. This lemma hands that cache back: every entry the right
recording holds was recorded at some cache which the final one extends, where its own input was
absent and the right test held. Reading the order off the recorder is what lets a later
argument say which of two queries came first without appealing to who makes them. -/

/-- **What a run adds to the target recording, with the cache each entry was filed at.** The
suffix form of `right_record_witness`: it names the entries the run appended, so a caller that
can rule out the right test at every cache the run reaches concludes the recording did not grow
at all. -/
theorem right_record_suffix {α : Type}
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (computation : OracleComp OracleWorld α) (state : SplitState) (result : α × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder leftKeep rightKeep) computation).run state)) :
    ∃ suffix : Record, result.2.2.2 = state.2.2 ++ suffix ∧
      ∀ entry ∈ suffix, ∃ mid : QueryCache HashSpec,
        (∀ (probe : Bytes) (value : HashOutput),
            state.1 probe = some value → mid probe = some value) ∧
          (∀ (probe : Bytes) (value : HashOutput),
            mid probe = some value → result.2.1 probe = some value) ∧
            mid entry.1 = none ∧ rightKeep entry.1 mid ∧
              result.2.1 entry.1 = some entry.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact ⟨[], (List.append_nil _).symm, fun entry hentry => absurd hentry (by simp)⟩
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    obtain ⟨suffix, hsuffix, hentries⟩ := ih step.1 step.2 result hrest
    have hpersistStep : ∀ (probe : Bytes) (value : HashOutput),
        step.2.1 probe = some value → result.2.1 probe = some value := fun probe value hprobe =>
      recorder_cache_value_persists leftKeep rightKeep (next step.1) step.2 result hrest probe
        value hprobe
    rcases queried with coin | input
    · rw [recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      have hsame : step.2 = state := congrArg Prod.snd hpure
      refine ⟨suffix, by rw [hsuffix, hsame], fun entry hentry => ?_⟩
      obtain ⟨mid, hstart, hlater, habsent, hkeep, hfinal⟩ := hentries entry hentry
      exact ⟨mid, by rw [← hsame]; exact hstart, hlater, habsent, hkeep, hfinal⟩
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, hinner, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      cases hcached : state.1 input with
      | some cached =>
        rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
          Set.mem_singleton_iff] at hinner
        have hstate : step.2 = state := by
          rw [hpure, hinner]
          exact Prod.ext rfl (appended_of_cached leftKeep rightKeep input state cached cached
            hcached)
        refine ⟨suffix, by rw [hsuffix, hstate], fun entry hentry => ?_⟩
        obtain ⟨mid, hstart, hlater, habsent, hkeep, hfinal⟩ := hentries entry hentry
        exact ⟨mid, by rw [← hstate]; exact hstart, hlater, habsent, hkeep, hfinal⟩
      | none =>
        rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hinner
        obtain ⟨answer, -, hpair⟩ := hinner
        have hinnerCache : inner.2 = state.1.cacheQuery input answer :=
          (Prod.ext_iff.mp hpair).2.symm
        have hinnerAnswer : inner.1 = answer := (Prod.ext_iff.mp hpair).1.symm
        have hcacheStep : step.2.1 = state.1.cacheQuery input answer := by
          rw [hpure, ← hinnerCache]
        have hrecStep : step.2.2 = appended leftKeep rightKeep input state answer := by
          rw [hpure, ← hinnerAnswer]
        have hstartStep : ∀ (probe : Bytes) (value : HashOutput),
            state.1 probe = some value → step.2.1 probe = some value := by
          intro probe value hprobe
          rw [hcacheStep]
          have hne : probe ≠ input := by
            intro hsame
            rw [hsame, hcached] at hprobe
            simp at hprobe
          rw [QueryCache.cacheQuery_of_ne state.1 answer hne]
          exact hprobe
        have hshift : ∀ entry ∈ suffix, ∃ mid : QueryCache HashSpec,
            (∀ (probe : Bytes) (value : HashOutput),
                state.1 probe = some value → mid probe = some value) ∧
              (∀ (probe : Bytes) (value : HashOutput),
                mid probe = some value → result.2.1 probe = some value) ∧
                mid entry.1 = none ∧ rightKeep entry.1 mid ∧
                  result.2.1 entry.1 = some entry.2 := by
          intro entry hentry
          obtain ⟨mid, hstart, hlater, habsent, hkeep, hfinal⟩ := hentries entry hentry
          exact ⟨mid, fun probe value hprobe => hstart probe value (hstartStep probe value hprobe),
            hlater, habsent, hkeep, hfinal⟩
        by_cases hleft : leftKeep input state.1
        · refine ⟨suffix, ?_, hshift⟩
          rw [hsuffix, hrecStep,
            appended_of_left leftKeep rightKeep input state answer hcached hleft]
        · by_cases hright : rightKeep input state.1
          · refine ⟨(input, answer) :: suffix, ?_, ?_⟩
            · rw [hsuffix, hrecStep,
                appended_of_right leftKeep rightKeep input state answer hcached hleft hright]
              simp
            · intro entry hentry
              rcases List.mem_cons.mp hentry with hnew | hold
              · refine ⟨state.1, fun _ _ hprobe => hprobe, ?_, ?_, ?_, ?_⟩
                · intro probe value hprobe
                  exact hpersistStep probe value (hstartStep probe value hprobe)
                · rw [hnew]; exact hcached
                · rw [hnew]; exact hright
                · rw [hnew]
                  refine hpersistStep input answer ?_
                  rw [hcacheStep, QueryCache.cacheQuery_self]
              · exact hshift entry hold
          · refine ⟨suffix, ?_, hshift⟩
            rw [hsuffix, hrecStep,
              appended_of_neither leftKeep rightKeep input state answer hleft hright]

end SLHDSA.SHAKE128s.SplitPrefix
