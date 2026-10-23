/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.NoticingCover
public import HashSig.SLHDSA.SHAKE128s.Proof.OrderingCompose

/-!
# The cover lemma across a bracketed phase

`NoticingCover.mem_recordOf_of_cache_reaches` is the single-run statement. This is the same
statement for `PhaseFusion.fuseServing` — the adversary's phase, with a bracket raised and
lowered around each signing sub-run.

**Two view predicates, because one cannot survive the bracket.** `reaches` is for the views the
phase itself is at, which for the carrier is a clear framing; `reachesIn request` is for the
views inside the sub-run serving `request`, which for the carrier is that request's own frame.
The opening bracket moves from the first to the second **on purpose** — that is the same fact
`RecordInvariant.phase_invariant_of_after` exists for — so there is no single predicate here,
and a coincidence hypothesis between the two is not available either: they genuinely differ at
exactly the states the lemma visits.

**The signing branch takes the conclusion's own shape at the sub-run's own starting state.**
`hsub` is not a cover for in-flight views quantified over every request; it is this lemma's own
conclusion, asked of one sub-run, at the state the opening bracket produced. That is the rule
that makes these compose, and here it buys something beyond composing: a cover over all requests
would have to be supplied for every frame, which is exactly how the carrier's narrowing — the
residue being a coincidence at *the frame in flight* rather than a class over all frames — gets
lost on the way to the caller. Asked of the sub-runs that actually occur, at the views actually
reached, with the input actually answered there, the hypothesis says where the cost comes from
instead of rounding it up.

**And the closing bracket is asked for unconditionally**, for the reason
`phase_invariant_of_after` was: it writes rather than tests, so it restores `reaches` whatever it
is handed, and then the signing branch needs nothing about the sub-run's own final view.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.FusedCover

variable {α : Type}

open Security RecorderView SplitPrefix PhaseFusion DigestTape

variable {σ : Type} [CacheView σ] {ω : Type} [Monoid ω]

/-! ## The phase's own two run facts -/

/-- **The recordings only grow across the phase.** -/
theorem recordOf_prefix (leftKeep rightKeep : Bytes → σ → Prop)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → StateOf σ → StateOf σ) (afterMap : StateOf σ → StateOf σ)
    (hbeforeRecord : ∀ (request : Message) (state : StateOf σ), (before request state).2 = state.2)
    (hafterRecord : ∀ state : StateOf σ, (afterMap state).2 = state.2)
    {α : Type} (phase : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : ω × SigningLog × StateOf σ) (result : α × (ω × SigningLog × StateOf σ)),
      result ∈ support ((simulateQ (fuseServing (noticingRecorderOf leftKeep rightKeep) inner
        before afterMap) phase).run state) →
        state.2.2.2.1 <+: result.2.2.2.2.1 ∧ state.2.2.2.2 <+: result.2.2.2.2.2 := by
  induction phase using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [show result.2.2.2 = state.2.2 from by rw [hmem]]
    exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  | query_bind queried next ih =>
    intro state result hmem
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    obtain ⟨htailLeft, htailRight⟩ := ih step.1 step.2 result hrest
    refine ⟨List.IsPrefix.trans ?_ htailLeft, List.IsPrefix.trans ?_ htailRight⟩ <;>
      rcases queried with world | request
    · rw [OrderingCompose.fuseServing_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨z, hz, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [show step.2.2.2 = z.2 from by rw [hpure]]
      exact (NoticingCover.recordOf_prefix leftKeep rightKeep _ state.2.2 z hz).1
    · rw [OrderingCompose.fuseServing_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨z, hz, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [show step.2.2.2 = afterMap z.2 from by rw [hpure],
        show (afterMap z.2).2.1 = z.2.2.1 from by rw [hafterRecord]]
      refine List.IsPrefix.trans ?_
        (NoticingCover.recordOf_prefix leftKeep rightKeep _ (before request state.2.2) z hz).1
      rw [hbeforeRecord]
    · rw [OrderingCompose.fuseServing_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨z, hz, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [show step.2.2.2 = z.2 from by rw [hpure]]
      exact (NoticingCover.recordOf_prefix leftKeep rightKeep _ state.2.2 z hz).2
    · rw [OrderingCompose.fuseServing_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨z, hz, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [show step.2.2.2 = afterMap z.2 from by rw [hpure],
        show (afterMap z.2).2.2 = z.2.2.2 from by rw [hafterRecord]]
      refine List.IsPrefix.trans ?_
        (NoticingCover.recordOf_prefix leftKeep rightKeep _ (before request state.2.2) z hz).2
      rw [hbeforeRecord]

/-- **And a cached value survives it.** -/
theorem cache_value_persists (leftKeep rightKeep : Bytes → σ → Prop)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → StateOf σ → StateOf σ) (afterMap : StateOf σ → StateOf σ)
    (hbeforeCache : ∀ (request : Message) (state : StateOf σ),
      CacheView.cacheOf (before request state).1 = CacheView.cacheOf state.1)
    (hafterCache : ∀ state : StateOf σ,
      CacheView.cacheOf (afterMap state).1 = CacheView.cacheOf state.1)
    {α : Type} (phase : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : ω × SigningLog × StateOf σ) (result : α × (ω × SigningLog × StateOf σ)),
      result ∈ support ((simulateQ (fuseServing (noticingRecorderOf leftKeep rightKeep) inner
        before afterMap) phase).run state) →
      ∀ (input : Bytes) (answer : HashOutput),
        CacheView.cacheOf state.2.2.1 input = some answer →
          CacheView.cacheOf result.2.2.2.1 input = some answer := by
  induction phase using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem input answer hentry
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [show result.2.2.2 = state.2.2 from by rw [hmem]]
    exact hentry
  | query_bind queried next ih =>
    intro state result hmem input answer hentry
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine ih step.1 step.2 result hrest input answer ?_
    rcases queried with world | request
    · rw [OrderingCompose.fuseServing_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨z, hz, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [show step.2.2.2 = z.2 from by rw [hpure]]
      exact NoticingCover.cache_value_persists leftKeep rightKeep _ state.2.2 z hz input answer
        hentry
    · rw [OrderingCompose.fuseServing_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨z, hz, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [show step.2.2.2 = afterMap z.2 from by rw [hpure], hafterCache]
      refine NoticingCover.cache_value_persists leftKeep rightKeep _ (before request state.2.2) z
        hz input answer ?_
      rw [hbeforeCache]
      exact hentry

/-! ## The cover across the phase -/

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **A query whose answer the phase ends holding is recorded on one side or the other.**

The adversary's own steps are nested runs at the phase's own views and are discharged by
`NoticingCover.mem_recordOf_of_cache_reaches`. A signing step is a nested run at the view the
opening bracket produced, and `hsub` is this lemma's own conclusion asked there — of the sub-runs
that actually occur, at the views actually reached, and only when the input is actually answered
inside one. -/
theorem mem_recordOf_of_cache_reaches (leftKeep rightKeep : Bytes → σ → Prop)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → StateOf σ → StateOf σ) (afterMap : StateOf σ → StateOf σ)
    (inClass : Bytes → Prop) (reaches : σ → Prop) (input : Bytes) (answer : HashOutput)
    (hclass : inClass input)
    (hcover : ∀ (probe : Bytes) (view : σ), inClass probe → reaches view →
      CacheView.cacheOf view probe = none → leftKeep probe view ∨ rightKeep probe view)
    (hupdate : ∀ (view : σ) (probe : Bytes) (value : HashOutput),
      reaches view → reaches (CacheView.update view probe value))
    (honQuery : ∀ (view : σ) (probe : Bytes), reaches view →
      reaches (CacheView.onQuery view probe))
    (hbeforeRecord : ∀ (request : Message) (state : StateOf σ), (before request state).2 = state.2)
    (hafterRecord : ∀ state : StateOf σ, (afterMap state).2 = state.2)
    (hbeforeCache : ∀ (request : Message) (state : StateOf σ),
      CacheView.cacheOf (before request state).1 = CacheView.cacheOf state.1)
    (hafterCache : ∀ state : StateOf σ,
      CacheView.cacheOf (afterMap state).1 = CacheView.cacheOf state.1)
    (hafter : ∀ state : StateOf σ, reaches (afterMap state).1)
    (hsub : ∀ (request : Message) (log : SigningLog) (state : StateOf σ)
        (z : (((OracleWorld + SigningSpec).Range (Sum.inr request) × ω) × SigningLog) ×
          StateOf σ),
      z ∈ support ((simulateQ (noticingRecorderOf leftKeep rightKeep)
        (((inner (Sum.inr request)).run).run log)).run (before request state)) →
      reaches state.1 → CacheView.cacheOf state.1 input = none →
      CacheView.cacheOf z.2.1 input = some answer →
        (input, answer) ∈ z.2.2.1 ∨ (input, answer) ∈ z.2.2.2)
    {α : Type} (phase : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : ω × SigningLog × StateOf σ) (result : α × (ω × SigningLog × StateOf σ)),
      result ∈ support ((simulateQ (fuseServing (noticingRecorderOf leftKeep rightKeep) inner
        before afterMap) phase).run state) →
      reaches state.2.2.1 → CacheView.cacheOf state.2.2.1 input = none →
      CacheView.cacheOf result.2.2.2.1 input = some answer →
        (input, answer) ∈ result.2.2.2.2.1 ∨ (input, answer) ∈ result.2.2.2.2.2 := by
  classical
  induction phase using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem hreach hfresh hfinal
    rw [show result.2.2.2 = state.2.2 from by
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      rw [hmem]] at hfinal
    rw [hfresh] at hfinal
    simp at hfinal
  | query_bind queried next ih =>
    intro state result hmem hreach hfresh hfinal
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases queried with world | request
    · rw [OrderingCompose.fuseServing_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨z, hz, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      have hstate : step.2.2.2 = z.2 := by rw [hpure]
      by_cases hz2 : CacheView.cacheOf z.2.1 input = none
      · refine ih step.1 step.2 result hrest ?_ ?_ hfinal
        · rw [hstate]
          exact NoticingCover.reaches_run leftKeep rightKeep reaches hupdate honQuery _
            state.2.2 z hz hreach
        · rw [hstate]
          exact hz2
      · obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hz2
        have hsame : value = answer := by
          have hpers : CacheView.cacheOf result.2.2.2.1 input = some value :=
            cache_value_persists leftKeep rightKeep inner before afterMap hbeforeCache
              hafterCache _ step.2 result hrest input value (by rw [hstate]; exact hvalue)
          rw [hpers] at hfinal
          exact Option.some.inj hfinal
        subst hsame
        obtain ⟨hleft, hright⟩ := recordOf_prefix leftKeep rightKeep inner before afterMap
          hbeforeRecord hafterRecord _ step.2 result hrest
        rw [hstate] at hleft hright
        exact (NoticingCover.mem_recordOf_of_cache_reaches leftKeep rightKeep inClass reaches
          hcover hupdate honQuery _ state.2.2 z hz input value hclass hreach hfresh
          hvalue).imp (fun hmemz => hleft.subset hmemz) fun hmemz => hright.subset hmemz
    · rw [OrderingCompose.fuseServing_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨z, hz, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      have hstate : step.2.2.2 = afterMap z.2 := by rw [hpure]
      by_cases hz2 : CacheView.cacheOf z.2.1 input = none
      · refine ih step.1 step.2 result hrest ?_ ?_ hfinal
        · rw [hstate]
          exact hafter z.2
        · rw [hstate, hafterCache]
          exact hz2
      · obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hz2
        have hsame : value = answer := by
          have hpers : CacheView.cacheOf result.2.2.2.1 input = some value :=
            cache_value_persists leftKeep rightKeep inner before afterMap hbeforeCache
              hafterCache _ step.2 result hrest input value
              (by rw [hstate, hafterCache]; exact hvalue)
          rw [hpers] at hfinal
          exact Option.some.inj hfinal
        subst hsame
        obtain ⟨hleft, hright⟩ := recordOf_prefix leftKeep rightKeep inner before afterMap
          hbeforeRecord hafterRecord _ step.2 result hrest
        rw [hstate] at hleft hright
        rw [show (afterMap z.2).2.1 = z.2.2.1 from by rw [hafterRecord]] at hleft
        rw [show (afterMap z.2).2.2 = z.2.2.2 from by rw [hafterRecord]] at hright
        exact (hsub request state.2.1 state.2.2 z hz hreach hfresh hvalue).imp
          (fun hmemz => hleft.subset hmemz) fun hmemz => hright.subset hmemz

end SlhDsaSecurity.FusedCover
