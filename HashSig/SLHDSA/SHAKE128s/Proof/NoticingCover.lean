/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SplitWitness

/-!
# The cover lemma for the recorder that notices

The cover lemma (a query whose answer the run ends holding is in one of the two recordings) is
stated here for `RecorderView.noticingRecorderOf`, the recorder the carrier runs under, together
with the three run-level facts it needs on the way. A run of the noticing recorder is not a run
of the plain `RecorderView.recorderOf`, so the plain lemma does not apply.

**Every step is a plain step at the noticed view**, which is the one thing worth saying up front:
`step_inr` turns a step of the noticing recorder into a step of `recorderOf`
at `CacheView.onQuery state.1 input`, so all four step facts come from the plain ones with no new
case analysis. Only the run-level facts need their own induction, and only because the induction
threads a state.

**The tests are read at the noticed view, and so is the cover.** That is the rule the family
keeps — a filing test is read at the state the query is made from, and after the notice is that
state — and it is why `reaches` has to survive `onQuery` as well as `update`. The extra law is
`honQuery`, and for a view whose notice touches only what the tests ignore it is as free as
`hupdate` is.

This is the single-run statement of the composition the carrier tail needs.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.NoticingCover

variable {α : Type}

open Security RecorderView SplitPrefix DigestTape

variable {σ : Type} [CacheView σ]

/-! ## Every step is a plain step at the noticed view -/

/-- **A hash step of the noticing recorder is a plain step at the noticed view.** -/
theorem step_inr (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes) (state : StateOf σ)
    (step : OracleWorld.Range (Sum.inr input) × StateOf σ)
    (hstep : step ∈ support (((noticingRecorderOf leftKeep rightKeep)
      (Sum.inr input)).run state)) :
    step ∈ support (((recorderOf leftKeep rightKeep) (Sum.inr input)).run
      (CacheView.onQuery state.1 input, state.2)) := by
  rw [noticingRecorderOf_run_inr] at hstep
  exact hstep

/-- **And a coin step is a plain coin step at the state itself**, since nothing is noticed. -/
theorem step_inl (leftKeep rightKeep : Bytes → σ → Prop) (coin : unifSpec.Domain)
    (state : StateOf σ) (step : OracleWorld.Range (Sum.inl coin) × StateOf σ)
    (hstep : step ∈ support (((noticingRecorderOf leftKeep rightKeep)
      (Sum.inl coin)).run state)) :
    step.2 = state := by
  rw [@noticingRecorderOf_run_inl σ _ leftKeep rightKeep coin state] at hstep
  exact recorderOf_step_inl leftKeep rightKeep coin state step hstep

/-- **The recordings only grow.** -/
theorem recordOf_prefix {α : Type} (leftKeep rightKeep : Bytes → σ → Prop)
    (computation : OracleComp OracleWorld α) (state : StateOf σ) (result : α × StateOf σ)
    (hmem : result ∈ support ((simulateQ (noticingRecorderOf leftKeep rightKeep)
      computation).run state)) :
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
    rcases queried with coin | probe
    · rw [step_inl leftKeep rightKeep coin state step hstep] at hrest
      exact ih step.1 state result hrest
    · obtain ⟨hleft, hright⟩ := ih step.1 step.2 result hrest
      have hshape := recorderOf_step_record leftKeep rightKeep probe
        (CacheView.onQuery state.1 probe, state.2) step
        (step_inr leftKeep rightKeep probe state step hstep)
      refine ⟨List.IsPrefix.trans ?_ hleft, List.IsPrefix.trans ?_ hright⟩
      · rw [hshape]
        exact left_prefix_appendedOf leftKeep rightKeep probe
          (CacheView.onQuery state.1 probe, state.2) step.1
      · rw [hshape]
        exact right_prefix_appendedOf leftKeep rightKeep probe
          (CacheView.onQuery state.1 probe, state.2) step.1

/-- **And a cached value survives the rest of the run.** -/
theorem cache_value_persists {α : Type} (leftKeep rightKeep : Bytes → σ → Prop)
    (computation : OracleComp OracleWorld α) (state : StateOf σ) (result : α × StateOf σ)
    (hmem : result ∈ support ((simulateQ (noticingRecorderOf leftKeep rightKeep)
      computation).run state))
    (input : Bytes) (answer : HashOutput)
    (hentry : CacheView.cacheOf state.1 input = some answer) :
    CacheView.cacheOf result.2.1 input = some answer := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hentry
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases queried with coin | probe
    · rw [step_inl leftKeep rightKeep coin state step hstep] at hrest
      exact ih step.1 state result hrest hentry
    · refine ih step.1 step.2 result hrest ?_
      refine recorderOf_step_persists leftKeep rightKeep probe
        (CacheView.onQuery state.1 probe, state.2) step
        (step_inr leftKeep rightKeep probe state step hstep) input answer ?_
      change CacheView.cacheOf (CacheView.onQuery state.1 probe) input = some answer
      rw [cacheOf_onQuery]
      exact hentry

/-- **A run stays among the views `reaches` names**, which is what lets a composition enter the
next stage with the predicate it entered this one with. -/
theorem reaches_run {α : Type} (leftKeep rightKeep : Bytes → σ → Prop) (reaches : σ → Prop)
    (hupdate : ∀ (view : σ) (probe : Bytes) (answer : HashOutput),
      reaches view → reaches (CacheView.update view probe answer))
    (honQuery : ∀ (view : σ) (probe : Bytes), reaches view →
      reaches (CacheView.onQuery view probe))
    (computation : OracleComp OracleWorld α) (state : StateOf σ) (result : α × StateOf σ)
    (hmem : result ∈ support ((simulateQ (noticingRecorderOf leftKeep rightKeep)
      computation).run state))
    (hstart : reaches state.1) : reaches result.2.1 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hstart
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases queried with coin | probe
    · rw [step_inl leftKeep rightKeep coin state step hstep] at hrest
      exact ih step.1 state result hrest hstart
    · refine ih step.1 step.2 result hrest ?_
      rcases recorderOf_step leftKeep rightKeep probe
        (CacheView.onQuery state.1 probe, state.2) step
        (step_inr leftKeep rightKeep probe state step hstep) with ⟨-, hshape⟩ | ⟨-, hshape⟩
      · rw [show step.2.1 = CacheView.onQuery state.1 probe from by rw [hshape]]
        exact honQuery state.1 probe hstart
      · rw [show step.2.1 =
          CacheView.update (CacheView.onQuery state.1 probe) probe step.1 from by rw [hshape]]
        exact hupdate _ probe step.1 (honQuery state.1 probe hstart)

/-! ## The cover, at the views a run of the noticing recorder passes through -/

open scoped Classical in
/-- **A query whose answer the run ends holding is recorded on one side or the other.**
The cover lemma for the recorder that notices.

The cover is consulted exactly once, at the noticed view the input is *answered* at. `reaches`
is threaded to get there, which is why it has to survive both of the view's moves. -/
theorem mem_recordOf_of_cache_reaches {α : Type} (leftKeep rightKeep : Bytes → σ → Prop)
    (inClass : Bytes → Prop) (reaches : σ → Prop)
    (hcover : ∀ (input : Bytes) (view : σ), inClass input → reaches view →
      CacheView.cacheOf view input = none → leftKeep input view ∨ rightKeep input view)
    (hupdate : ∀ (view : σ) (probe : Bytes) (answer : HashOutput),
      reaches view → reaches (CacheView.update view probe answer))
    (honQuery : ∀ (view : σ) (probe : Bytes), reaches view →
      reaches (CacheView.onQuery view probe))
    (computation : OracleComp OracleWorld α) (state : StateOf σ) (result : α × StateOf σ)
    (hmem : result ∈ support ((simulateQ (noticingRecorderOf leftKeep rightKeep)
      computation).run state))
    (input : Bytes) (answer : HashOutput) (hclass : inClass input)
    (hstart : reaches state.1)
    (hfresh : CacheView.cacheOf state.1 input = none)
    (hfinal : CacheView.cacheOf result.2.1 input = some answer) :
    (input, answer) ∈ result.2.2.1 ∨ (input, answer) ∈ result.2.2.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem] at hfinal
    rw [hfresh] at hfinal
    simp at hfinal
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases queried with coin | probe
    · rw [step_inl leftKeep rightKeep coin state step hstep] at hrest
      exact ih step.1 state result hrest hstart hfresh hfinal
    · -- The plain step, at the noticed view.
      have hplain := step_inr leftKeep rightKeep probe state step hstep
      have hnoticed : CacheView.cacheOf (CacheView.onQuery state.1 probe) = CacheView.cacheOf
        state.1 := cacheOf_onQuery state.1 probe
      by_cases hsame : input = probe
      · subst hsame
        have hpersist : CacheView.cacheOf result.2.1 input = some step.1 :=
          cache_value_persists leftKeep rightKeep (next step.1) step.2 result hrest input step.1
            (recorderOf_step_cache_self leftKeep rightKeep input
              (CacheView.onQuery state.1 input, state.2) step hplain)
        have hvalue : step.1 = answer := by
          rw [hpersist] at hfinal
          exact Option.some.inj hfinal
        obtain ⟨hgrowLeft, hgrowRight⟩ :=
          recordOf_prefix leftKeep rightKeep (next step.1) step.2 result hrest
        have hrecStep := recorderOf_step_record leftKeep rightKeep input
          (CacheView.onQuery state.1 input, state.2) step hplain
        have hfreshNoticed :
            CacheView.cacheOf (CacheView.onQuery state.1 input) input = none := by
          rw [hnoticed]; exact hfresh
        by_cases hleft : leftKeep input (CacheView.onQuery state.1 input)
        · refine Or.inl (hgrowLeft.subset ?_)
          rw [hrecStep, appendedOf_of_left leftKeep rightKeep input
            (CacheView.onQuery state.1 input, state.2) step.1 hfreshNoticed hleft, hvalue]
          simp
        · have hright : rightKeep input (CacheView.onQuery state.1 input) := by
            rcases hcover input (CacheView.onQuery state.1 input) hclass
              (honQuery state.1 input hstart) hfreshNoticed with hcase | hcase
            · exact absurd hcase hleft
            · exact hcase
          refine Or.inr (hgrowRight.subset ?_)
          rw [hrecStep, appendedOf_of_right leftKeep rightKeep input
            (CacheView.onQuery state.1 input, state.2) step.1 hfreshNoticed hleft hright, hvalue]
          simp
      · refine ih step.1 step.2 result hrest ?_ ?_ hfinal
        · rcases recorderOf_step leftKeep rightKeep probe
            (CacheView.onQuery state.1 probe, state.2) step hplain with
            ⟨-, hshape⟩ | ⟨-, hshape⟩
          · rw [show step.2.1 = CacheView.onQuery state.1 probe from by rw [hshape]]
            exact honQuery state.1 probe hstart
          · rw [show step.2.1 =
              CacheView.update (CacheView.onQuery state.1 probe) probe step.1 from by rw [hshape]]
            exact hupdate _ probe step.1 (honQuery state.1 probe hstart)
        · rcases recorderOf_step leftKeep rightKeep probe
            (CacheView.onQuery state.1 probe, state.2) step hplain with
            ⟨-, hshape⟩ | ⟨-, hshape⟩
          · rw [show step.2.1 = CacheView.onQuery state.1 probe from by rw [hshape], hnoticed]
            exact hfresh
          · rw [show step.2.1 =
                CacheView.update (CacheView.onQuery state.1 probe) probe step.1 from by
              rw [hshape],
              cacheOf_update_of_ne (CacheView.onQuery state.1 probe) probe input step.1 hsame,
              hnoticed]
            exact hfresh

end SlhDsaSecurity.NoticingCover
