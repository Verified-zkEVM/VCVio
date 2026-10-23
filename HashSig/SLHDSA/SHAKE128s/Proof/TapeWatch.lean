/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.FusedTape
public import HashSig.SLHDSA.SHAKE128s.Proof.FiredCoverage
import VCVio.OracleComp.EvalDist.Sum

/-!
# Watching one input of a tape run

The second-order coverage charge needs, for each fired target, that the `PRF_msg` answer which
made it fire was a fresh draw. This file is the probabilistic half of that: at a run of the tape
recorder with both blocks fixed, an input that is uncached now ends up holding an answer in a
given set **and not filed in either recording** with probability at most the set's mass under
one fresh draw.

The reason is that an input is drawn at most once, and the draw is fresh exactly when neither
block answers it — a block answer files the input, which the event excludes. So the watched
quantity is a supermartingale: `watchValue` is the set's mass while the input is uncached, and
the indicator of the event once it is cached. A step that does not touch the input leaves it
alone; a step that files the input drops it to zero; a step that draws it inline averages to the
mass. `expect_run_le` turns the one-step bound into a whole-run bound, and the fused and
three-stage forms follow because the brackets do not touch the cache or the recordings.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal


namespace SlhDsaSecurity.TapeWatch

variable {α γ : Type}

open DigestTape TapeFactor NoticingTape RecorderView PhaseFusion FusedTape

/-! ## A supermartingale survives a run -/

/-- **A value that no step raises in expectation is not raised by a run.** -/
theorem expect_run_le {ι : Type} {spec : OracleSpec ι} {S : Type}
    (impl : QueryImpl spec (StateT S ProbComp)) (value : S → ℝ≥0∞)
    (hstep : ∀ (queried : spec.Domain) (state : S),
      ∑' z, Pr{let x ← (impl queried).run state}[x = z] * value z.2 ≤ value state)
    {α : Type} (computation : OracleComp spec α) (state : S) :
    ∑' z, Pr{let x ← (simulateQ impl computation).run state}[x = z] * value z.2 ≤ value state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result =>
    rw [simulateQ_pure, StateT.run_pure]
    exact le_of_eq (FiredCoverage.tsum_probOutput_pure (result, state) (fun z => value z.2))
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      FiredCoverage.tsum_probOutput_bind]
    calc ∑' step, Pr{let x ← (impl queried).run state}[x = step] *
          ∑' z, Pr{let x ← (simulateQ impl (next step.1)).run step.2}[x = z] * value z.2
        ≤ ∑' step, Pr{let x ← (impl queried).run state}[x = step] * value step.2 :=
          ENNReal.tsum_le_tsum fun step => mul_le_mul' le_rfl (ih step.1 step.2)
      _ ≤ value state := hstep queried state

/-- **And a run followed by a continuation that does not raise it either.** -/
theorem expect_run_bind_le {ι : Type} {spec : OracleSpec ι} {S γ : Type}
    (impl : QueryImpl spec (StateT S ProbComp)) (value : S → ℝ≥0∞)
    (hstep : ∀ (queried : spec.Domain) (state : S),
      ∑' z, Pr{let x ← (impl queried).run state}[x = z] * value z.2 ≤ value state)
    {α : Type} (computation : OracleComp spec α) (state : S)
    (cont : α × S → ProbComp γ) (final : γ → ℝ≥0∞)
    (hcont : ∀ z, ∑' w, Pr{let x ← cont z}[x = w] * final w ≤ value z.2) :
    ∑' w, Pr{let x ← (simulateQ impl computation).run state >>= cont}[x = w] * final w ≤
      value state := by
  rw [FiredCoverage.tsum_probOutput_bind]
  calc ∑' z, Pr{let x ← (simulateQ impl computation).run state}[x = z] *
        ∑' w, Pr{let x ← cont z}[x = w] * final w
      ≤ ∑' z, Pr{let x ← (simulateQ impl computation).run state}[x = z] * value z.2 :=
        ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl (hcont z)
    _ ≤ value state := expect_run_le impl value hstep computation state

/-! ## The watched value -/

variable {σ : Type} [CacheView σ]

open scoped Classical in
/-- **The watched value of one input.** While it is uncached: the mass of the target set under
one fresh draw. Once cached: whether it holds an answer in the set and sits in neither
recording. -/
noncomputable def watchValue (target : Bytes) (hits : HashOutput → Prop)
    (state : SplitTapeState σ) : ℝ≥0∞ :=
  match CacheView.cacheOf state.1 target with
  | some answer =>
      if hits answer ∧ target ∉ state.2.2.1.map Prod.fst ∧ target ∉ state.2.2.2.map Prod.fst
      then 1 else 0
  | none => Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[hits x]

open scoped Classical in
/-- **A step that does not query the input leaves its watched value alone**, pathwise. -/
theorem watchValue_step_ne (leftKeep rightKeep : Bytes → σ → Prop) (target : Bytes)
    (hits : HashOutput → Prop) (input : Bytes) (hne : input ≠ target)
    (state : SplitTapeState σ)
    (step : HashOutput × SplitTapeState σ)
    (hstep : step ∈ support (((noticingSplitTapeRecorder leftKeep rightKeep)
      (Sum.inr input)).run state)) :
    watchValue target hits step.2 = watchValue target hits state := by
  classical
  rw [noticingSplitTapeRecorder_run_inr] at hstep
  obtain ⟨carrier, ⟨leftTape, rightTape⟩, ⟨leftRecord, rightRecord⟩⟩ := state
  set noticed := CacheView.onQuery carrier input with hnoticed
  have hcacheNoticed : CacheView.cacheOf noticed = CacheView.cacheOf carrier :=
    CacheView.cache_onQuery carrier input
  have hupdate : ∀ answer : HashOutput,
      CacheView.cacheOf (CacheView.update noticed input answer) target =
        CacheView.cacheOf carrier target := fun answer => by
    rw [CacheView.cache_update, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hne), hcacheNoticed]
  have hfst : ∀ (record : Record) (answer : HashOutput),
      (target ∈ (record ++ [(input, answer)]).map Prod.fst) ↔ target ∈ record.map Prod.fst :=
    fun record answer => by
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton]
      exact ⟨fun h => h.resolve_right (fun h' => hne h'.symm), Or.inl⟩
  by_cases hleft : CacheView.cacheOf noticed input = none ∧ leftKeep input noticed
  · cases leftTape with
    | nil =>
      rw [splitTapeRecorder_run_left_nil leftKeep rightKeep input noticed rightTape leftRecord
        rightRecord hleft.1 hleft.2] at hstep
      rw [mem_support_bind_iff] at hstep
      obtain ⟨answer, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      subst hpure
      simp only [watchValue, hupdate, hfst]
    | cons head rest =>
      rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed head rest rightTape
        leftRecord rightRecord hleft.1 hleft.2, support_pure, Set.mem_singleton_iff] at hstep
      subst hstep
      simp only [watchValue, hupdate, hfst]
  · by_cases hright : CacheView.cacheOf noticed input = none ∧ rightKeep input noticed
    · have hnotLeft : ¬ leftKeep input noticed := fun h => hleft ⟨hright.1, h⟩
      cases rightTape with
      | nil =>
        rw [splitTapeRecorder_run_right_nil leftKeep rightKeep input noticed leftTape leftRecord
          rightRecord hright.1 hnotLeft hright.2] at hstep
        rw [mem_support_bind_iff] at hstep
        obtain ⟨answer, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        subst hpure
        simp only [watchValue, hupdate, hfst]
      | cons head rest =>
        rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape head rest
          leftRecord rightRecord hright.1 hnotLeft hright.2, support_pure,
          Set.mem_singleton_iff] at hstep
        subst hstep
        simp only [watchValue, hupdate, hfst]
    · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed _ _ hleft hright,
        mem_support_bind_iff] at hstep
      obtain ⟨plain, hplain, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      subst hpure
      have hcarrier : CacheView.cacheOf plain.2 target = CacheView.cacheOf carrier target := by
        rw [plainStep] at hplain
        cases hcached : CacheView.cacheOf noticed input with
        | some cached =>
          rw [hcached, support_pure, Set.mem_singleton_iff] at hplain
          rw [hplain, hcacheNoticed]
        | none =>
          rw [hcached, support_map] at hplain
          obtain ⟨answer, -, hanswer⟩ := hplain
          rw [← hanswer]
          exact hupdate answer
      simp only [watchValue, hcarrier]

open scoped Classical in
/-- **No step raises the watched value in expectation.** -/
theorem watchValue_step_le (leftKeep rightKeep : Bytes → σ → Prop) (target : Bytes)
    (hits : HashOutput → Prop) (queried : OracleWorld.Domain) (state : SplitTapeState σ) :
    ∑' z, Pr{let x ← ((noticingSplitTapeRecorder leftKeep rightKeep) queried).run state}[x = z] *
        watchValue target hits z.2 ≤ watchValue target hits state := by
  classical
  rcases queried with coin | input
  · rw [noticingSplitTapeRecorder_run_inl, splitTapeRecorder_run_inl,
      FiredCoverage.tsum_probOutput_bind]
    calc ∑' value, Pr{let x ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)}[x = value] *
          ∑' z, Pr{let x ← (pure (value, state) : ProbComp _)}[x = z] * watchValue target hits z.2
        = ∑' value, Pr{let x ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)}[x = value] *
            watchValue target hits state :=
          tsum_congr fun value => by rw [FiredCoverage.tsum_probOutput_pure]
      _ ≤ watchValue target hits state := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
  · by_cases hsame : input = target
    swap
    · calc ∑' z, Pr{let x ← ((noticingSplitTapeRecorder leftKeep rightKeep)
              (Sum.inr input)).run state}[x = z] * watchValue target hits z.2
          = ∑' z, Pr{let x ← ((noticingSplitTapeRecorder leftKeep rightKeep)
              (Sum.inr input)).run state}[x = z] * watchValue target hits state := by
            refine tsum_congr fun z => ?_
            by_cases hz : z ∈ support (((noticingSplitTapeRecorder leftKeep rightKeep)
              (Sum.inr input)).run state)
            · rw [watchValue_step_ne leftKeep rightKeep target hits input hsame state z hz]
            · rw [prEvent_eq_zero_of_not_mem_support _ hz, zero_mul, zero_mul]
        _ ≤ watchValue target hits state := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
    subst hsame
    rw [noticingSplitTapeRecorder_run_inr]
    obtain ⟨carrier, ⟨leftTape, rightTape⟩, ⟨leftRecord, rightRecord⟩⟩ := state
    set noticed := CacheView.onQuery carrier input with hnoticed
    have hcacheNoticed : CacheView.cacheOf noticed = CacheView.cacheOf carrier :=
      CacheView.cache_onQuery carrier input
    have hupdate : ∀ answer : HashOutput,
        CacheView.cacheOf (CacheView.update noticed input answer) input = some answer :=
      fun answer => by rw [CacheView.cache_update]; simp
    -- the value at the start
    cases hcached : CacheView.cacheOf carrier input with
    | some cached =>
      -- a hit: nothing moves
      have hnoticedCached : CacheView.cacheOf noticed input = some cached := by
        rw [hcacheNoticed, hcached]
      rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed _ _
          (fun h => by rw [hnoticedCached] at h; exact absurd h.1 (by simp))
          (fun h => by rw [hnoticedCached] at h; exact absurd h.1 (by simp)),
        plainStep, hnoticedCached]
      simp only [pure_bind]
      rw [FiredCoverage.tsum_probOutput_pure]
      simp only [watchValue, hcacheNoticed, hcached]
      exact le_rfl
    | none =>
      have hfresh : CacheView.cacheOf noticed input = none := by rw [hcacheNoticed, hcached]
      have hstart :
          watchValue input hits (carrier, (leftTape, rightTape), (leftRecord, rightRecord)) =
          Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[hits x] := by
        simp only [watchValue, hcached]
      rw [hstart]
      have hrecorded : ∀ (record : Record) (answer : HashOutput),
          input ∈ (record ++ [(input, answer)]).map Prod.fst := fun record answer => by simp
      by_cases hleft : leftKeep input noticed
      · cases leftTape with
        | nil =>
          rw [splitTapeRecorder_run_left_nil leftKeep rightKeep input noticed rightTape leftRecord
            rightRecord hfresh hleft, FiredCoverage.tsum_probOutput_bind]
          refine le_trans (ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl
            (le_of_eq (FiredCoverage.tsum_probOutput_pure _ _))) ?_
          simp only [watchValue, hupdate, hrecorded, not_true_eq_false, false_and, and_false,
            ite_false, mul_zero, tsum_zero]
          exact zero_le
        | cons head rest =>
          rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed head rest
            rightTape leftRecord rightRecord hfresh hleft, FiredCoverage.tsum_probOutput_pure]
          simp only [watchValue, hupdate, hrecorded, not_true_eq_false, false_and, and_false,
            ite_false]
          exact zero_le
      · by_cases hright : rightKeep input noticed
        · cases rightTape with
          | nil =>
            rw [splitTapeRecorder_run_right_nil leftKeep rightKeep input noticed leftTape
              leftRecord rightRecord hfresh hleft hright, FiredCoverage.tsum_probOutput_bind]
            refine le_trans (ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl
              (le_of_eq (FiredCoverage.tsum_probOutput_pure _ _))) ?_
            simp only [watchValue, hupdate, hrecorded, not_true_eq_false, and_false,
              ite_false, mul_zero, tsum_zero]
            exact zero_le
          | cons head rest =>
            rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape head
              rest leftRecord rightRecord hfresh hleft hright, FiredCoverage.tsum_probOutput_pure]
            simp only [watchValue, hupdate, hrecorded, not_true_eq_false, and_false, ite_false]
            exact zero_le
        · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed _ _
            (fun h => hleft h.2) (fun h => hright h.2), plainStep, hfresh,
            map_eq_bind_pure_comp, bind_assoc]
          simp only [Function.comp_apply, pure_bind]
          rw [FiredCoverage.tsum_probOutput_bind]
          refine le_trans (le_of_eq (tsum_congr fun answer =>
            congrArg _ (FiredCoverage.tsum_probOutput_pure _ _))) ?_
          refine le_trans (ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl
            (show watchValue input hits (CacheView.update noticed input answer,
                (leftTape, rightTape), (leftRecord, rightRecord)) ≤
              (if hits answer then 1 else 0) from ?_)) ?_
          · unfold watchValue
            rw [hupdate]
            dsimp only
            split_ifs with h1 h2 h2
            · exact le_rfl
            · exact absurd h1.1 h2
            · exact zero_le
            · exact le_rfl
          · exact le_of_eq (FiredCoverage.tsum_ite_eq_probEvent _ _)

/-! ## The watched value across the fused phase

A fused step is one run of the tape recorder on a sub-computation, opened and closed by brackets
that leave the cache and the recordings alone. So the one-step bound at the fused handler is
`expect_run_bind_le` at the recorder, and the whole phase is `expect_run_le` again. -/

/-- A bracket on the carrier that leaves its cache alone keeps the watched value. -/
theorem watchValue_onCarrierTape (target : Bytes) (hits : HashOutput → Prop) (f : σ → σ)
    (hf : ∀ carrier : σ, CacheView.cacheOf (f carrier) = CacheView.cacheOf carrier)
    (state : SplitTapeState σ) :
    watchValue target hits (onCarrierTape f state) = watchValue target hits state := by
  simp only [watchValue, onCarrierTape, hf]
  rfl

variable {ω : Type} [Monoid ω]

/-! ## A tape run is a run of the shared oracle

With both blocks fixed the tape recorder still answers each query as the shared oracle could: a
block answer is a value a fresh draw might have returned. So a supported tape run, read at its
cache, is a supported run of `KeygenUniform.rom` — which is what lets the signer's and the
verifier's cache provenance, stated at the shared oracle, be read at a tape run. -/

open scoped Classical in
/-- **One tape step is a step of the shared oracle**, at the view's cache. -/
theorem tape_step_rom (leftKeep rightKeep : Bytes → σ → Prop) (queried : OracleWorld.Domain)
    (state : SplitTapeState σ) (step : OracleWorld.Range queried × SplitTapeState σ)
    (hstep : step ∈ support (((noticingSplitTapeRecorder leftKeep rightKeep) queried).run
      state)) :
    (step.1, CacheView.cacheOf step.2.1) ∈
      support ((KeygenUniform.rom queried).run (CacheView.cacheOf state.1)) := by
  classical
  rcases queried with coin | input
  · rw [noticingSplitTapeRecorder_run_inl, splitTapeRecorder_run_inl, mem_support_bind_iff]
      at hstep
    obtain ⟨value, hvalue, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [DigestTape.rom_run_inl, mem_support_bind_iff]
    exact ⟨value, hvalue, by rw [support_pure, Set.mem_singleton_iff, hpure]⟩
  · rw [noticingSplitTapeRecorder_run_inr] at hstep
    obtain ⟨carrier, ⟨leftTape, rightTape⟩, ⟨leftRecord, rightRecord⟩⟩ := state
    set noticed := CacheView.onQuery carrier input with hnoticed
    have hcacheNoticed : CacheView.cacheOf noticed = CacheView.cacheOf carrier :=
      CacheView.cache_onQuery carrier input
    have hfreshStep : ∀ answer : HashOutput,
        CacheView.cacheOf carrier input = none →
        ((answer : OracleWorld.Range (Sum.inr input)),
          CacheView.cacheOf (CacheView.update noticed input answer)) ∈
          support ((KeygenUniform.rom (Sum.inr input)).run (CacheView.cacheOf carrier)) := by
      intro answer hnone
      rw [CoverageCount.rom_run_inr_none input _ hnone, support_map]
      refine ⟨answer, (mem_support_uniformSample (x := answer)), ?_⟩
      rw [CacheView.cache_update, hcacheNoticed]
    by_cases hleft : CacheView.cacheOf noticed input = none ∧ leftKeep input noticed
    · have hnone : CacheView.cacheOf carrier input = none := by rw [← hcacheNoticed]; exact hleft.1
      cases leftTape with
      | nil =>
        rw [splitTapeRecorder_run_left_nil leftKeep rightKeep input noticed rightTape leftRecord
          rightRecord hleft.1 hleft.2, mem_support_bind_iff] at hstep
        obtain ⟨answer, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        subst hpure
        exact hfreshStep answer hnone
      | cons head rest =>
        rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed head rest rightTape
          leftRecord rightRecord hleft.1 hleft.2, support_pure, Set.mem_singleton_iff] at hstep
        subst hstep
        exact hfreshStep head hnone
    · by_cases hright : CacheView.cacheOf noticed input = none ∧ rightKeep input noticed
      · have hnone : CacheView.cacheOf carrier input = none := by
          rw [← hcacheNoticed]; exact hright.1
        have hnotLeft : ¬ leftKeep input noticed := fun h => hleft ⟨hright.1, h⟩
        cases rightTape with
        | nil =>
          rw [splitTapeRecorder_run_right_nil leftKeep rightKeep input noticed leftTape
            leftRecord rightRecord hright.1 hnotLeft hright.2, mem_support_bind_iff] at hstep
          obtain ⟨answer, -, hpure⟩ := hstep
          rw [support_pure, Set.mem_singleton_iff] at hpure
          subst hpure
          exact hfreshStep answer hnone
        | cons head rest =>
          rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape head rest
            leftRecord rightRecord hright.1 hnotLeft hright.2, support_pure,
            Set.mem_singleton_iff] at hstep
          subst hstep
          exact hfreshStep head hnone
      · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed _ _ hleft hright,
          mem_support_bind_iff] at hstep
        obtain ⟨plain, hplain, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        subst hpure
        rw [plainStep] at hplain
        cases hcached : CacheView.cacheOf noticed input with
        | some cached =>
          rw [hcached, support_pure, Set.mem_singleton_iff] at hplain
          rw [hplain]
          have hcarrier : CacheView.cacheOf carrier input = some cached := by
            rw [← hcacheNoticed]; exact hcached
          rw [CoverageCount.rom_run_inr_some input _ cached hcarrier, support_pure,
            Set.mem_singleton_iff, hcacheNoticed]
        | none =>
          rw [hcached, support_map] at hplain
          obtain ⟨answer, -, hanswer⟩ := hplain
          rw [← hanswer]
          exact hfreshStep answer (by rw [← hcacheNoticed]; exact hcached)

/-- **A supported tape run is a supported run of the shared oracle**, at the view's cache. -/
theorem tape_run_rom (leftKeep rightKeep : Bytes → σ → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (state : SplitTapeState σ)
    (result : α × SplitTapeState σ)
    (hmem : result ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
      computation).run state)) :
    (result.1, CacheView.cacheOf result.2.1) ∈
      support ((simulateQ KeygenUniform.rom computation).run (CacheView.cacheOf state.1)) := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, hmem]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    exact ⟨(step.1, CacheView.cacheOf step.2.1),
      tape_step_rom leftKeep rightKeep queried state step hstep, ih step.1 step.2 result hrest⟩

end SlhDsaSecurity.TapeWatch
