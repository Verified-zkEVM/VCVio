/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.TapeWatch
import VCVio.OracleComp.EvalDist.Sum

/-!
# A watched value that is paid for as it is earned

`TapeWatch.expect_run_le` bounds a run by the value it starts from. The thinning the
second-order coverage charge needs is not of that shape: the probability that a target cell is
reached **and** fires has to come out below `2 ^ -128` times the probability that it is reached,
and before the cell is reached there is nothing to watch.

So the value is paid for as it is earned. Beside the watched value `value` runs a **bound**
`bound`, which jumps when the cell is reached and never moves otherwise; a step may raise
`value` by no more, in expectation, than it raises `bound`:

    E[value'] + bound ≤ value + E[bound'].

Over a run this telescopes to `E[value_end] + bound_start ≤ value_start + E[bound_end]`, and with
both zero at the start that is the thinning. The cancellation needs `bound` finite, which is why
it is capped at one; `value` is never cancelled and may be anything.

The second half of the file is the step structure the carrier's instance reads: one query of the
tape recorder is a hit, a left filing, a right filing or a plain draw
(`tapeStep_inr_cases`), and a product of two watched values at distinct answers is still a
supermartingale (`watchPair_step_le`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.SignedWatch

variable {α β γ : Type}

open DigestTape TapeFactor NoticingTape RecorderView PhaseFusion FusedTape TapeWatch

/-! ## The compensated supermartingale -/

/-- **An invariant of every step is an invariant of every run.** -/
theorem run_invariant {ι : Type} {spec : OracleSpec ι} {S : Type}
    (impl : QueryImpl spec (StateT S ProbComp)) (Inv : S → Prop)
    (hinv : ∀ (queried : spec.Domain) (state : S), Inv state →
      ∀ z ∈ support ((impl queried).run state), Inv z.2)
    {α : Type} (computation : OracleComp spec α) (state : S) (hstate : Inv state) :
    ∀ z ∈ support ((simulateQ impl computation).run state), Inv z.2 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
    intro z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hstate
  | query_bind queried next ih =>
    intro z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact ih step.1 step.2 (hinv queried state hstate step hstep) z hrest

/-- The expected bound is at most one when the bound is. -/
theorem tsum_bound_le_one {S β : Type} (computation : ProbComp (β × S)) (bound : S → ℝ≥0∞)
    (hbound : ∀ state, bound state ≤ 1) :
    ∑' z, Pr{let x ← computation}[x = z] * bound z.2 ≤ 1 :=
  le_trans (ENNReal.tsum_le_tsum fun z => mul_le_of_le_one_right' (hbound z.2))
    (OracleComp.tsum_prEvent_le_one _)

/-- **The cancellation**, isolated: two inequalities that share a finite middle term. -/
theorem add_le_of_two {a b p q v c : ℝ≥0∞} (hb : b ≠ ⊤) (hfirst : a + b ≤ p + q)
    (hsecond : p + c ≤ v + b) : a + c ≤ v + q := by
  have h : (a + c) + b ≤ (v + q) + b :=
    calc (a + c) + b = (a + b) + c := by ring
      _ ≤ (p + q) + c := add_le_add hfirst le_rfl
      _ = (p + c) + q := by ring
      _ ≤ (v + b) + q := add_le_add hsecond le_rfl
      _ = (v + q) + b := by ring
  exact (ENNReal.add_le_add_iff_right hb).mp h

/-- The weighted sum of a pointwise inequality, kept on the support. -/
theorem tsum_add_le_of_support {β : Type} (computation : ProbComp β)
    (left right : β → ℝ≥0∞) (outerLeft outerRight : β → ℝ≥0∞)
    (h : ∀ z ∈ support computation, left z + outerLeft z ≤ right z + outerRight z) :
    (∑' z, Pr{let x ← computation}[x = z] * left z) +
        ∑' z, Pr{let x ← computation}[x = z] * outerLeft z ≤
      (∑' z, Pr{let x ← computation}[x = z] * right z) +
        ∑' z, Pr{let x ← computation}[x = z] * outerRight z := by
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : z ∈ support computation
  · rw [← mul_add, ← mul_add]
    exact mul_le_mul' le_rfl (h z hz)
  · rw [(prEvent_eq_zero_of_not_mem_support _) hz]
    simp

/-- **A compensated supermartingale survives a run.** -/
theorem expect_run_signed_le {ι : Type} {spec : OracleSpec ι} {S : Type}
    (impl : QueryImpl spec (StateT S ProbComp)) (Inv : S → Prop) (value bound : S → ℝ≥0∞)
    (hbound : ∀ state, bound state ≤ 1)
    (hinv : ∀ (queried : spec.Domain) (state : S), Inv state →
      ∀ z ∈ support ((impl queried).run state), Inv z.2)
    (hstep : ∀ (queried : spec.Domain) (state : S), Inv state →
      (∑' z, Pr{let x ← (impl queried).run state}[x = z] * value z.2) + bound state ≤
        value state + ∑' z, Pr{let x ← (impl queried).run state}[x = z] * bound z.2)
    {α : Type} (computation : OracleComp spec α) (state : S) (hstate : Inv state) :
    (∑' z, Pr{let x ← (simulateQ impl computation).run state}[x = z] * value z.2) + bound state ≤
      value state +
        ∑' z, Pr{let x ← (simulateQ impl computation).run state}[x = z] * bound z.2 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result =>
    rw [simulateQ_pure, StateT.run_pure, FiredCoverage.tsum_probOutput_pure,
      FiredCoverage.tsum_probOutput_pure]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      FiredCoverage.tsum_probOutput_bind, FiredCoverage.tsum_probOutput_bind]
    refine add_le_of_two
      (b := ∑' step, Pr{let x ← (impl queried).run state}[x = step] * bound step.2)
      (p := ∑' step, Pr{let x ← (impl queried).run state}[x = step] * value step.2)
      (ne_top_of_le_ne_top one_ne_top (tsum_bound_le_one _ bound hbound)) ?_
      (hstep queried state hstate)
    exact tsum_add_le_of_support _ _ _ _ _ fun step hmem =>
      ih step.1 step.2 (hinv queried state hstate step hmem)

/-- **And a run followed by a continuation that keeps the same accounting.** -/
theorem expect_bind_signed_le {ι : Type} {spec : OracleSpec ι} {S γ : Type}
    (impl : QueryImpl spec (StateT S ProbComp)) (Inv : S → Prop) (value bound : S → ℝ≥0∞)
    (hbound : ∀ state, bound state ≤ 1)
    (hinv : ∀ (queried : spec.Domain) (state : S), Inv state →
      ∀ z ∈ support ((impl queried).run state), Inv z.2)
    (hstep : ∀ (queried : spec.Domain) (state : S), Inv state →
      (∑' z, Pr{let x ← (impl queried).run state}[x = z] * value z.2) + bound state ≤
        value state + ∑' z, Pr{let x ← (impl queried).run state}[x = z] * bound z.2)
    {α : Type} (computation : OracleComp spec α) (state : S) (hstate : Inv state)
    (cont : α × S → ProbComp γ) (final finalBound : γ → ℝ≥0∞)
    (hcont : ∀ z ∈ support ((simulateQ impl computation).run state),
      (∑' w, Pr{let x ← cont z}[x = w] * final w) + bound z.2 ≤
        value z.2 + ∑' w, Pr{let x ← cont z}[x = w] * finalBound w) :
    (∑' w, Pr{let x ← (simulateQ impl computation).run state >>= cont}[x = w] * final w) +
        bound state ≤
      value state +
        ∑' w, Pr{let x ← (simulateQ impl computation).run state >>= cont}[x = w] *
          finalBound w := by
  rw [FiredCoverage.tsum_probOutput_bind, FiredCoverage.tsum_probOutput_bind]
  refine add_le_of_two
    (b := ∑' z, Pr{let x ← (simulateQ impl computation).run state}[x = z] * bound z.2)
    (p := ∑' z, Pr{let x ← (simulateQ impl computation).run state}[x = z] * value z.2)
    (ne_top_of_le_ne_top one_ne_top (tsum_bound_le_one _ bound hbound)) ?_
    (expect_run_signed_le impl Inv value bound hbound hinv hstep computation state hstate)
  exact tsum_add_le_of_support _ _ _ _ _ hcont

/-- **At a final `pure`**, the accounting is a pointwise inequality. -/
theorem pure_signed_le {S γ : Type} (point : γ) (state : S) (value bound : S → ℝ≥0∞)
    (final finalBound : γ → ℝ≥0∞)
    (h : final point + bound state ≤ value state + finalBound point) :
    (∑' w, Pr{let x ← (pure point : ProbComp γ)}[x = w] * final w) + bound state ≤
      value state + ∑' w, Pr{let x ← (pure point : ProbComp γ)}[x = w] * finalBound w := by
  rw [FiredCoverage.tsum_probOutput_pure, FiredCoverage.tsum_probOutput_pure]
  exact h

/-! ## One query of the tape recorder, by cases -/

variable {σ : Type} [CacheView σ]

open scoped Classical in
/-- **One hash query of the tape recorder is one of four steps**: a hit, which only notices; a
left filing; a right filing; or a plain draw. Every filing and every draw happens at an input
the noticed carrier did not hold, and installs exactly the answer returned. -/
theorem tapeStep_inr_cases (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : SplitTapeState σ) (step : HashOutput × SplitTapeState σ)
    (hstep : step ∈ support (((noticingSplitTapeRecorder leftKeep rightKeep)
      (Sum.inr input)).run state)) :
    (CacheView.cacheOf (CacheView.onQuery state.1 input) input = some step.1 ∧
        step.2 = (CacheView.onQuery state.1 input, state.2)) ∨
      (CacheView.cacheOf (CacheView.onQuery state.1 input) input = none ∧
        leftKeep input (CacheView.onQuery state.1 input) ∧
        step.2 = (CacheView.update (CacheView.onQuery state.1 input) input step.1,
          (state.2.1.1.tail, state.2.1.2), (state.2.2.1 ++ [(input, step.1)], state.2.2.2))) ∨
      (CacheView.cacheOf (CacheView.onQuery state.1 input) input = none ∧
        ¬ leftKeep input (CacheView.onQuery state.1 input) ∧
        rightKeep input (CacheView.onQuery state.1 input) ∧
        step.2 = (CacheView.update (CacheView.onQuery state.1 input) input step.1,
          (state.2.1.1, state.2.1.2.tail), (state.2.2.1, state.2.2.2 ++ [(input, step.1)]))) ∨
      (CacheView.cacheOf (CacheView.onQuery state.1 input) input = none ∧
        ¬ leftKeep input (CacheView.onQuery state.1 input) ∧
        ¬ rightKeep input (CacheView.onQuery state.1 input) ∧
        step.2 = (CacheView.update (CacheView.onQuery state.1 input) input step.1,
          state.2.1, state.2.2)) := by
  classical
  rw [noticingSplitTapeRecorder_run_inr] at hstep
  obtain ⟨carrier, ⟨leftTape, rightTape⟩, ⟨leftRecord, rightRecord⟩⟩ := state
  dsimp only at hstep ⊢
  set noticed := CacheView.onQuery carrier input with hnoticed
  by_cases hleft : CacheView.cacheOf noticed input = none ∧ leftKeep input noticed
  · refine Or.inr (Or.inl ⟨hleft.1, hleft.2, ?_⟩)
    cases leftTape with
    | nil =>
      rw [splitTapeRecorder_run_left_nil leftKeep rightKeep input noticed rightTape leftRecord
        rightRecord hleft.1 hleft.2, mem_support_bind_iff] at hstep
      obtain ⟨answer, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      subst hpure
      rfl
    | cons head rest =>
      rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed head rest rightTape
        leftRecord rightRecord hleft.1 hleft.2, support_pure, Set.mem_singleton_iff] at hstep
      subst hstep
      rfl
  · by_cases hright : CacheView.cacheOf noticed input = none ∧ rightKeep input noticed
    · have hnotLeft : ¬ leftKeep input noticed := fun h => hleft ⟨hright.1, h⟩
      refine Or.inr (Or.inr (Or.inl ⟨hright.1, hnotLeft, hright.2, ?_⟩))
      cases rightTape with
      | nil =>
        rw [splitTapeRecorder_run_right_nil leftKeep rightKeep input noticed leftTape
          leftRecord rightRecord hright.1 hnotLeft hright.2, mem_support_bind_iff] at hstep
        obtain ⟨answer, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        subst hpure
        rfl
      | cons head rest =>
        rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape head rest
          leftRecord rightRecord hright.1 hnotLeft hright.2, support_pure,
          Set.mem_singleton_iff] at hstep
        subst hstep
        rfl
    · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed _ _ hleft hright,
        mem_support_bind_iff] at hstep
      obtain ⟨plain, hplain, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      subst hpure
      rw [plainStep] at hplain
      cases hcached : CacheView.cacheOf noticed input with
      | some cached =>
        rw [hcached, support_pure, Set.mem_singleton_iff] at hplain
        refine Or.inl ⟨?_, ?_⟩
        · rw [hplain]
        · rw [hplain]
      | none =>
        rw [hcached, support_map] at hplain
        obtain ⟨answer, -, hanswer⟩ := hplain
        refine Or.inr (Or.inr (Or.inr ⟨rfl, fun h => hleft ⟨hcached, h⟩,
          fun h => hright ⟨hcached, h⟩, ?_⟩))
        rw [← hanswer]

/-- **A coin leaves the state alone.** -/
theorem tapeStep_inl (leftKeep rightKeep : Bytes → σ → Prop) (coin : unifSpec.Domain)
    (state : SplitTapeState σ) (step : OracleWorld.Range (Sum.inl coin) × SplitTapeState σ)
    (hstep : step ∈ support (((noticingSplitTapeRecorder leftKeep rightKeep)
      (Sum.inl coin)).run state)) :
    step.2 = state := by
  rw [noticingSplitTapeRecorder_run_inl, splitTapeRecorder_run_inl, mem_support_bind_iff]
    at hstep
  obtain ⟨value, -, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]

/-- **After a hash query, the queried input holds the answer returned.** -/
theorem tapeStep_cache_self (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : SplitTapeState σ) (step : HashOutput × SplitTapeState σ)
    (hstep : step ∈ support (((noticingSplitTapeRecorder leftKeep rightKeep)
      (Sum.inr input)).run state)) :
    CacheView.cacheOf step.2.1 input = some step.1 := by
  rcases tapeStep_inr_cases leftKeep rightKeep input state step hstep with
    ⟨hhit, hstate⟩ | ⟨-, -, hstate⟩ | ⟨-, -, -, hstate⟩ | ⟨-, -, -, hstate⟩
  · rw [hstate]; exact hhit
  all_goals rw [hstate]; simp [CacheView.cache_update]

/-- **And nothing else moves in the cache.** -/
theorem tapeStep_cache_ne (leftKeep rightKeep : Bytes → σ → Prop) (input other : Bytes)
    (hne : other ≠ input)
    (state : SplitTapeState σ) (step : HashOutput × SplitTapeState σ)
    (hstep : step ∈ support (((noticingSplitTapeRecorder leftKeep rightKeep)
      (Sum.inr input)).run state)) :
    CacheView.cacheOf step.2.1 other = CacheView.cacheOf state.1 other := by
  have hnoticed : CacheView.cacheOf (CacheView.onQuery state.1 input) =
      CacheView.cacheOf state.1 := CacheView.cache_onQuery state.1 input
  rcases tapeStep_inr_cases leftKeep rightKeep input state step hstep with
    ⟨-, hstate⟩ | ⟨-, -, hstate⟩ | ⟨-, -, -, hstate⟩ | ⟨-, -, -, hstate⟩ <;>
    rw [hstate] <;>
    simp [CacheView.cache_update, QueryCache.cacheQuery_of_ne _ _ hne, hnoticed]

/-- **A cached input stays cached at the same answer, and the step is a hit if it is the one
queried.** -/
theorem tapeStep_cache_persists (leftKeep rightKeep : Bytes → σ → Prop) (input other : Bytes)
    (answer : HashOutput) (state : SplitTapeState σ)
    (hcached : CacheView.cacheOf state.1 other = some answer)
    (step : HashOutput × SplitTapeState σ)
    (hstep : step ∈ support (((noticingSplitTapeRecorder leftKeep rightKeep)
      (Sum.inr input)).run state)) :
    CacheView.cacheOf step.2.1 other = some answer := by
  by_cases hsame : other = input
  · subst hsame
    have hnoticed : CacheView.cacheOf (CacheView.onQuery state.1 other) other = some answer := by
      rw [CacheView.cache_onQuery]; exact hcached
    rcases tapeStep_inr_cases leftKeep rightKeep other state step hstep with
      ⟨hhit, hstate⟩ | ⟨hnone, -⟩ | ⟨hnone, -⟩ | ⟨hnone, -⟩
    · rw [hstate, CacheView.cache_onQuery, hcached]
    all_goals rw [hnoticed] at hnone; exact absurd hnone (by simp)
  · rw [tapeStep_cache_ne leftKeep rightKeep input other hsame state step hstep]
    exact hcached

/-! ## Two watched inputs at once -/

open scoped Classical in
/-- **A step that hits leaves every watched value alone**: the cache and both recordings are
what they were. -/
theorem watchValue_step_cached (leftKeep rightKeep : Bytes → σ → Prop) (target : Bytes)
    (hits : HashOutput → Prop) (input : Bytes) (state : SplitTapeState σ)
    (hcached : CacheView.cacheOf state.1 input ≠ none)
    (step : HashOutput × SplitTapeState σ)
    (hstep : step ∈ support (((noticingSplitTapeRecorder leftKeep rightKeep)
      (Sum.inr input)).run state)) :
    watchValue target hits step.2 = watchValue target hits state := by
  have hnoticed : CacheView.cacheOf (CacheView.onQuery state.1 input) =
      CacheView.cacheOf state.1 := CacheView.cache_onQuery state.1 input
  rcases tapeStep_inr_cases leftKeep rightKeep input state step hstep with
    ⟨-, hstate⟩ | ⟨hnone, -⟩ | ⟨hnone, -⟩ | ⟨hnone, -⟩
  · rw [hstate]
    simp only [watchValue, hnoticed]
  all_goals rw [hnoticed] at hnone; exact absurd hnone hcached

open scoped Classical in
/-- **A step that draws a watched input fresh leaves it cached at the answer returned**, and the
watched value there is at most the indicator of that answer. -/
theorem watchValue_le_of_cache (target : Bytes) (hits : HashOutput → Prop)
    (state : SplitTapeState σ) (answer : HashOutput)
    (hcache : CacheView.cacheOf state.1 target = some answer) :
    watchValue target hits state ≤ if hits answer then 1 else 0 := by
  unfold watchValue
  rw [hcache]
  dsimp only
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd h1.1 h2
  · exact zero_le
  · exact le_rfl

open scoped Classical in
/-- **The product of two watched values is a supermartingale**, when the two are at different
inputs or ask for disjoint answers. One query moves at most one of them; when it is the same
input for both, a fresh answer cannot land in both sets and a block answer files it. -/
theorem watchPair_step_le (leftKeep rightKeep : Bytes → σ → Prop) (first second : Bytes)
    (firstHits secondHits : HashOutput → Prop)
    (hdisjoint : first = second → ∀ answer, firstHits answer → secondHits answer → False)
    (queried : OracleWorld.Domain) (state : SplitTapeState σ) :
    ∑' z, Pr{let x ← ((noticingSplitTapeRecorder leftKeep rightKeep) queried).run state}[x = z] *
        (watchValue first firstHits z.2 * watchValue second secondHits z.2) ≤
      watchValue first firstHits state * watchValue second secondHits state := by
  classical
  set step := ((noticingSplitTapeRecorder leftKeep rightKeep) queried).run state with hstepDef
  have hconst : ∀ value : ℝ≥0∞, ∑' z, Pr{let x ← step}[x = z] * value ≤ value := fun value => by
    rw [ENNReal.tsum_mul_right]
    exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
  rcases queried with coin | input
  · refine le_trans (le_of_eq (tsum_congr fun z => ?_)) (hconst _)
    by_cases hz : z ∈ support step
    · rw [tapeStep_inl leftKeep rightKeep coin state z hz]
    · rw [prEvent_eq_zero_of_not_mem_support _ hz, zero_mul, zero_mul]
  · by_cases hfirst : input = first
    · by_cases hsecond : input = second
      · -- one input, two disjoint sets
        subst hfirst
        by_cases hcached : CacheView.cacheOf state.1 input = none
        · refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun z => ?_)) zero_le
          by_cases hz : z ∈ support step
          · have hself := tapeStep_cache_self leftKeep rightKeep input state z hz
            have hle1 := watchValue_le_of_cache input firstHits z.2 z.1 hself
            have hle2 := watchValue_le_of_cache second secondHits z.2 z.1 (hsecond ▸ hself)
            by_cases h1 : firstHits z.1
            · by_cases h2 : secondHits z.1
              · exact absurd (hdisjoint hsecond z.1 h1 h2) id
              · rw [ite_eq_right_iff.mpr (fun h => absurd h h2)] at hle2
                rw [nonpos_iff_eq_zero.mp hle2, mul_zero, mul_zero]
            · rw [ite_eq_right_iff.mpr (fun h => absurd h h1)] at hle1
              rw [nonpos_iff_eq_zero.mp hle1, zero_mul, mul_zero]
          · rw [prEvent_eq_zero_of_not_mem_support _ hz, zero_mul]
        · refine le_trans (le_of_eq (tsum_congr fun z => ?_)) (hconst _)
          by_cases hz : z ∈ support step
          · rw [watchValue_step_cached leftKeep rightKeep input firstHits input state hcached z hz,
              watchValue_step_cached leftKeep rightKeep second secondHits input state hcached z
                hz]
          · rw [prEvent_eq_zero_of_not_mem_support _ hz, zero_mul, zero_mul]
      · -- only the first moves
        calc ∑' z, Pr{let x ← step}[x = z] *
              (watchValue first firstHits z.2 * watchValue second secondHits z.2)
            = ∑' z, Pr{let x ← step}[x = z] * watchValue first firstHits z.2 *
                watchValue second secondHits state := by
              refine tsum_congr fun z => ?_
              by_cases hz : z ∈ support step
              · rw [watchValue_step_ne leftKeep rightKeep second secondHits input hsecond state z
                  hz, mul_assoc]
              · rw [prEvent_eq_zero_of_not_mem_support _ hz, zero_mul, zero_mul, zero_mul]
          _ ≤ watchValue first firstHits state * watchValue second secondHits state := by
              rw [ENNReal.tsum_mul_right]
              exact mul_le_mul' (watchValue_step_le leftKeep rightKeep first firstHits _ state)
                le_rfl
    · by_cases hsecond : input = second
      · -- only the second moves
        calc ∑' z, Pr{let x ← step}[x = z] *
              (watchValue first firstHits z.2 * watchValue second secondHits z.2)
            = ∑' z, Pr{let x ← step}[x = z] * watchValue second secondHits z.2 *
                watchValue first firstHits state := by
              refine tsum_congr fun z => ?_
              by_cases hz : z ∈ support step
              · rw [watchValue_step_ne leftKeep rightKeep first firstHits input hfirst state z
                  hz, mul_assoc, mul_comm (watchValue first firstHits state)]
              · rw [prEvent_eq_zero_of_not_mem_support _ hz, zero_mul, zero_mul, zero_mul]
          _ ≤ watchValue first firstHits state * watchValue second secondHits state := by
              rw [ENNReal.tsum_mul_right, mul_comm]
              exact mul_le_mul' le_rfl
                (watchValue_step_le leftKeep rightKeep second secondHits _ state)
      · -- neither moves
        refine le_trans (le_of_eq (tsum_congr fun z => ?_)) (hconst _)
        by_cases hz : z ∈ support step
        · rw [watchValue_step_ne leftKeep rightKeep first firstHits input hfirst state z hz,
            watchValue_step_ne leftKeep rightKeep second secondHits input hsecond state z hz]
        · rw [prEvent_eq_zero_of_not_mem_support _ hz, zero_mul, zero_mul]

/-! ## Any recorder supermartingale, across the fused phase -/

variable {ω : Type} [Monoid ω]

/-- **A value no recorder step raises, and the brackets keep, no fused step raises.** -/
theorem fused_step_le (leftKeep rightKeep : Bytes → σ → Prop)
    (inner : QueryImpl (OracleWorld + Security.SigningSpec)
      (WriterT ω (StateT Security.SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ) (value : SplitTapeState σ → ℝ≥0∞)
    (hstep : ∀ (queried : OracleWorld.Domain) (state : SplitTapeState σ),
      ∑' z, Pr{let x ← ((noticingSplitTapeRecorder leftKeep rightKeep) queried).run state}[x = z] *
        value z.2 ≤ value state)
    (hbefore : ∀ (request : Message) (state : SplitTapeState σ),
      value (onCarrierTape (before request) state) = value state)
    (hafter : ∀ state : SplitTapeState σ, value (onCarrierTape afterMap state) = value state)
    (queried : (OracleWorld + Security.SigningSpec).Domain)
    (state : ω × Security.SigningLog × SplitTapeState σ) :
    ∑' z, Pr{let x ← (((fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
        (fun request => onCarrierTape (before request)) (onCarrierTape afterMap))
        queried).run state)}[x = z] * value z.2.2.2 ≤ value state.2.2 := by
  rcases queried with world | request
  · rw [FusedTape.fuseServing_run_inl]
    refine expect_run_bind_le _ value hstep _ state.2.2 _
      (fun w : (OracleWorld + Security.SigningSpec).Range (Sum.inl world) × ω ×
        Security.SigningLog × SplitTapeState σ => value w.2.2.2) fun z => ?_
    rw [FiredCoverage.tsum_probOutput_pure]
  · rw [FusedTape.fuseServing_run_inr]
    refine le_trans (expect_run_bind_le _ value hstep _
      (onCarrierTape (before request) state.2.2) _
      (fun w : (OracleWorld + Security.SigningSpec).Range (Sum.inr request) × ω ×
        Security.SigningLog × SplitTapeState σ => value w.2.2.2)
      fun z => ?_) (le_of_eq (hbefore request state.2.2))
    rw [FiredCoverage.tsum_probOutput_pure, hafter]

/-- The pair's value is kept by a bracket that keeps the cache. -/
theorem watchPair_onCarrierTape (first second : Bytes) (firstHits secondHits : HashOutput → Prop)
    (f : σ → σ) (hf : ∀ carrier : σ, CacheView.cacheOf (f carrier) = CacheView.cacheOf carrier)
    (state : SplitTapeState σ) :
    watchValue first firstHits (onCarrierTape f state) *
        watchValue second secondHits (onCarrierTape f state) =
      watchValue first firstHits state * watchValue second secondHits state := by
  rw [watchValue_onCarrierTape _ _ _ hf, watchValue_onCarrierTape _ _ _ hf]

end SlhDsaSecurity.SignedWatch
