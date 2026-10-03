/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-!
# Fresh-query API checks

Ordinary imports support events that depend on unqueried cells and queries with unequal answer
types. The examples protect those interfaces and repeated-key behavior; the security result is
the general theorem in the library.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace FreshQueryConsumer

/-- The queried target is compared with an ancestor that is never queried. -/
def target : OracleComp (Bool →ₒ Bool) Bool := liftM ((Bool →ₒ Bool).query true)

/-- A target collision whose other table cell is absent from the visible query history. -/
def bad (t : Bool) (g : Bool → Bool) : Prop := t = true ∧ g true = g false

/-- The fresh-query theorem protects an event depending on an unqueried ancestor. -/
theorem latent_ancestor_bound :
    Pr{let g ← $ᵗ (Bool → Bool)}[∃ q ∈ tableQueryLog target g, bad q.1 g] ≤ (2 : ℝ≥0∞)⁻¹ := by
  classical
  have local_bound : ∀ t g, Pr{let u ← $ᵗ Bool}[bad t (Function.update g t u)] ≤
      (2 : ℝ≥0∞)⁻¹ := by
    intro t g
    cases t with
    | false => simp [bad]
    | true =>
        simp only [bad, Function.update_self, true_and]
        let : MeasurableSpace Bool := ⊤
        rw [prEvent_eq_evalDist_of_discrete, SampleableType.evalDist_uniformSample]
        change (ProbabilityTheory.uniformOn Set.univ : Measure Bool) {g false} ≤ _
        rw [ProbabilityTheory.uniformOn_univ_apply_singleton]
        norm_num
  simpa only [Nat.cast_one, one_mul] using
    prEvent_tableQueryLog_bad_le target 1 (by
      change IsTotalQueryBound (liftM ((Bool →ₒ Bool).query true) >>= pure) 1
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨by decide, fun _ => trivial⟩) bad _ local_bound

end FreshQueryConsumer

namespace FreshQueryConsumer

/-- Two oracle coordinates have different answer types. -/
@[expose] def Answer : Bool → Type
  | false => Bool
  | true => Fin 3

instance (b : Bool) : Finite (Answer b) := by
  cases b with
  | false => exact inferInstanceAs (Finite Bool)
  | true => exact inferInstanceAs (Finite (Fin 3))

instance (b : Bool) : Nonempty (Answer b) := by
  cases b with
  | false => exact inferInstanceAs (Nonempty Bool)
  | true => exact inferInstanceAs (Nonempty (Fin 3))

-- This proof-only dependent sampler must not build an enumeration at module initialization.
noncomputable instance (b : Bool) : SampleableType (Answer b) :=
  letI : Fintype (Answer b) := Fintype.ofFinite _
  SampleableType.ofFintype _

/-- Read a later coordinate, then an earlier one, then repeat the first query. -/
@[expose] def differentAnswers : OracleComp (ofFn Answer) (Fin 3 × Bool × Fin 3) := do
  let first ← liftM ((ofFn Answer).query true)
  let ancestor ← liftM ((ofFn Answer).query false)
  let repeated ← liftM ((ofFn Answer).query true)
  pure (first, ancestor, repeated)

-- Ordinary imports expose dependent query logs, retaining repeats and their actual answers.
example (g : ∀ b, Answer b) :
    tableQueryLog differentAnswers g = [⟨true, g true⟩, ⟨false, g false⟩, ⟨true, g true⟩] := by
  simp only [differentAnswers, tableQueryLog_query_bind, tableQueryLog_pure]

-- Output and log interfaces agree on the repeated dependent coordinate.
example (g : ∀ b, Answer b) :
    evalWithAnswerFn (QueryImpl.ofFn g) differentAnswers = (g true, g false, g true) := rfl

end FreshQueryConsumer

namespace FreshQueryConsumer

/-- A genuinely infinite key type, an adaptive second key, and a repeated first key. -/
@[expose] def infiniteKeys : OracleComp (ℕ →ₒ Bool) (Bool × Bool) := do
  let first ← liftM ((ℕ →ₒ Bool).query 7)
  let _ ← liftM ((ℕ →ₒ Bool).query (if first then 8 else 9))
  let repeated ← liftM ((ℕ →ₒ Bool).query 7)
  pure (first, repeated)

-- This consumer cannot elaborate through a theorem requiring a finite key domain or a
-- uniformly sampled complete infinite table. It also checks actual lazy repeated-key semantics.
theorem infiniteKeys_consistent :
    Pr{let result ← (simulateQ randomOracle infiniteKeys).run' ∅}[result.1 ≠ result.2] = 0 := by
  apply le_antisymm ?_ zero_le
  have budget : IsTotalQueryBound infiniteKeys 3 := by
    simp only [infiniteKeys, isTotalQueryBound_query_bind_iff]
    exact ⟨by decide, fun _ => ⟨by decide, fun _ => ⟨by decide, fun _ => trivial⟩⟩⟩
  have bound := prEvent_randomOracle_le_of_bad_queries infiniteKeys 3 budget
    (fun result => result.1 ≠ result.2) (fun _ _ => False) 0
    (by intro t g; simp) (by
      intro g h
      have same : evalWithAnswerFn (QueryImpl.ofFn g) infiniteKeys = (g 7, g 7) := rfl
      simp only [same, ne_eq, not_true_eq_false] at h)
  simpa only [mul_zero] using bound

end FreshQueryConsumer

namespace FreshQueryConsumer

/-- Query a three-valued cell, then query the Boolean cell only when needed. -/
@[expose] noncomputable def nonuniformAdaptive : OracleComp (ofFn Answer) Bool := by
  classical
  exact (liftM ((ofFn Answer).query true) : OracleComp (ofFn Answer) (Answer true)) >>=
    fun first => if first = (0 : Fin 3) then pure true else
      (liftM ((ofFn Answer).query false) : OracleComp (ofFn Answer) (Answer false)) >>=
        fun second => pure (!second)

/-- The Boolean and three-valued cells have different failure charges. -/
@[expose] noncomputable def keyError (t : Bool) : ENNReal := if t then 1 / 3 else 1 / 2

private theorem query_weight (t : Bool) :
    WorstCaseCostBound (liftM ((ofFn Answer).query t) : OracleComp (ofFn Answer) (Answer t))
      ⟨keyError⟩ (keyError t) := by
  have h : WorstCaseCostBound
      ((liftM ((ofFn Answer).query t) : OracleComp (ofFn Answer) (Answer t)) >>= pure)
      ⟨keyError⟩ (keyError t) := by
    rw [worstCaseCostBound_query_bind_iff]
    simp [costDist, instrumentedRun]
  simpa using h

/-- The actual instrumented adaptive client spends at most the sum of its two key charges. -/
theorem nonuniformAdaptive_budget :
    WorstCaseCostBound nonuniformAdaptive ⟨keyError⟩ (1 / 3 + 1 / 2) := by
  unfold nonuniformAdaptive
  classical
  apply WorstCaseCostBound.bind (A := 1 / 3) (B := 1 / 2)
  · simpa [keyError] using query_weight true
  · intro first
    split
    · simp
    · have h := WorstCaseCostBound.bind (query_weight false)
        (fun second : Answer false => (worstCaseCostBound_pure (!second) ⟨keyError⟩ 0).mpr le_rfl)
      simpa [keyError] using h

/-- The actual cached failure event is bounded by `5 / 6`; a uniform two-query bound
using the larger local error would give only `1`. -/
theorem nonuniformAdaptive_bound :
    Pr{let result ← (simulateQ randomOracle nonuniformAdaptive).run' ∅}[result = true] ≤
      1 / 3 + 1 / 2 := by
  classical
  let bad (t : Bool) (g : ∀ b, Answer b) : Prop :=
    if t then g true = (0 : Fin 3) else g false = false
  apply prEvent_randomOracle_le_of_bad_queries_weighted nonuniformAdaptive keyError _
    nonuniformAdaptive_budget (· = true) bad
  · intro t g
    cases t with
    | false =>
        simp only [bad, Bool.false_eq_true, ite_false, Function.update_self, keyError]
        let : MeasurableSpace (Answer false) := ⊤
        rw [prEvent_eq_evalDist_of_discrete, SampleableType.evalDist_uniformSample]
        change (ProbabilityTheory.uniformOn Set.univ : Measure Bool) {false} ≤ _
        rw [ProbabilityTheory.uniformOn_univ_apply_singleton]
        norm_num
    | true =>
        simp only [bad, ite_true, Function.update_self, keyError]
        let : MeasurableSpace (Answer true) := ⊤
        rw [prEvent_eq_evalDist_of_discrete, SampleableType.evalDist_uniformSample]
        change (ProbabilityTheory.uniformOn Set.univ : Measure (Fin 3)) {0} ≤ _
        rw [ProbabilityTheory.uniformOn_univ_apply_singleton]
        norm_num
  · intro g h
    by_cases hfirst : g true = (0 : Fin 3)
    · refine ⟨⟨true, g true⟩, ?_, ?_⟩
      · simp [nonuniformAdaptive, tableQueryLog_query_bind, hfirst]
      · simpa [bad] using hfirst
    · refine ⟨⟨false, g false⟩, ?_, ?_⟩
      · simp [nonuniformAdaptive, tableQueryLog_query_bind, hfirst]
      · change g false = false
        have hn : (!(g false : Bool)) = true := by
          simpa [nonuniformAdaptive, hfirst, evalWithAnswerFn_bind,
            evalWithAnswerFn_liftM_query] using h
        exact Bool.eq_false_of_not_eq_true' hn


end FreshQueryConsumer
