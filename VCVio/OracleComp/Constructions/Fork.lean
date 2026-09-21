/-
Copyright (c) 2026 Devon Tuma, Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.Fork.Basic
public import VCVio.OracleComp.EvalDist.UniformCompatibility
public import VCVio.EvalDist.Prod

/-!
# Probability bounds for forking oracle computations

Typed occurrence forks admit measure-native conditional-square and focused-answer collision
bounds. This module supplies their discrete probability equations.
-/

@[expose] public section

open OracleSpec ENNReal MeasureTheory
open scoped PFunctor

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- Fixed-index observed success squares under two independent completions of
the selected occurrence context. -/
@[deprecated "VCVio retiring probability API: use `prEvent_sq_le_observedForkPair`"
  (since := "2026-09-16")]
theorem sq_probOutput_map_le_observedForkPair [DecidableEq ι] [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (n : Nat) (observe : α → Option β) (value : β)
    (hselect : OutputSelectsOccurrence main i n observe value) :
    Pr[= value | observe <$> main] ^ 2 ≤
      Pr[= (some (some value, some value) : Option (Option β × Option β)) |
        observedForkPair main i n observe] := by
  let (t : spec.Domain) : MeasurableSpace (spec.Range t) := ⊤
  let : MeasurableSpace β := ⊤
  have h := prEvent_sq_le_observedForkPair main i n observe value hselect
  rw [← prEvent_map main observe (fun output ↦ output = some value)] at h
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton] at h
  simpa only [evalDist_apply_singleton] using h

/-! ## Focused-answer collision bound

The two focused answers of a completed fork collide with probability at most the
inverse answer-space cardinality: the second focused answer is a fresh uniform
draw, independent of the first path and of the resampled suffix. -/

/-- Completing an occurrence resamples the focused answer as a fresh `query i`:
any event on that answer marginalizes the resampled suffix away. -/
@[deprecated "VCVio retiring probability API: use `prEvent_answer_completeOccurrence`"
  (since := "2026-09-16")]
theorem probEvent_answer_ofFreeM_complete [IsProbabilitySpec spec]
    {main : OracleComp spec α} {i : ι} {n : Nat}
    (occ : PFunctor.FreeM.Cursor.Occurrence i main n) (P : spec.Range i → Prop) :
    Pr[fun completion => P completion.answer | OracleComp.ofFreeM occ.complete] =
      Pr[P | (query i : OracleComp spec (spec.Range i))] := by
  let (t : spec.Domain) : MeasurableSpace (spec.Range t) := ⊤
  let := PFunctor.IsProbabilitySpec.toMeasureSpec spec.toPFunctor
  let : MeasurableSpace occ.Completion := ⊤
  have h := congrArg (fun μ ↦ μ {answer | P answer})
    (evalDist_map_answer_completeOccurrence occ)
  rw [evalDist_map_of_discrete, Measure.map_apply Measurable.of_discrete .of_discrete,
    ← evalDist_query i] at h
  simpa only [Set.preimage_setOf_eq, Cursor.completeOccurrence, evalDist_apply_setOf] using h

/-- The two focused answers of a located fork collide with probability at most
the inverse answer-space cardinality: the second answer is a fresh uniform
draw, independent of the first completion. Any additional guard on the first
output only tightens the event. -/
@[deprecated "VCVio retiring probability API: use `prEvent_focusCollision_fork_le_of_uniform`"
  (since := "2026-09-16")]
theorem probEvent_focusCollision_ofFreeM_fork_le [IsUniformSpec spec]
    {main : OracleComp spec α} {i : ι} {n : Nat} {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path n) (accept : α → Prop) :
    Pr[fun view => view.firstAnswer = view.secondAnswer ∧
        accept (PFunctor.FreeM.output main view.firstPath) |
          OracleComp.ofFreeM located.fork] ≤ (Fintype.card (spec.Range i) : ℝ≥0∞)⁻¹ := by
  rw [PFunctor.FreeM.Cursor.Located.fork_eq_map_complete, probEvent_ofFreeM_map]
  exact (probEvent_mono fun completion _ h ↦ h.1).trans <|
    (probEvent_answer_ofFreeM_complete located.occurrence
      (fun a ↦ located.completion.answer = a)).trans_le
      (probEvent_query_le_inv_of_unique i _ fun x y hx hy ↦ hx.symm.trans hy)

end OracleComp
