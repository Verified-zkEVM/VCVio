/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.OracleComp.Constructions.FirstSuccess.Measure
public import VCVio.EvalDist.Instances.OptionT
public import VCVio.OracleComp.Constructions.UniformFinMeasure
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Finiteness

/-!
# First-success observation regressions

Stateful and indexed controls distinguish the first successful draw from later draws and keep
returned exhaustion separate from missing output mass. A mixed finite experiment checks the
quantitative exhaustion, success and missing-mass equations together.
-/

public section

namespace VCVioTest.FirstSuccess

open VCVio.Algorithms.FirstSuccess
open scoped ENNReal

/-- Consume one Boolean from a stream, defaulting to false at its end. -/
@[expose] def draw : StateM (List Bool) Bool := fun stream =>
  match stream with
  | [] => (false, [])
  | first :: rest => (first, rest)

/-- A true draw returns a fixed payload and a false draw advances the loop. -/
@[expose] def accept (value : Bool) : Option ℕ := if value then some 7 else none

example : (runWith draw accept 0).run [true] = (none, [true]) := rfl
example : (runWith draw accept 3).run [true, false] = (some 7, [false]) := rfl
example : (runWith draw accept 3).run [false, true, false] = (some 7, [false]) := rfl
example : (runWith draw accept 2).run [false, false, true] = (none, [true]) := rfl

/-- Indexed search records the second successful attempt and consumes no third draw. -/
theorem indexed_second_trace :
    (indexed accept 3 (fun _ => draw)).run [false, true, false] =
      (.success 7 2 [false, true], [false]) := rfl

example : indexed (m := Id) (fun n => if n = 12 then some n else none) 4
    (fun i => i.val + 10) = .success 12 3 [10, 11, 12] := rfl
example : indexed (m := Id) accept 0 (fun i => nomatch i) = .exhausted [] := rfl
example : indexed (m := Id) (fun _ : ℕ => (none : Option ℕ)) 3 (fun i => i.val) =
    .exhausted [0, 1, 2] := rfl

/-- Mapping payloads preserves the actual prefix and one-based successful attempt. -/
theorem mapped_second_trace :
    (Result.map (fun n => 2 * n) <$> indexed accept 3 (fun _ => draw)).run
      [false, true, false] = (.success 14 2 [false, true], [false]) := rfl

example : (Result.exhausted [0, 1] : Result ℕ ℕ).map (fun n => n + 1) = .exhausted [0, 1] := rfl

/-- The fixed sampler has exactly the indexed loop's optional output observation. -/
theorem fixed_sampler_observation :
    (runWith draw accept 3).run [false, true, false] =
      (Result.output <$> indexed accept 3 (fun _ => draw)).run [false, true, false] := by
  rw [runWith_eq_output_indexed]

/-- Optional abort is missing execution mass in this runtime. -/
@[expose] noncomputable def optionalRuntime : ProbCompRuntime (OptionT ProbComp) where
  toSemanticsVia := SemanticsVia.ofEvalDistSemantics (OptionT ProbComp)
  toProbCompLift := ProbCompLift.ofMonadLift (OptionT ProbComp)
  evalDist_map_eq _f hf mx := evalDist_map mx hf

/-- The optional runtime interprets native pure and bind with their integral semantics. -/
theorem optional_sampling_laws : optionalRuntime.SamplingLaws where
  pure_eq x := by
    simp [optionalRuntime, ProbCompRuntime.evalDist,
      SemanticsVia.ofEvalDistSemantics_evalDist, evalDist_pure]
  bind_eq {α} {β} c f p := by
    let : MeasurableSpace α := ⊤
    simp only [optionalRuntime, ProbCompRuntime.evalDist,
      SemanticsVia.ofEvalDistSemantics_evalDist]
    simpa only [← prEvent_eq_evalDist_map] using prEvent_bind_eq_lintegral_of_discrete c f p

/-- Aborting a draw has missing mass one. -/
theorem abort_missing_mass : missingMass optionalRuntime (failure : OptionT ProbComp Bool) = 1 := by
  simp [missingMass, optionalRuntime, ProbCompRuntime.evalDist,
    SemanticsVia.ofEvalDistSemantics_evalDist]

/-- A zero budget avoids an aborting draw and returns ordinary exhaustion. -/
theorem zero_budget_avoids_abort :
    missingMass optionalRuntime (runWith (failure : OptionT ProbComp Bool) accept 0) = 0 :=
  missingMass_runWith_zero optionalRuntime optional_sampling_laws _ _

/-- A reached abort remains missing mass rather than returned exhaustion. -/
theorem reached_abort_missing_mass :
    missingMass optionalRuntime (runWith (failure : OptionT ProbComp Bool) accept 2) = 1 := by
  rw [missingMass_runWith_eq_mul_sum optionalRuntime optional_sampling_laws, abort_missing_mass]
  simp [failureMass, failureIndicatorDist, optionalRuntime,
    ProbCompRuntime.evalDist, SemanticsVia.ofEvalDistSemantics_evalDist, Finset.sum_range_succ]

/-- One quarter returns false, one quarter true, and one half aborts. -/
@[expose] def mixedValue (i : Fin 4) : Option Bool :=
  if i = 0 then some false else if i = 1 then some true else none

/-- A finite experiment with all three observations carrying positive mass. -/
@[expose] def mixed : OptionT ProbComp Bool :=
  OptionT.mk (mixedValue <$> ProbComp.uniformFin 3)

/-- The mixed experiment's Boolean event mass is the finite count of its present outcomes. -/
theorem mixed_event (event : Set Bool)
    [DecidablePred (fun i : Fin 4 => mixedValue i ∈ some '' event)] :
    optionalRuntime.evalDist mixed event =
    ((Finset.univ.filter (fun i : Fin 4 => mixedValue i ∈ some '' event)).card : ℝ≥0∞) / 4 := by
  classical
  change 𝒟[mixed] event = _
  rw [OptionT.evalDist_apply]
  change 𝒟[mixedValue <$> ProbComp.uniformFin 3] (some '' event) = _
  rw [evalDist_map _ Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  change 𝒟[ProbComp.uniformFin 3] {i | mixedValue i ∈ some '' event} = _
  rw [← prEvent_eq_evalDist_of_discrete, ProbComp.prEvent_uniformFin]
  norm_num

/-- The mixed draw returns an ordinary encoding-style failure with mass one quarter. -/
theorem mixed_failure_mass : failureMass optionalRuntime mixed accept = 1 / 4 := by
  classical
  rw [failureMass, failureIndicatorDist,
    optionalRuntime.evalDist_map (fun value => (accept value).isNone) Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true),
    mixed_event]
  norm_num [mixedValue, accept, Fin.univ_succ, Finset.filter_insert, Finset.filter_singleton]

/-- The mixed draw returns success with mass one quarter. -/
theorem mixed_success_mass : successMass optionalRuntime mixed accept = 1 / 4 := by
  classical
  rw [successMass, failureIndicatorDist,
    optionalRuntime.evalDist_map (fun value => (accept value).isNone) Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton false),
    mixed_event]
  norm_num [mixedValue, accept, Fin.univ_succ, Finset.filter_insert, Finset.filter_singleton]

/-- The mixed draw's two aborting outcomes retain missing mass one half. -/
theorem mixed_missing_mass : missingMass optionalRuntime mixed = 1 / 2 := by
  classical
  rw [missingMass, optionalRuntime.evalDist_map (fun _ : Bool => true) Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true),
    mixed_event]
  norm_num [mixedValue, Fin.univ_succ, Finset.filter_insert, Finset.filter_singleton]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (by norm_num [ENNReal.div_le_iff]) ENNReal.one_ne_top]
  norm_num

/-- Two returned failures have mass one sixteenth. -/
theorem mixed_two_exhaustion :
    failureMass optionalRuntime (runWith mixed accept 2) id = 1 / 16 := by
  rw [failureMass_runWith_eq_pow optionalRuntime optional_sampling_laws, mixed_failure_mass]
  simp only [one_div, ← ENNReal.inv_pow]
  norm_num

/-- Missing mass also includes failing the first draw then aborting on the second. -/
theorem mixed_two_missing : missingMass optionalRuntime (runWith mixed accept 2) = 5 / 8 := by
  rw [missingMass_runWith_eq_mul_sum optionalRuntime optional_sampling_laws,
    mixed_missing_mass, mixed_failure_mass]
  norm_num [Finset.sum_range_succ]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_add]

/-- Success is not the complement of exhaustion when the sampler can abort. -/
theorem mixed_two_success :
    successMass optionalRuntime (runWith mixed accept 2) id = 5 / 16 := by
  rw [successMass_runWith_eq_mul_sum optionalRuntime optional_sampling_laws,
    mixed_success_mass, mixed_failure_mass]
  norm_num [Finset.sum_range_succ]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_add]

end VCVioTest.FirstSuccess
