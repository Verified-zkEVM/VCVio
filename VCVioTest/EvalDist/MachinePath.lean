/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.MachinePath.Observe
public import VCVio.OracleComp.Coinductive.UniformThreshold

/-!
# Path laws through ordinary imports

The persistent threshold machine has countable residual states. A pure real-valued
machine uses the Borel measurable structure instead. Both expose actual execution
marginals and eventual-return laws through the same public certificate.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor DynSystem DynComputation OracleComp

namespace MachinePathTest

local instance (q : ℚ) : MeasurableSpace (UniformThreshold.machine q).State :=
  inferInstanceAs (MeasurableSpace UniformThreshold.Prefix)

local instance (q : ℚ) : DiscreteMeasurableSpace (UniformThreshold.machine q).State :=
  inferInstanceAs (DiscreteMeasurableSpace UniformThreshold.Prefix)

local instance (q : ℚ) : Countable (UniformThreshold.machine q).State :=
  inferInstanceAs (Countable UniformThreshold.Prefix)

/-- Countable residual data discharges all measurability obligations automatically. -/
theorem threshold_measurable (q : ℚ) : MeasurableExecution (UniformThreshold.machine q) :=
  MeasurableExecution.of_countable

example (q : ℚ) (input : UniformThreshold.Prefix) (fuel : ℕ) :
    ((threshold_measurable q).pathLaw input).map (fun path => path fuel) =
      FreeM.denote ((UniformThreshold.machine q).unrollChunk fuel input) :=
  (threshold_measurable q).pathLaw_map_time input fuel

/-- The certificate controls the joint history, not only each coordinate separately. -/
example (q : ℚ) (input : UniformThreshold.Prefix) (fuel : ℕ) :
    ((threshold_measurable q).pathLaw input).map
        (fun path (i : Fin (fuel + 1)) => path i) =
      FreeM.denote ((UniformThreshold.machine q).unrollHistory fuel input) :=
  (threshold_measurable q).pathLaw_map_history input fuel

example (q : ℚ) (fuel : ℕ) :
    Measurable (fun input =>
      FreeM.denote ((UniformThreshold.machine q).unrollHistory fuel input)) :=
  (threshold_measurable q).measurable_unrollHistory fuel

example (q : ℚ) (input : UniformThreshold.Prefix) (event : Set (Bool × UniformThreshold.Prefix))
    (hevent : MeasurableSet event) :
    Resumption.returnedMeasure ((UniformThreshold.machine q).denote input) event =
      (threshold_measurable q).pathLaw input {path | ∃ n, (path n).result ∈ some '' event} :=
  (threshold_measurable q).returnedMeasure_eq_path_event Chunk.measurable_result input event hevent

/-- An initialized Borel real is returned without asking the available bit oracle. -/
@[expose, reducible] def returnReal : OracleMachine coinSpec ℝ ℝ :=
  ofStep (fun value => Sum.inl value) id

/-- Every fuel observes the same terminal value, including zero fuel. -/
theorem returnReal_unroll (fuel : ℕ) (value : ℝ) :
    returnReal.unrollChunk fuel value = FreeM.pure (.done value) := by
  cases fuel <;> simp only [unrollChunk_zero, unrollChunk_succ, returnReal, view_ofStep]

/-- Borel initialization and a measurable case split give a continuous-state certificate. -/
theorem returnReal_measurable : MeasurableExecution returnReal where
  initial := by
    change Measurable (fun value : ℝ => Measure.dirac (.done value : Chunk ℝ ℝ))
    exact Measure.measurable_dirac.comp Chunk.measurable_done
  step := by
    change Measurable (fun chunk : Chunk ℝ ℝ =>
      FreeM.denote (returnReal.resumeChunk 1 chunk))
    have heq : (fun chunk => FreeM.denote (returnReal.resumeChunk 1 chunk)) =
        (fun chunk : Chunk ℝ ℝ => match chunk with
          | .done value => Measure.dirac (.done value : Chunk ℝ ℝ)
          | .paused value => Measure.dirac (.done value : Chunk ℝ ℝ)) := by
      funext chunk
      cases chunk with
      | done value =>
          rw [resumeChunk_done returnReal 1 value]
          exact FreeM.denote_pure (P := coinSpec.toPFunctor) (Chunk.done value : Chunk ℝ ℝ)
      | paused value =>
          rw [resumeChunk_paused returnReal 1 value, returnReal_unroll]
          exact FreeM.denote_pure (P := coinSpec.toPFunctor) (Chunk.done value : Chunk ℝ ℝ)
    rw [heq]
    convert Chunk.measurable_elim (S := ℝ) (β := ℝ) (γ := Measure (Chunk ℝ ℝ))
      (Measure.measurable_dirac.comp Chunk.measurable_done)
      (Measure.measurable_dirac.comp Chunk.measurable_done) using 1
    funext chunk
    cases chunk <;> rfl

example (input : ℝ) (fuel : ℕ) :
    (returnReal_measurable.pathLaw input).map (fun path => path fuel) =
      Measure.dirac (.done input : Chunk ℝ ℝ) := by
  rw [returnReal_measurable.pathLaw_map_time, returnReal_unroll]
  exact FreeM.denote_pure (P := coinSpec.toPFunctor) (Chunk.done input : Chunk ℝ ℝ)

example (input : ℝ) (event : Set ℝ) (hevent : MeasurableSet event) :
    Resumption.returnedMeasure (returnReal.denote input) event =
      returnReal_measurable.pathLaw input {path | ∃ n, (path n).result ∈ some '' event} :=
  returnReal_measurable.returnedMeasure_eq_path_event Chunk.measurable_result input event hevent

/-- An input adapter reuses the certificate without a new proof about residual states. -/
example (input : ℝ × ℝ) :
    (returnReal_measurable.contramapInput Prod.fst measurable_fst).pathLaw input =
      returnReal_measurable.pathLaw input.1 :=
  returnReal_measurable.pathLaw_contramapInput Prod.fst measurable_fst input

/-- A noninjective Borel observation transports the joint law of all returned values. -/
example (input : ℝ) :
    (returnReal_measurable.mapResult (fun value => value * value)
      (measurable_id.mul measurable_id)).pathLaw input =
      (returnReal_measurable.pathLaw input).map
        (fun path n => (path n).map id (fun value => value * value)) :=
  returnReal_measurable.pathLaw_mapResult _ (measurable_id.mul measurable_id) input

/-- State-dependent real weights accumulate in the usual Borel measurable space. -/
theorem threshold_accumulator_measurable (q : ℚ)
    (observe : (UniformThreshold.machine q).toDynSystem.EventMap (Multiplicative ℝ)) :
    MeasurableExecution ((UniformThreshold.machine q).withAccumulator observe) :=
  MeasurableExecution.withAccumulator_of_countable _ observe measurable_id

/-- Every coordinate retains the accumulator, including unfinished executions. -/
example (q : ℚ)
    (observe : (UniformThreshold.machine q).toDynSystem.EventMap (Multiplicative ℝ))
    (p : UniformThreshold.Prefix) (initial : Multiplicative ℝ) (fuel : ℕ) :
    ((threshold_accumulator_measurable q observe).pathLaw (p, initial)).map
        (fun path (i : Fin (fuel + 1)) => path i) =
      FreeM.denote (((UniformThreshold.machine q).withAccumulator observe).unrollHistory
        fuel (p, initial)) :=
  (threshold_accumulator_measurable q observe).pathLaw_map_history (p, initial) fuel

end MachinePathTest
