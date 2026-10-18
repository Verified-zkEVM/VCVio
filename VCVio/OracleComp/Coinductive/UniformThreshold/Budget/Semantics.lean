/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.UniformThreshold.Budget
public import VCVio.EvalDist.KernelHandler.Except
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.EvalDist.MachinePath
public import ToMathlib.MeasureTheory.MeasurableSpace.NNRat

/-!
# Joint laws of admitted threshold clients

The service kernel retains the explicit error or Boolean answer together with
the updated dyadic prefix and rational allowance. Its law extends to every
adaptive finite client through the common exception-answer adapter. Refusal and
timeout are ordinary probability outcomes; neither discards the retained state.
A local potential bounds timeout for every adaptive finite client by its initial
allowance. The conservative executable cap policy preserves positive allowance,
so the same bound covers all of its errors.
-/

public section

open OracleComp PFunctor MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace UniformThreshold.Budget

instance : MeasurableSpace Failure := ⊤

instance : DiscreteMeasurableSpace Failure := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : Countable Failure := Function.Injective.countable
  (f := fun x : Failure => match x with | .budgetExhausted => false | .timeout => true) (by
    intro x y h
    cases x <;> cases y <;> simp_all)

/-- The joint error-or-answer and retained-state law of an admitted operation. -/
noncomputable def answerKernel (cap : ℚ → Session → ℕ) :
    KernelHandler (spec.toPFunctor.withExcept Failure) Session := fun q =>
  ⟨fun state => 𝒟[((handler cap q).run).run state], Measurable.of_discrete⟩

/-- Each capped operation terminates with either an answer or an explicit error. -/
instance (cap : ℚ → Session → ℕ) (q : ℚ) : IsMarkovKernel (answerKernel cap q) := by
  refine ⟨fun state => ?_⟩
  change IsProbabilityMeasure 𝒟[((handler cap q).run).run state]
  exact FreeM.isProbabilityMeasure_denote _

/-- The executable service realizes its explicit exceptional-answer kernel. -/
theorem realizes (cap : ℚ → Session → ℕ) :
    (answerKernel cap).Realizes (handler cap).exceptAnswers := fun _ _ => rfl

/-- The finite client's full law includes the failure tag, sampled prefix and unused allowance. -/
theorem evalDist_run {α : Type} [MeasurableSpace α] (cap : ℚ → Session → ℕ)
    (program : FreeM spec.toPFunctor α) (state : Session) :
    𝒟[run cap program state] = FreeM.runKernel (answerKernel cap) program.withExcept state :=
  (realizes cap).runExcept program state

/-- Refusal produces a point mass at the original state, including the untouched allowance. -/
theorem answerKernel_of_refused (cap : ℚ → Session → ℕ) (q : ℚ) (state : Session)
    (h : state.2 < charge (cap q state)) :
    answerKernel cap q state = Measure.dirac (.error .budgetExhausted, state) := by
  change 𝒟[((handler cap q).run).run state] = _
  rw [show ((handler cap q).run).run state = pure (.error .budgetExhausted, state) from
    machineHandler.admitted_run_error (admission cap) _ q state .budgetExhausted
      (admission_error cap q state h)]
  exact evalDist_pure _

/-- Admission maps the actual saved chunk to its error-or-answer and retained session. -/
theorem answerKernel_of_admitted (cap : ℚ → Session → ℕ) (q : ℚ) (state : Session)
    (h : charge (cap q state) ≤ state.2) :
    answerKernel cap q state =
      (FreeM.denote (α := DynSystem.DynComputation.Chunk Prefix (Bool × Prefix))
        ((machine q).unrollChunk (cap q state) state.1)).map
        (fun chunk : DynSystem.DynComputation.Chunk Prefix (Bool × Prefix) =>
          machineHandler.finishAdmitted (fun _ _ residual => (.timeout, residual)) q
            (state.1, state.2 - charge (cap q state)) chunk) := by
  rw [← realizes cap q state]
  change 𝒟[((handler cap q).run).run state] = _
  rw [show ((handler cap q).run).run state =
    FreeM.map (machineHandler.finishAdmitted (fun _ _ residual => (.timeout, residual)) q
      (state.1, state.2 - charge (cap q state)))
      ((machine q).unrollChunk (cap q state) state.1) from
        machineHandler.admitted_run_ok (admission cap) _ q state _ _
          (admission_ok cap q state h)]
  exact FreeM.denote_map_of_measurable (P := coinSpec.toPFunctor)
    (α := DynSystem.DynComputation.Chunk Prefix (Bool × Prefix)) _ _ Measurable.of_discrete

/-- Observe only a successful value and prefix, forgetting the allowance and all errors. -/
@[expose] def successfulResult {α : Type} (out : Except Failure α × Session) :
    Option (α × Prefix) := out.1.toOption.map (fun value => (value, out.2.1))

/-- After admission, forgetting errors and budget recovers the capped threshold law. -/
theorem map_answerKernel_of_admitted (cap : ℚ → Session → ℕ) (q : ℚ) (state : Session)
    (h : charge (cap q state) ≤ state.2) :
    (answerKernel cap q state).map successfulResult = boundedLaw q state.1 (cap q state) := by
  rw [answerKernel_of_admitted cap q state h,
    Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  have hproj : successfulResult ∘
      machineHandler.finishAdmitted (fun _ _ residual => (.timeout, residual)) q
        (state.1, state.2 - charge (cap q state)) = DynSystem.DynComputation.Chunk.result := by
    funext chunk
    cases chunk <;> rfl
  rw [hproj, ← FreeM.denote_map_of_measurable (P := coinSpec.toPFunctor)
    (α := DynSystem.DynComputation.Chunk Prefix (Bool × Prefix)) _
      DynSystem.DynComputation.Chunk.result Measurable.of_discrete]
  rw [DynSystem.DynComputation.unrollChunk_result (machine q) (cap q state) state.1]
  rw [boundedLaw_eq_truncateMeasure]
  exact DynSystem.DynComputation.denote_unroll _ _ _

/-- The actual error-and-state kernel charges at most the reserved allowance after admission. -/
theorem failure_le_charge_of_admitted (cap : ℚ → Session → ℕ) (q : ℚ) (state : Session)
    (h : charge (cap q state) ≤ state.2) :
    answerKernel cap q state {out | out.1.toOption = none} ≤ (charge (cap q state) : ℝ≥0∞) := by
  have hcutoff := cutoff_le_charge q state.1 (cap q state)
  rw [← map_answerKernel_of_admitted cap q state h,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton none)] at hcutoff
  have hevent : (successfulResult ⁻¹' {none} : Set (Except Failure Bool × Session)) =
      {out | out.1.toOption = none} := by
    ext out
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      successfulResult, Option.map_eq_none_iff]
  rwa [hevent] at hcutoff

/-- Every admitted outcome retains exactly the debited allowance, including timeout. -/
theorem ae_allowance_eq_of_admitted (cap : ℚ → Session → ℕ) (q : ℚ) (state : Session)
    (h : charge (cap q state) ≤ state.2) :
    ∀ᵐ out ∂answerKernel cap q state, out.2.2 = state.2 - charge (cap q state) := by
  rw [answerKernel_of_admitted cap q state h]
  apply (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).mpr
  exact Filter.Eventually.of_forall fun _ =>
    machineHandler.finishAdmitted_snd_snd _ _ _ _

/-- An immediate timeout and the successful continuation's remaining allowance fit
within the incoming allowance. Refusal contributes no timeout error. -/
theorem lintegral_answerKernel_timeout_le (cap : ℚ → Session → ℕ) (q : ℚ) (state : Session) :
    (∫⁻ out, out.1.casesOn (({Failure.timeout} : Set Failure).indicator (fun _ => 1))
      (fun _ => (out.2.2 : ℝ≥0∞)) ∂answerKernel cap q state) ≤ (state.2 : ℝ≥0∞) := by
  by_cases h : charge (cap q state) ≤ state.2
  · let failures : Set (Except Failure Bool × Session) := {out | out.1.toOption = none}
    have hmono : (∫⁻ out, out.1.casesOn (({Failure.timeout} : Set Failure).indicator (fun _ => 1))
        (fun _ => (out.2.2 : ℝ≥0∞)) ∂answerKernel cap q state) ≤
        ∫⁻ out, failures.indicator (fun _ => 1) out +
          ((state.2 - charge (cap q state) : ℚ≥0) : ℝ≥0∞) ∂answerKernel cap q state := by
      apply lintegral_mono_ae
      filter_upwards [ae_allowance_eq_of_admitted cap q state h] with out hout
      obtain ⟨answer, pref, budget⟩ := out
      cases answer with
      | error e => cases e <;> simp [failures, Set.indicator, Except.toOption]
      | ok value => simp_all [failures, Set.indicator]
    apply hmono.trans
    rw [lintegral_add_left (measurable_const.indicator MeasurableSet.of_discrete),
      lintegral_indicator_fun_one MeasurableSet.of_discrete, lintegral_const, measure_univ, mul_one]
    calc
      _ ≤ (charge (cap q state) : ℝ≥0∞) +
          ((state.2 - charge (cap q state) : ℚ≥0) : ℝ≥0∞) :=
        add_le_add (failure_le_charge_of_admitted cap q state h) le_rfl
      _ = (state.2 : ℝ≥0∞) := by
        have hb := congrArg (fun x : ℚ≥0 => (x : ℝ≥0∞)) (debit_add_charge (cap q state) state.2 h)
        simpa only [← ENNReal.coe_nnratCast, NNRat.cast_add, ENNReal.coe_add, add_comm] using hb
  · rw [answerKernel_of_refused cap q state (lt_of_not_ge h), lintegral_dirac]
    simp [Set.indicator]

/-- The probability of any timeout in an adaptive finite client is at most its
initial rational allowance. Refusal remains a distinct, explicitly retained outcome. -/
theorem timeout_le_allowance {α : Type} [MeasurableSpace α]
    (cap : ℚ → Session → ℕ) (program : FreeM spec.toPFunctor α) (state : Session) :
    𝒟[run cap program state] {out | out.1 = .error .timeout} ≤ (state.2 : ℝ≥0∞) := by
  rw [evalDist_run]
  simpa using FreeM.runKernel_withExcept_error_le (answerKernel cap) {Failure.timeout}
    (measurableSet_singleton _) (fun state => (state.2 : ℝ≥0∞))
    (lintegral_answerKernel_timeout_le cap) program state

/-- A session initialized with the geometric allowance has a uniform timeout bound,
regardless of its adaptive cap policy and the number of calls in its finite client. -/
theorem timeout_le_geometric {α : Type} [MeasurableSpace α]
    (cap : ℚ → Session → ℕ) (program : FreeM spec.toPFunctor α) (p : Prefix) (precision : ℕ) :
    𝒟[run cap program (p, charge precision)] {out | out.1 = .error .timeout} ≤
      (2 : ℝ≥0∞)⁻¹ ^ precision := by
  simpa only [coe_charge] using timeout_le_allowance cap program (p, charge precision)

/-- From a positive allowance, every capped-call outcome keeps a positive reserve
and cannot be a budget refusal. Timeout still retains its refined prefix. -/
theorem ae_halfAllowanceCap (q : ℚ) (state : Session) (h : 0 < state.2) :
    ∀ᵐ out ∂answerKernel halfAllowanceCap q state,
      out.1 ≠ .error .budgetExhausted ∧ 0 < out.2.2 := by
  have hc : charge (halfAllowanceCap q state) < state.2 :=
    (charge_halfAllowanceCap_lt q state h).trans_le (div_le_self zero_le (by norm_num))
  rw [answerKernel_of_admitted _ q state hc.le]
  apply (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).mpr
  apply Filter.Eventually.of_forall
  intro chunk
  cases chunk <;> simp [MachineHandler.finishAdmitted, tsub_pos_iff_lt.mpr hc]

/-- The conservative cap policy cannot exhaust a positive allowance, even in an
adaptive finite client with no uniform bound on its number of calls. -/
theorem refusal_halfAllowanceCap_eq_zero {α : Type} [MeasurableSpace α]
    (program : FreeM spec.toPFunctor α) (state : Session) (h : 0 < state.2) :
    𝒟[run halfAllowanceCap program state] {out | out.1 = .error .budgetExhausted} = 0 := by
  let potential : Session → ℝ≥0∞ := fun s => if 0 < s.2 then 0 else 1
  have hstep (q : ℚ) (s : Session) :
      (∫⁻ out, out.1.casesOn (({Failure.budgetExhausted} : Set Failure).indicator (fun _ => 1))
        (fun _ => potential out.2) ∂answerKernel halfAllowanceCap q s) ≤ potential s := by
    by_cases hs : 0 < s.2
    · simp only [potential, hs, ↓reduceIte]
      apply le_of_eq
      calc
        _ = ∫⁻ _ : Except Failure Bool × Session, (0 : ℝ≥0∞)
            ∂answerKernel halfAllowanceCap q s := by
          apply lintegral_congr_ae
          filter_upwards [ae_halfAllowanceCap q s hs] with out hout
          obtain ⟨answer, rest⟩ := out
          cases answer with
          | error e => cases e <;> simp_all [Set.indicator]
          | ok value => simp_all
        _ = 0 := by simp
    · simp only [potential, hs, ↓reduceIte]
      calc
        _ ≤ ∫⁻ _ : Except Failure Bool × Session, (1 : ℝ≥0∞)
            ∂answerKernel halfAllowanceCap q s := by
          apply lintegral_mono
          intro out
          obtain ⟨answer, rest⟩ := out
          cases answer with
          | error e => cases e <;> simp [Set.indicator]
          | ok value =>
            change (if 0 < rest.2 then 0 else 1) ≤ (1 : ℝ≥0∞)
            split_ifs <;> simp
        _ = 1 := by simp
  have hb := FreeM.runKernel_withExcept_error_le (answerKernel halfAllowanceCap)
    {Failure.budgetExhausted} (measurableSet_singleton _) potential hstep program state
  rw [evalDist_run]
  apply le_antisymm _ zero_le
  simpa [potential, h] using hb

/-- With the conservative cap policy, every client error is a timeout and the
probability of any error is at most the initial positive allowance. -/
theorem failure_le_allowance_halfAllowanceCap {α : Type} [MeasurableSpace α]
    (program : FreeM spec.toPFunctor α) (state : Session) (h : 0 < state.2) :
    𝒟[run halfAllowanceCap program state] {out | out.1.toOption = none} ≤ (state.2 : ℝ≥0∞) := by
  have hevent : {out : Except Failure α × Session | out.1.toOption = none} =
      {out | out.1 = .error .budgetExhausted} ∪ {out | out.1 = .error .timeout} := by
    ext out
    obtain ⟨answer, rest⟩ := out
    cases answer with
    | error e => cases e <;> simp [Except.toOption]
    | ok value => simp [Except.toOption]
  rw [hevent]
  apply (measure_union_le _ _).trans
  rw [refusal_halfAllowanceCap_eq_zero program state h, zero_add]
  exact timeout_le_allowance halfAllowanceCap program state

end UniformThreshold.Budget
