/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.MeasurableServices.RejectionTiming
public import VCVio.EvalDist.ResumptionMeasure.Domain
public import Mathlib.Probability.Distributions.Geometric
public import VCVio.EvalDist.ResumptionKernel.Stateless
public import VCVio.EvalDist.KernelHandler.Machine
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.ProgramLogic.Relational.ConditionalView
public import ToMathlib.Probability.FairBit

/-!
# Compiled rejection sampling with a retry simulator

Instrument the existing four-outcome rejection step with its retry count, then
implement each request by two fair bits through `MachineHandler.dispatch`.
The actual compiled machine returns a uniform value independent of a geometric
retry count. The named `retrySimulator` therefore simulates retries from any
public view while retaining the entire accepted value as secret. This is a
joint-law statement about retry counts, not a backend constant-time claim.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal

namespace ResumptionRejection

/-- Instrument the existing rejection step, incrementing the counter only on rejection. -/
def countedStep (state : ℕ × Option (Fin 3)) :
    (Fin 3 × ℕ) ⊕ four.Obj (ℕ × Option (Fin 3)) :=
  match step state.2 with
  | .inl x => .inl (x, state.1)
  | .inr ⟨q, next⟩ => .inr ⟨q, fun x => match next x with
      | some y => (state.1, some y)
      | none => (state.1 + 1, none)⟩

/-- The counted rejection behavior starting with an initial retry count. -/
def countedSample (retries : ℕ) : Resumption four (Fin 3 × ℕ) :=
  Resumption.corec countedStep (retries, none)

/-- Acceptance returns the current retry count without another query. -/
theorem counted_corec_some (n : ℕ) (x : Fin 3) :
    Resumption.corec countedStep (n, some x) = Resumption.pure (x, n) := by
  apply Resumption.eq_of_dest_eq
  simp [countedStep, step]

/-- One four-outcome attempt either returns its value or retries with the incremented counter. -/
theorem countedSample_unfold (n : ℕ) : countedSample n = Resumption.query () (fun x =>
    match accept x with
    | some y => Resumption.pure (y, n)
    | none => countedSample (n + 1)) := by
  apply Resumption.eq_of_dest_eq
  rw [countedSample, Resumption.dest_corec, Resumption.dest_query]
  change Sum.inr (⟨(), fun x => Resumption.corec countedStep (match accept x with
    | some y => (n, some y) | none => (n + 1, none))⟩ : four.Obj _) = _
  congr 2
  funext x
  cases h : accept x <;> simp only [counted_corec_some, countedSample]

/-- One finite attempt gives each accepted value and the retry branch equal weight. -/
theorem counted_output_succ (fuel n : ℕ) (event : Set (Fin 3 × ℕ)) :
    Resumption.outputMeasure (fuel + 1) (countedSample n) event =
      (Measure.dirac (0, n) event + Measure.dirac (1, n) event +
        Measure.dirac (2, n) event +
        Resumption.outputMeasure fuel (countedSample (n + 1)) event) * (4 : ℝ≥0∞)⁻¹ := by
  conv_lhs => rw [countedSample_unfold]
  rw [Resumption.outputMeasure_query_succ (P := four), Measure.bind_apply MeasurableSet.of_discrete
    Measurable.of_discrete.aemeasurable, lintegral_fintype]
  simp [Fin.sum_univ_succ, accept, Resumption.outputMeasure_pure,
    AnswerMeasure.toMeasure, uniformOn_univ, ← add_mul, add_assoc]

/-- The finite joint law records exactly the possible retry counts at the supplied cutoff. -/
theorem counted_output_atom (fuel start retries : ℕ) (x : Fin 3) :
    Resumption.outputMeasure fuel (countedSample start) {(x, retries)} =
      if start ≤ retries ∧ retries < start + fuel then
        (4 : ℝ≥0∞)⁻¹ ^ (retries - start + 1) else 0 := by
  induction fuel generalizing start with
  | zero =>
    rw [countedSample_unfold, Resumption.outputMeasure_query_zero (P := four)]
    simp
  | succ fuel ih =>
    rw [counted_output_succ, ih]
    by_cases h : start = retries
    · subst retries
      fin_cases x <;> simp [show ¬start + 1 ≤ start by omega]
    · have hdirac : ∀ y : Fin 3, Measure.dirac (y, start) {(x, retries)} = 0 := by
        intro y
        simp [h]
      simp only [hdirac, zero_add]
      by_cases hle : start ≤ retries
      · have hnext : start + 1 ≤ retries := by omega
        have hsub : retries - start = retries - (start + 1) + 1 := by omega
        simp only [hle, hnext, true_and]
        by_cases hlt : retries < start + (fuel + 1)
        · have hlt' : retries < start + 1 + fuel := by omega
          simp only [hlt, hlt', ↓reduceIte, hsub, pow_succ]
        · have hlt' : ¬retries < start + 1 + fuel := by omega
          simp [hlt, hlt']
      · have hnext : ¬start + 1 ≤ retries := by omega
        simp [hle, hnext]

/-- Exactly `n` rejections followed by a specified accepted value has mass `4⁻⁽ⁿ⁺¹⁾`. -/
theorem counted_returned_atom (retries : ℕ) (x : Fin 3) :
    Resumption.returnedMeasure (countedSample 0) {(x, retries)} =
      (4 : ℝ≥0∞)⁻¹ ^ (retries + 1) := by
  rw [Resumption.returnedMeasure_apply (P := four) _ _ (measurableSet_singleton _)]
  simp only [counted_output_atom, Nat.zero_le, zero_add, Nat.sub_zero, true_and]
  apply le_antisymm
  · apply iSup_le
    intro fuel
    split_ifs <;> simp
  · exact le_iSup_of_le (retries + 1) (by simp)

/-- The geometric number of failed attempts before a three-in-four success. -/
noncomputable def retryLaw : Measure ℕ := geometricMeasure ⟨3 / 4, by norm_num, by norm_num⟩
instance : IsProbabilityMeasure retryLaw := by
  unfold retryLaw
  infer_instance

/-- The retry simulator assigns geometric mass to each finite retry count. -/
theorem retryLaw_singleton (n : ℕ) :
    retryLaw {n} = (4 : ℝ≥0∞)⁻¹ ^ n * (3 / 4) := by
  rw [retryLaw, geometricMeasure_singleton (by norm_num [Subtype.ext_iff])]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]

/-- The accepted value and exact retry count are independent in the returned law. -/
theorem counted_joint_law : Resumption.returnedMeasure (countedSample 0) =
    (uniformOn (Set.univ : Set (Fin 3))).prod retryLaw := by
  apply Measure.ext_of_singleton
  rintro ⟨x, n⟩
  rw [counted_returned_atom, ← Set.singleton_prod_singleton, Measure.prod_prod,
    uniformOn_univ_apply_singleton, retryLaw_singleton]
  simp only [Fintype.card_fin, Nat.cast_ofNat, pow_succ, div_eq_mul_inv]
  rw [← mul_assoc, mul_comm (3 : ℝ≥0∞)⁻¹, mul_assoc]
  congr 1
  norm_num [← mul_assoc, ENNReal.inv_mul_cancel]


open DynSystem

/-- Primitive coin answers use the ordinary measurable space on Boolean values. -/
local instance coinAnswerMeasurableSpace :
    ∀ a, MeasurableSpace (coinSpec.toPFunctor.B a) :=
  fun _ => inferInstanceAs (MeasurableSpace Bool)

/-- Decode two bits as their binary value in `Fin 4`. -/
def bitsValue (b c : Bool) : Fin 4 :=
  ⟨(if b then 2 else 0) + (if c then 1 else 0), by cases b <;> cases c <;> decide⟩

/-- The executable four-outcome service uses exactly two primitive fair-bit queries. -/
def bitsProgram : FreeM coinSpec.toPFunctor (Fin 4 × Unit) :=
  FreeM.liftBind () (fun b => FreeM.liftBind () (fun c => pure (bitsValue b c, ())))

/-- Implement four-outcome requests by the finite fair-bit program with trivial shared state. -/
def bitsHandler : MachineHandler four coinSpec.toPFunctor Unit :=
  .ofFreeM (fun _ _ => bitsProgram)

/-- The two-bit implementation has the prescribed uniform answer and unchanged trivial state. -/
theorem bitsProgram_law : 𝒟[bitsProgram] =
    (uniformOn (Set.univ : Set (Fin 4))).map (fun x => (x, ())) := by
  have fair {X : Type} [MeasurableSpace X] (k : Bool → FreeM coinSpec.toPFunctor X) :
      FreeM.denote (.liftBind (P := coinSpec.toPFunctor) () k) =
        (2 : ℝ≥0∞)⁻¹ • (FreeM.denote (k false) + FreeM.denote (k true)) := by
    rw [FreeM.denote_liftBind (P := coinSpec.toPFunctor) _ _
      Measurable.of_discrete.aemeasurable,
      show AnswerMeasure.toMeasure (P := coinSpec.toPFunctor) () =
        uniformOn (Set.univ : Set Bool) from
          OracleSpec.AnswerMeasure.toMeasure_eq_uniformOn (spec := coinSpec) (),
      Measure.bind_uniformOn_bool]
  rw [FreeM.evalDist_eq_denote (P := coinSpec.toPFunctor), bitsProgram, fair, fair, fair]
  simp only [FreeM.denote_pure]
  apply Measure.ext_of_singleton
  rintro ⟨x, u⟩
  cases u
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  have hpre : (fun x : Fin 4 => (x, ())) ⁻¹' {(x, ())} = {x} := by
    ext y
    simp
  rw [hpre, uniformOn_univ_apply_singleton]
  fin_cases x <;> norm_num [bitsValue, Measure.smul_apply, Measure.add_apply, ← ENNReal.mul_inv]

/-- The fair-bit service realizes the chosen four-outcome answer kernel. -/
theorem bitsHandler_realizes : (AnswerMeasure.statelessKernel four).Realizes
    bitsHandler.toHandler := by
  intro a u
  cases a
  cases u
  change 𝒟[(DynComputation.ofFreeM (fun _ : Unit => bitsProgram)).denote ()] = _
  rw [Resumption.evalDist_eq_returnedMeasure (P := coinSpec.toPFunctor),
    DynComputation.denote_ofFreeM,
    Resumption.returnedMeasure_toResumption (P := coinSpec.toPFunctor)]
  rw [AnswerMeasure.statelessKernel_apply]
  simpa only [FreeM.evalDist_eq_denote, AnswerMeasure.toMeasure] using bitsProgram_law

/-- An executable caller using the instrumented rejection step and a retained retry counter. -/
@[expose, implicit_reducible] def countedMachine : DynComputation four ℕ (Fin 3 × ℕ) :=
  .ofStep countedStep (fun n => (n, none))

/-- The counted caller machine has the canonical counted resumption behavior. -/
theorem countedMachine_denote (n : ℕ) : countedMachine.denote n = countedSample n := by
  have h : countedMachine.toDynSystem.behavior = Resumption.corec countedStep :=
    Resumption.corec_unique countedStep _ (fun state => by
      have hv := DynComputation.view_ofStep countedStep (fun n => (n, none)) state
      change countedMachine.view state = countedStep state at hv
      rw [DynComputation.dest_behavior_view countedMachine, hv])
  exact congrFun h (n, none)

/-- Compose the continuing rejection caller with the actual two-bit service machine. -/
@[expose, implicit_reducible] def compiledMachine :
    DynComputation (coinSpec.toPFunctor + PFunctor.y) (ℕ × Unit) ((Fin 3 × ℕ) × Unit) :=
  bitsHandler.dispatch countedMachine

/-- The compiled fair-bit machine returns a uniform value and independent geometric retries. -/
theorem compiled_joint_law :
    (𝒟[ITree.ofResumptionWithTau (compiledMachine.denote (0, ()))]).map Prod.fst =
      (uniformOn (Set.univ : Set (Fin 3))).prod retryLaw := by
  rw [compiledMachine, bitsHandler.evalDist_dispatch (AnswerMeasure.statelessKernel four)
    bitsHandler_realizes, countedMachine_denote, Resumption.map_runKernel_stateless (P := four),
    counted_joint_law]

/-- The compiled sampler returns almost surely, including its retained retry count. -/
theorem compiled_almost_sure_return :
    𝒟[ITree.ofResumptionWithTau (compiledMachine.denote (0, ()))] Set.univ = 1 := by
  have h := congrArg (fun μ : Measure (Fin 3 × ℕ) => μ Set.univ) compiled_joint_law
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ, measure_univ] using h

/-- A named simulator that samples retries independently of the supplied public view. -/
noncomputable def retrySimulator (Public : Type*) [MeasurableSpace Public] : Kernel Public ℕ :=
  Kernel.const Public retryLaw

instance (Public : Type*) [MeasurableSpace Public] : IsMarkovKernel (retrySimulator Public) := by
  unfold retrySimulator
  infer_instance

/-- Retrying reveals no additional information about the accepted value, under any public view. -/
theorem simulates_retries {Public : Type*} [MeasurableSpace Public]
    (view : Fin 3 → Public) (hview : Measurable view) :
    SimulatesView Prod.fst (fun out => view out.1) Prod.snd (retrySimulator Public)
      ((𝒟[ITree.ofResumptionWithTau (compiledMachine.denote (0, ()))]).map Prod.fst) := by
  rw [compiled_joint_law]
  apply SimulatesView.of_indepFun measurable_fst (hview.comp measurable_fst) measurable_snd
    (indepFun_prod (hview.prodMk measurable_id) measurable_id) retryLaw
  simp [Measure.map_snd_prod]

end ResumptionRejection
