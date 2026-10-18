/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Relational.Reconstruction
public import PolyFun.PFunctor.Bound
public import ToMathlib.Probability.Kernel.TotalVariation

/-!
# Approximate reconstruction and error potentials

Local error is charged under the concrete execution's actual intermediate state law.
A nonnegative potential pays for each charge and the expected remaining potential; induction
then bounds the accumulated charge of every adaptive client. This is an expectation argument,
so it requires neither a choice of pointwise couplings nor an optional-stopping hypothesis.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PFunctor.KernelHandler

variable {P : PFunctor} {S T : Type*}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace T]

/-- A measurable local allowance for the failure of the reconstruction square to commute. -/
structure ApproxReconstructionContract (concrete : KernelHandler P S)
    (ideal : KernelHandler P T) (reconstruct : Kernel S T) (charge : P.A → S → ℝ≥0∞) : Prop where
  /-- Reconstruction preserves mass. -/
  isMarkov : IsMarkovKernel reconstruct
  /-- Each operation's allowance is measurable in the concrete state. -/
  measurable_charge : ∀ a, Measurable (charge a)
  /-- The two local joint laws differ by at most the stated allowance. -/
  step : ∀ a s, ((ideal a ∘ₖ reconstruct) s).etvDist
    ((Kernel.retainLeft (P.B a) reconstruct ∘ₖ concrete a) s) ≤ charge a s

/-- Expected sum of local charges along the concrete execution, including its adaptive choices. -/
noncomputable def expectedCharge {α : Type*} (concrete : KernelHandler P S)
    (charge : P.A → S → ℝ≥0∞) : FreeM P α → S → ℝ≥0∞
  | .pure _, _ => 0
  | .liftBind a next, s => charge a s +
      ∫⁻ out, expectedCharge concrete charge (next out.1) out.2 ∂concrete a s

@[simp]
theorem expectedCharge_pure {α : Type*} (concrete : KernelHandler P S)
    (charge : P.A → S → ℝ≥0∞) (x : α) (s : S) :
    expectedCharge concrete charge (pure x) s = 0 := by rfl

/-- A query pays its local charge and the expected charge of its continuation. -/
theorem expectedCharge_liftBind {α : Type*} (concrete : KernelHandler P S)
    (charge : P.A → S → ℝ≥0∞) (a : P.A) (next : P.B a → FreeM P α) (s : S) :
    expectedCharge concrete charge (.liftBind a next) s = charge a s +
      ∫⁻ out, expectedCharge concrete charge (next out.1) out.2 ∂concrete a s := by rfl

/-- The expected local charge is a measurable function of the starting state. -/
theorem measurable_expectedCharge [∀ a, Countable (P.B a)]
    [∀ a, MeasurableSingletonClass (P.B a)] {α : Type*} (concrete : KernelHandler P S)
    {charge : P.A → S → ℝ≥0∞} (hcharge : ∀ a, Measurable (charge a)) (program : FreeM P α) :
    Measurable (expectedCharge concrete charge program) := by
  induction program with
  | pure x => exact measurable_const
  | lift_bind a next ih =>
      exact (hcharge a).add ((measurable_from_prod_countable_right ih).lintegral_kernel)

/-- A potential paying for each step bounds the expected sum of charges of any adaptive client.
History and work counters may be included in the concrete state. -/
theorem expectedCharge_le_potential {α : Type*} (concrete : KernelHandler P S)
    (charge : P.A → S → ℝ≥0∞) (budget : S → ℝ≥0∞)
    (hstep : ∀ a s, charge a s + ∫⁻ out, budget out.2 ∂concrete a s ≤ budget s)
    (program : FreeM P α) (s : S) : expectedCharge concrete charge program s ≤ budget s := by
  induction program generalizing s with
  | pure x => exact zero_le
  | lift_bind a next ih =>
      rw [← FreeM.liftBind_eq, expectedCharge_liftBind]
      exact (add_le_add le_rfl
        (lintegral_mono (μ := concrete a s) fun out : P.B a × S => ih out.1 out.2)).trans
          (hstep a s)

/-- A uniform per-operation charge recovers the usual query-count bound. This is a corollary
of expected accounting, so clients can instead use sharper state-dependent charges. -/
theorem expectedCharge_le_of_totalRollBound {α : Type*} (concrete : KernelHandler P S)
    [∀ a, IsSubprobabilityKernel (concrete a)] (charge : P.A → S → ℝ≥0∞)
    (ε : ℝ≥0∞) (hcharge : ∀ a s, charge a s ≤ ε)
    (program : FreeM P α) (n : ℕ) (hbound : program.IsTotalRollBound n) (s : S) :
    expectedCharge concrete charge program s ≤ n * ε := by
  induction program generalizing n s with
  | pure x => simp
  | lift_bind a next ih =>
      rw [← FreeM.liftBind_eq, FreeM.isTotalRollBound_liftBind_iff] at hbound
      cases n with
      | zero => omega
      | succ n =>
          rw [← FreeM.liftBind_eq, expectedCharge_liftBind]
          calc
            _ ≤ ε + ∫⁻ _ : P.B a × S, (n : ℝ≥0∞) * ε ∂concrete a s :=
              add_le_add (hcharge a s) (lintegral_mono fun out =>
                ih out.1 n (by simpa using hbound.2 out.1) out.2)
            _ ≤ ε + n * ε := by
              rw [lintegral_const]
              exact add_le_add le_rfl (mul_le_of_le_one_right' (measure_univ_le _))
            _ = (n + 1 : ℕ) * ε := by simp [Nat.cast_add, add_mul, add_comm]

namespace ApproxReconstructionContract

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  {concrete : KernelHandler P S} {ideal : KernelHandler P T}
  [∀ a, IsSubprobabilityKernel (ideal a)] {R : Kernel S T} {charge : P.A → S → ℝ≥0∞}
  (contract : ApproxReconstructionContract concrete ideal R charge)
  {α : Type*} [MeasurableSpace α]

include contract

/-- Adaptive composition accumulates local reconstruction error in expectation under the
concrete execution. The distance uses the event-supremum normalization. -/
theorem runKernel_le_expectedCharge (program : FreeM P α) (state : S) :
    ((FreeM.runKernel ideal program ∘ₖ R) state).etvDist
      ((Kernel.retainLeft α R ∘ₖ FreeM.runKernel concrete program) state) ≤
        expectedCharge concrete charge program state := by
  let := contract.isMarkov
  simp only [Kernel.comp_apply]
  induction program generalizing state with
  | pure x =>
      rw [show ⇑(FreeM.runKernel ideal (pure x)) =
        (fun t => Measure.dirac (x, t)) from funext (FreeM.runKernel_pure ideal x)]
      simp only [FreeM.runKernel_pure, expectedCharge_pure]
      rw [Measure.dirac_bind (Kernel.retainLeft α R).measurable,
        Kernel.retainLeft_apply, Measure.bind_dirac_eq_map _ measurable_prodMk_left]
      exact le_of_eq (Measure.etvDist_self _)
  | lift_bind a next ih =>
      simp only [← FreeM.liftBind_eq, expectedCharge_liftBind]
      rw [show ⇑(FreeM.runKernel ideal (.liftBind a next)) =
        (fun t => (ideal a t).bind fun out => FreeM.runKernel ideal (next out.1) out.2)
        from funext (FreeM.runKernel_liftBind ideal a next), FreeM.runKernel_liftBind]
      let ki : Kernel (P.B a × T) (α × T) :=
        ⟨fun out => FreeM.runKernel ideal (next out.1) out.2,
          FreeM.measurable_runKernel_continuation ideal next⟩
      have hki : IsSubprobabilityKernel ki := ⟨fun out => by
        change FreeM.runKernel ideal (next out.1) out.2 Set.univ ≤ 1
        exact measure_univ_le _⟩
      have hmC := FreeM.measurable_runKernel_continuation concrete next
      have hmI := FreeM.measurable_runKernel_continuation ideal next
      rw [← Measure.bind_bind (ideal a).aemeasurable hmI.aemeasurable,
        Measure.bind_bind hmC.aemeasurable (Kernel.retainLeft α R).aemeasurable]
      have hfirst := (Measure.etvDist_bind_le ((ideal a ∘ₖ R) state)
        ((Kernel.retainLeft (P.B a) R ∘ₖ concrete a) state) ki ki.measurable).trans
          (contract.step a state)
      apply (Measure.etvDist_triangle _
        (((Kernel.retainLeft (P.B a) R ∘ₖ concrete a) state).bind ki) _).trans
      refine add_le_add hfirst ?_
      rw [Kernel.comp_apply, Measure.bind_bind
        (Kernel.retainLeft (P.B a) R).aemeasurable ki.aemeasurable]
      apply Measure.etvDist_bind_bind_le_lintegral _ _ _
        ((Measure.measurable_bind' ki.measurable).comp
          (Kernel.retainLeft (P.B a) R).measurable).aemeasurable
        ((Measure.measurable_bind' (Kernel.retainLeft α R).measurable).comp hmC).aemeasurable
      exact Filter.Eventually.of_forall fun out => by
        simp only [Function.comp_apply]
        rw [Kernel.bind_retainLeft R _ ki.measurable]
        exact ih out.1 out.2

/-- A local potential is a whole-client reconstruction-error budget. -/
theorem runKernel_le_potential (budget : S → ℝ≥0∞)
    (hstep : ∀ a s, charge a s + ∫⁻ out, budget out.2 ∂concrete a s ≤ budget s)
    (program : FreeM P α) (s : S) :
    ((FreeM.runKernel ideal program ∘ₖ R) s).etvDist
      ((Kernel.retainLeft α R ∘ₖ FreeM.runKernel concrete program) s) ≤ budget s :=
  (contract.runKernel_le_expectedCharge program s).trans
    (expectedCharge_le_potential concrete charge budget hstep program s)

/-- An initial reconstruction error and the actual expected running charges bound the final
joint law. The concrete initial law supplies the reference expectation. -/
theorem bind_state_laws_le (μ : Measure S) (ν : Measure T) (program : FreeM P α) :
    (ν.bind (FreeM.runKernel ideal program)).etvDist
      ((μ.bind (FreeM.runKernel concrete program)).bind (Kernel.retainLeft α R)) ≤
        ν.etvDist (μ.bind R) + ∫⁻ s, expectedCharge concrete charge program s ∂μ := by
  have hfirst := Measure.etvDist_bind_le ν (μ.bind R)
    (FreeM.runKernel ideal program) (FreeM.runKernel ideal program).measurable
  apply (Measure.etvDist_triangle _ ((μ.bind R).bind (FreeM.runKernel ideal program)) _).trans
  refine add_le_add hfirst ?_
  rw [Measure.bind_bind R.aemeasurable (FreeM.runKernel ideal program).aemeasurable,
    Measure.bind_bind (FreeM.runKernel concrete program).aemeasurable
      (Kernel.retainLeft α R).aemeasurable]
  exact Measure.etvDist_bind_bind_le_lintegral μ
    (FreeM.runKernel ideal program ∘ₖ R)
    (Kernel.retainLeft α R ∘ₖ FreeM.runKernel concrete program)
    (Kernel.aemeasurable _) (Kernel.aemeasurable _) _
    (Filter.Eventually.of_forall (contract.runKernel_le_expectedCharge program))

/-- Hiding private states cannot increase the reconstruction error. -/
theorem output_law_le (μ : Measure S) (ν : Measure T) (program : FreeM P α) :
    ((ν.bind (FreeM.runKernel ideal program)).map Prod.fst).etvDist
      ((μ.bind (FreeM.runKernel concrete program)).map Prod.fst) ≤
        ν.etvDist (μ.bind R) + ∫⁻ s, expectedCharge concrete charge program s ∂μ := by
  let := contract.isMarkov
  rw [← Kernel.map_fst_bind_retainLeft R (μ.bind (FreeM.runKernel concrete program))]
  exact (Measure.etvDist_map_le _ _ _ measurable_fst).trans
    (contract.bind_state_laws_le μ ν program)

end ApproxReconstructionContract

end PFunctor.KernelHandler
