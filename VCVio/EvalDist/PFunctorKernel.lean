/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import PolyFun.PFunctor.Free.Basic
public import ToMathlib.Probability.Kernel.Subprobability
public import ToMathlib.MeasureTheory.Measure.Coupling.Bind

/-!
# Stateful kernel interpretation of polynomial programs

A kernel handler jointly samples an operation's answer and the successor state. Its free
extension interprets a whole polynomial program as a kernel from initial states to results and
final states. Query answers are countable with measurable singletons, while internal states
and final results may be continuous. Countability supplies joint measurability when a returned
answer selects a continuation; no discreteness assumption is made on private states.
-/

public section

open MeasureTheory ProbabilityTheory

universe uA uB uS uR uT uQ

namespace PFunctor

/-- Joint answer-and-state kernels for the operations of a polynomial interface. -/
abbrev KernelHandler (P : PFunctor.{uA, uB}) (S : Type uS)
    [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] :=
  (a : P.A) → Kernel S (P.B a × S)

namespace FreeM

variable {P : PFunctor.{uA, uB}} {S : Type uS} {α : Type uR} {β : Type uT}
variable [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S]
variable [MeasurableSpace α] [MeasurableSpace β]

/-- Recursive answer-and-state measure; joint measurability is certified by `KernelAdmissible`. -/
@[expose] noncomputable def runStateMeasure (impl : KernelHandler P S) :
    FreeM P α → S → Measure (α × S)
  | .pure x, state => Measure.dirac (x, state)
  | .liftBind a next, state =>
      (impl a state).bind fun out => runStateMeasure impl (next out.1) out.2

/-- A local measurability certificate for the existing free syntax. At each query,
answers and successor states jointly select a measurable continuation measure. -/
@[expose] def KernelAdmissible (impl : KernelHandler P S) : FreeM P α → Prop
  | .pure _ => True
  | .liftBind a next =>
      (∀ b, KernelAdmissible impl (next b)) ∧
        Measurable (fun result : P.B a × S => runStateMeasure impl (next result.1) result.2)

@[simp] theorem kernelAdmissible_pure (impl : KernelHandler P S) (value : α) :
    KernelAdmissible impl (pure value) := True.intro

/-- An admissible program varies measurably with the initial service state. -/
theorem KernelAdmissible.measurable {impl : KernelHandler P S} {program : FreeM P α}
    (h : KernelAdmissible impl program) : Measurable (runStateMeasure impl program) := by
  induction program with
  | pure x => exact Measure.measurable_dirac.comp (measurable_const.prodMk measurable_id)
  | lift_bind a next ih =>
      exact (Measure.measurable_bind' h.2).comp (impl a).measurable

/-- Bundle an explicitly certified program's result-and-state kernel. -/
noncomputable def runKernelOfAdmissible (impl : KernelHandler P S) (program : FreeM P α)
    (h : KernelAdmissible impl program) : Kernel S (α × S) where
  toFun := runStateMeasure impl program
  measurable' := h.measurable

@[simp] theorem runKernelOfAdmissible_apply (impl : KernelHandler P S) (program : FreeM P α)
    (h : KernelAdmissible impl program) (state : S) :
    runKernelOfAdmissible impl program h state = runStateMeasure impl program state := by rfl

/-- Measurable continuation substitution commutes with the recursive measure interpretation. -/
theorem runStateMeasure_bind (impl : KernelHandler P S) (program : FreeM P α)
    (hp : KernelAdmissible impl program) (next : α → FreeM P β)
    (hn : Measurable fun result : α × S => runStateMeasure impl (next result.1) result.2)
    (state : S) :
    runStateMeasure impl (program.bind next) state =
      (runStateMeasure impl program state).bind
        (fun result => runStateMeasure impl (next result.1) result.2) := by
  induction program generalizing state with
  | pure x => exact (Measure.dirac_bind hn (x, state)).symm
  | lift_bind a rest ih =>
      change KernelAdmissible impl (.liftBind a rest) at hp
      change (impl a state).bind (fun result =>
        runStateMeasure impl ((rest result.1).bind next) result.2) =
          ((impl a state).bind fun result => runStateMeasure impl (rest result.1) result.2).bind _
      rw [Measure.bind_bind hp.2.aemeasurable hn.aemeasurable]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun result =>
        ih result.1 (hp.1 result.1) result.2)

/-- Admissibility is closed under substitution with a jointly measurable continuation. -/
theorem KernelAdmissible.bind {impl : KernelHandler P S} {program : FreeM P α}
    (hp : KernelAdmissible impl program) (next : α → FreeM P β)
    (hn : ∀ x, KernelAdmissible impl (next x))
    (hmeas : Measurable fun result : α × S => runStateMeasure impl (next result.1) result.2) :
    KernelAdmissible impl (program.bind next) := by
  induction program with
  | pure x => exact hn x
  | lift_bind a rest ih =>
      change KernelAdmissible impl (.liftBind a rest) at hp
      refine ⟨fun b => ih b (hp.1 b), ?_⟩
      change Measurable fun result : P.B a × S =>
        runStateMeasure impl ((rest result.1).bind next) result.2
      simp_rw [runStateMeasure_bind impl _ (hp.1 _) next hmeas]
      exact (Measure.measurable_bind' hmeas).comp hp.2

/-- The kernel form of sequential substitution for explicitly certified programs. -/
theorem runKernelOfAdmissible_bind (impl : KernelHandler P S) (program : FreeM P α)
    (hp : KernelAdmissible impl program) (next : α → FreeM P β)
    (hn : ∀ x, KernelAdmissible impl (next x))
    (hmeas : Measurable fun result : α × S => runStateMeasure impl (next result.1) result.2)
    (state : S) :
    runKernelOfAdmissible impl (program.bind next) (hp.bind next hn hmeas) state =
      (runKernelOfAdmissible impl program hp state).bind
        (fun result => runKernelOfAdmissible impl (next result.1) (hn result.1) result.2) :=
  runStateMeasure_bind impl program hp next hmeas state

/-- Admissibility is preserved by measurable output postprocessing. -/
theorem KernelAdmissible.map {impl : KernelHandler P S} {program : FreeM P α}
    (hp : KernelAdmissible impl program) (f : α → β) (hf : Measurable f) :
    KernelAdmissible impl (program.map f) := by
  rw [← FreeM.bind_pure_comp]
  exact hp.bind (fun a => pure (f a)) (fun _ => trivial)
    (Measure.measurable_dirac.comp ((hf.comp measurable_fst).prodMk measurable_snd))

/-- Postprocessing changes only the output component of the certified kernel. -/
theorem runKernelOfAdmissible_map (impl : KernelHandler P S) (program : FreeM P α)
    (hp : KernelAdmissible impl program) (f : α → β) (hf : Measurable f) (state : S) :
    runKernelOfAdmissible impl (program.map f) (hp.map f hf) state =
      (runKernelOfAdmissible impl program hp state).map (fun out => (f out.1, out.2)) := by
  simp only [runKernelOfAdmissible_apply, ← FreeM.bind_pure_comp]
  rw [runStateMeasure_bind impl program hp _
    (Measure.measurable_dirac.comp ((hf.comp measurable_fst).prodMk measurable_snd))]
  exact Measure.bind_dirac_eq_map _ ((hf.comp measurable_fst).prodMk measurable_snd)

/-- Certified continuous-answer programs preserve subprobability mass. -/
instance runKernelOfAdmissible.instIsSubprobabilityKernel (impl : KernelHandler P S)
    [∀ a, IsSubprobabilityKernel (impl a)] (program : FreeM P α)
    (hp : KernelAdmissible impl program) :
    IsSubprobabilityKernel (runKernelOfAdmissible impl program hp) := by
  suffices h : ∀ state, runStateMeasure impl program state Set.univ ≤ 1 from ⟨h⟩
  induction program with
  | pure x => intro state; change (Measure.dirac (x, state)) Set.univ ≤ 1; simp
  | lift_bind a next ih =>
      change KernelAdmissible impl (.liftBind a next) at hp
      intro state
      let : ∀ result : P.B a × S,
          IsSubprobabilityMeasure (runStateMeasure impl (next result.1) result.2) :=
        fun result => ⟨ih result.1 (hp.1 result.1) result.2⟩
      let := isSubprobabilityMeasure_bind (μ := impl a state) hp.2.aemeasurable
      change ((impl a state).bind fun result =>
        runStateMeasure impl (next result.1) result.2) Set.univ ≤ 1
      exact measure_univ_le _

/-- Certified programs built from total kernels preserve total probability mass. -/
instance runKernelOfAdmissible.instIsMarkovKernel (impl : KernelHandler P S)
    [∀ a, IsMarkovKernel (impl a)] (program : FreeM P α)
    (hp : KernelAdmissible impl program) :
    IsMarkovKernel (runKernelOfAdmissible impl program hp) := by
  suffices h : ∀ state, runStateMeasure impl program state Set.univ = 1 from
    ⟨fun state => ⟨h state⟩⟩
  induction program with
  | pure x =>
      intro state
      change (Measure.dirac (x, state)) Set.univ = 1
      simp
  | lift_bind a next ih =>
      change KernelAdmissible impl (.liftBind a next) at hp
      intro state
      let : ∀ result : P.B a × S,
          IsProbabilityMeasure (runStateMeasure impl (next result.1) result.2) :=
        fun result => ⟨ih result.1 (hp.1 result.1) result.2⟩
      change ((impl a state).bind fun result =>
        runStateMeasure impl (next result.1) result.2) Set.univ = 1
      rw [Measure.bind_apply MeasurableSet.univ hp.2.aemeasurable]
      simp_rw [ih _ (hp.1 _)]
      simp

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]

/-- Countable answer types automatically supply the local measurability certificates. -/
theorem kernelAdmissible_of_countable (impl : KernelHandler P S) (program : FreeM P α) :
    KernelAdmissible impl program := by
  induction program with
  | pure x => trivial
  | lift_bind a next ih =>
      exact ⟨ih, measurable_from_prod_countable_right fun b => (ih b).measurable⟩

/-- Interpret a free polynomial program as its joint result-and-state kernel. -/
noncomputable def runKernel (impl : KernelHandler P S) (program : FreeM P α) :
    Kernel S (α × S) :=
  runKernelOfAdmissible impl program (kernelAdmissible_of_countable impl program)

/-- Returning a value keeps the current state. -/
@[simp]
theorem runKernel_pure (impl : KernelHandler P S) (value : α) (state : S) :
    runKernel impl (pure value) state = Measure.dirac (value, state) := by rfl

/-- A query samples its answer and successor state jointly before running the continuation. -/
theorem runKernel_liftBind (impl : KernelHandler P S) (a : P.A)
    (next : P.B a → FreeM P α) (state : S) :
    runKernel impl (.liftBind a next) state =
      (impl a state).bind (fun out => runKernel impl (next out.1) out.2) := by rfl

/-- The continuation selected by a countable result is jointly measurable with private state. -/
theorem measurable_runKernel_continuation [Countable α] [MeasurableSingletonClass α]
    (impl : KernelHandler P S) (next : α → FreeM P β) :
    Measurable fun out : α × S => runKernel impl (next out.1) out.2 :=
  measurable_from_prod_countable_right fun x => (runKernel impl (next x)).measurable

/-- The free kernel extension preserves the per-operation subprobability invariant. -/
instance runKernel.instIsSubprobabilityKernel (impl : KernelHandler P S)
    [∀ a, IsSubprobabilityKernel (impl a)] (program : FreeM P α) :
    IsSubprobabilityKernel (runKernel impl program) := by
  unfold runKernel
  infer_instance

/-- Total service operations give total laws for well-founded clients. -/
instance runKernel.instIsMarkovKernel (impl : KernelHandler P S)
    [∀ a, IsMarkovKernel (impl a)] (program : FreeM P α) :
    IsMarkovKernel (runKernel impl program) := by
  unfold runKernel
  infer_instance

/-- Stateful interpretation respects sequential substitution. -/
theorem runKernel_bind [Countable α] [MeasurableSingletonClass α]
    (impl : KernelHandler P S) (program : FreeM P α) (next : α → FreeM P β) (state : S) :
    runKernel impl (FreeM.bind program next) state =
      (runKernel impl program state).bind fun out => runKernel impl (next out.1) out.2 := by
  simpa only [runKernel, runKernelOfAdmissible_apply] using
    runStateMeasure_bind impl program (kernelAdmissible_of_countable impl program) next
      (measurable_runKernel_continuation impl next) state

/-- An isolated query has exactly its supplied answer-and-state kernel. -/
@[simp]
theorem runKernel_lift (impl : KernelHandler P S) (a : P.A) (state : S) :
    runKernel impl (FreeM.lift a) state = impl a state := by
  change (impl a state).bind Measure.dirac = impl a state
  exact Measure.bind_dirac

variable {Q : PFunctor.{uQ, uB}} [∀ a, MeasurableSpace (Q.B a)]
  [∀ a, Countable (Q.B a)] [∀ a, MeasurableSingletonClass (Q.B a)]

/-- Interpreting an inlined polynomial handler agrees with interpreting each local handler as
a kernel first. Both sides retain the same shared private state across all calls. -/
theorem runKernel_liftM {X : Type uB} [MeasurableSpace X]
    (impl : KernelHandler Q S) (handler : (a : P.A) → FreeM Q (P.B a))
    (program : FreeM P X) (state : S) :
    runKernel impl (program.liftM handler) state =
      runKernel (fun a => runKernel impl (handler a)) program state := by
  induction program generalizing state with
  | pure x => rfl
  | lift_bind a next ih =>
      change runKernel impl ((handler a).bind (fun b => (next b).liftM handler)) state =
        (runKernel impl (handler a) state).bind
          (fun out => runKernel (fun a => runKernel impl (handler a)) (next out.1) out.2)
      rw [runKernel_bind]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun out => ih out.1 out.2)

end FreeM
end PFunctor
