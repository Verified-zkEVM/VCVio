/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.PFunctorKernel

/-!
# Transport of stateful polynomial kernels

A measurable state observation that commutes with each local operation commutes with every
adaptive polynomial program. The local equations need only hold on an almost-everywhere
invariant. This supports projections from coupled private states to their two marginals.
-/

public section

open MeasureTheory ProbabilityTheory

universe uA uB uS uT uR

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {S : Type uS} {T : Type uT} {α : Type uR}
  [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace α]

/-- A local almost-everywhere invariant is preserved by every polynomial program. -/
theorem runKernel_ae_invariant (impl : KernelHandler P S) {I : S → Prop}
    (hI : MeasurableSet {s | I s})
    (hstep : ∀ a s, I s → ∀ᵐ out ∂impl a s, I out.2)
    (program : FreeM P α) {state : S} (hstate : I state) :
    ∀ᵐ out ∂runKernel impl program state, I out.2 := by
  induction program generalizing state with
  | pure x =>
      rw [runKernel_pure]
      exact (ae_dirac_iff (hI.preimage measurable_snd)).2 hstate
  | lift_bind a next ih =>
      rw [runKernel_liftBind]
      exact Measure.ae_bind_of_ae (measurable_runKernel_continuation impl next)
        (hI.preimage measurable_snd) ((hstep a state hstate).mono fun out hout => ih out.1 hout)

/-- A state projection respecting local kernels on an invariant respects whole programs. -/
theorem map_runKernel_state (impl : KernelHandler P S) (target : KernelHandler P T)
    (observe : S → T) (hobserve : Measurable observe) {I : S → Prop}
    (hstep : ∀ a s, I s →
      (impl a s).map (fun out => (out.1, observe out.2)) = target a (observe s))
    (hinvariant : ∀ a s, I s → ∀ᵐ out ∂impl a s, I out.2)
    (program : FreeM P α) {state : S} (hstate : I state) :
    (runKernel impl program state).map (fun out => (out.1, observe out.2)) =
      runKernel target program (observe state) := by
  have hm : Measurable (fun out : α × S => (out.1, observe out.2)) :=
    measurable_fst.prodMk (hobserve.comp measurable_snd)
  have hq (a : P.A) : Measurable (fun out : P.B a × S => (out.1, observe out.2)) :=
    measurable_fst.prodMk (hobserve.comp measurable_snd)
  induction program generalizing state with
  | pure x => simp only [runKernel_pure, Measure.map_dirac' hm]
  | lift_bind a next ih =>
      rw [runKernel_liftBind, runKernel_liftBind]
      rw [Measure.map_bind _ (measurable_runKernel_continuation impl next) hm]
      rw [Measure.bind_congr_right ((hinvariant a state hstate).mono fun out hout =>
        ih out.1 hout)]
      rw [← Measure.bind_map _ (hq a) (measurable_runKernel_continuation target next),
        hstep a state hstate]

end PFunctor.FreeM
