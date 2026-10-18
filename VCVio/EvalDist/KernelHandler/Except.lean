/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.KernelHandler.Realizes
public import ToMathlib.MeasureTheory.MeasurableSpace.Except
public import ToMathlib.Control.Except
public import PolyFun.PFunctor.Free.Except

/-!
# Kernel correctness with explicit failure and retained state

Core `ExceptT` over `StateT` retains the service state on failure. Its finite
client law follows from `KernelHandler.Realizes.run` by exposing exceptional
answers through `PFunctor.withExcept`. The resulting measure includes errors
and their final state; no success conditioning or error-mass erasure is used.
-/

public section

open MeasureTheory ProbabilityTheory

namespace PFunctor.KernelHandler

universe uA u v

variable {P : PFunctor.{uA, u}} {S ε α : Type u} {m : Type u → Type v}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace ε]
  [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  [Countable ε] [MeasurableSingletonClass ε] [MeasurableSpace α]

/-- Local joint error/answer/state laws determine the full law of an aborting finite client. -/
theorem Realizes.runExcept {K : KernelHandler (P.withExcept ε) S}
    {handler : Handler (ExceptT ε (StateT S m)) P}
    (h : K.Realizes handler.exceptAnswers) (program : FreeM P α) (state : S) :
    𝒟[((program.liftM handler).run).run state] =
      FreeM.runKernel K program.withExcept state := by
  have hrun := h.run program.withExcept state
  change 𝒟[((program.withExcept.liftM handler.exceptAnswers).run) state] = _ at hrun
  rw [FreeM.liftM_withExcept] at hrun
  exact hrun

end PFunctor.KernelHandler

open scoped ENNReal

universe uA uB uS uE uR

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {S : Type uS} {ε : Type uE} {α : Type uR}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace ε]
  [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  [Countable ε] [MeasurableSingletonClass ε] [MeasurableSpace α]

/-- A local reserve for selected errors and the successful continuation bounds
those errors in every adaptive finite client. Unselected errors stop the client
without consuming error probability. Private states and result universes remain
arbitrary; no uniform bound on the number of calls is required. -/
theorem runKernel_withExcept_error_le
    (K : KernelHandler (P.withExcept ε) S) (errors : Set ε) (he : MeasurableSet errors)
    (budget : S → ℝ≥0∞)
    (hstep : ∀ a s, (∫⁻ out, out.1.casesOn (errors.indicator (fun _ => 1))
      (fun _ => budget out.2) ∂K a s) ≤ budget s)
    (program : FreeM P α) (s : S) :
    runKernel K program.withExcept s {out | out.1 ∈ Except.error '' errors} ≤ budget s := by
  classical
  have hm : MeasurableSet {out : Except ε α × S | out.1 ∈ Except.error '' errors} :=
    measurable_fst (Except.measurableSet_error_image.mpr he)
  induction program generalizing s with
  | pure value =>
    rw [withExcept_pure, runKernel_pure, Measure.dirac_apply' _ hm]
    simp
  | lift_bind a next ih =>
    rw [← liftBind_eq, withExcept_liftBind, runKernel_liftBind]
    erw [Measure.bind_apply hm (measurable_runKernel_continuation K
        (fun answer : (P.withExcept ε).B a => match answer with
          | .error e => FreeM.pure (.error e)
          | .ok value => (next value).withExcept)).aemeasurable]
    apply le_trans (lintegral_mono (fun out => ?_)) (hstep a s)
    obtain ⟨answer, state⟩ := out
    cases answer with
    | error e =>
      change runKernel K (pure (.error e)) state
        {out | out.1 ∈ Except.error '' errors} ≤ errors.indicator (fun _ => 1) e
      rw [runKernel_pure, Measure.dirac_apply' _ hm]
      have hmem : Except.error e ∈ (Except.error '' errors : Set (Except ε α)) ↔ e ∈ errors := by
        constructor
        · rintro ⟨e', he', h⟩
          exact Except.error.inj h ▸ he'
        · exact fun he => ⟨e, he, rfl⟩
      change (if Except.error e ∈ (Except.error '' errors : Set (Except ε α)) then 1 else 0) ≤ _
      simp only [Set.indicator, hmem, le_refl]
    | ok value => exact ih value state

end PFunctor.FreeM
