/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.MachinePath.Constructions
public import PolyFun.PFunctor.Dynamical.DynComputation.Observe
public import ToMathlib.MeasureTheory.MeasurableSpace.TypeTags

/-!
# Measurable accumulation along countable-state machines

A countable machine state permits arbitrary state-dependent observations of
discrete answers. The accumulated value itself may be continuous, provided its
monoid multiplication is jointly measurable. Bounded laws and the full residual
path law retain accumulated observations even when execution pauses.

The original machine's step measurability alone does not certify an arbitrary
observation: that observation may reveal information discarded by its state.
This constructor uses countable states and discrete answer spaces explicitly.
-/

public section

open MeasureTheory ProbabilityTheory

namespace PFunctor.DynSystem.DynComputation

variable {P : PFunctor} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
  [∀ a, DiscreteMeasurableSpace (P.B a)] {α β W : Type*}
  [MeasurableSpace β] [Monoid W] [MeasurableSpace W] [MeasurableMul₂ W]
  (machine : DynComputation P α β) [MeasurableSpace machine.State]
  [Countable machine.State] [MeasurableSingletonClass machine.State]

/-- A continuous initial accumulator varies measurably through each bounded execution. -/
theorem measurable_unrollChunk_withAccumulator (observe : machine.toDynSystem.EventMap W)
    (fuel : ℕ) :
    Measurable (fun input : machine.State × W =>
      FreeM.denote ((machine.withAccumulator observe).unrollChunk fuel input)) := by
  let kernel : Kernel (machine.State × W)
      (Chunk (machine.State × W) (β × W)) :=
    ⟨fun input => FreeM.denote ((machine.withAccumulator observe).unrollChunk fuel (input.1, 1)),
      (measurable_of_countable (fun state : machine.State =>
        FreeM.denote ((machine.withAccumulator observe).unrollChunk fuel (state, 1)))).comp
          measurable_fst⟩
  let : IsMarkovKernel kernel := ⟨fun _ => FreeM.isProbabilityMeasure_denote _⟩
  have hm : Measurable (fun input : (machine.State × W) ×
      Chunk (machine.State × W) (β × W) =>
        input.2.map (fun out => (out.1, input.1.2 * out.2))
          (fun out => (out.1, input.1.2 * out.2))) :=
    Chunk.measurable_map_withInput
      (measurable_snd.fst.prodMk (measurable_fst.snd.mul measurable_snd.snd))
      (measurable_snd.fst.prodMk (measurable_fst.snd.mul measurable_snd.snd))
  convert kernel.measurable_map_withInput hm using 1
  funext input
  have hrun := machine.unrollChunk_withAccumulator_mul observe fuel input.1 input.2 1
  rw [mul_one] at hrun
  rw [hrun]
  exact FreeM.denote_map_of_measurable _ _
    (Chunk.measurable_map
      (measurable_fst.prodMk (measurable_const.mul measurable_snd))
      (measurable_fst.prodMk (measurable_const.mul measurable_snd)))

/-- Countable control state and measurable initialization support continuous accumulators. -/
theorem MeasurableExecution.withAccumulator_of_countable
    [MeasurableSpace α]
    (observe : machine.toDynSystem.EventMap W) (hinit : Measurable machine.init) :
    MeasurableExecution (machine.withAccumulator observe) where
  initial := (machine.measurable_unrollChunk_withAccumulator observe 0).comp
    ((hinit.comp measurable_fst).prodMk measurable_snd)
  step := by
    have hdone : Measurable (fun value : β × W => FreeM.denote
        ((machine.withAccumulator observe).resumeChunk 1 (.done value))) := by
      change Measurable (fun value : β × W =>
        Measure.dirac (.done value : Chunk (machine.State × W) (β × W)))
      exact Measure.measurable_dirac.comp Chunk.measurable_done
    convert Chunk.measurable_elim hdone
      (machine.measurable_unrollChunk_withAccumulator observe 1) using 1
    funext chunk
    cases chunk <;> rfl

end PFunctor.DynSystem.DynComputation
