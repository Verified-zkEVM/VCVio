/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.OracleComp.ProbCompLift
import VCVio.OracleComp.EvalDist.Measure

/-!
# Runtime laws for sequential sampling

A probability runtime supplies measurable map transport but does not require its native bind to
have integral semantics. These explicit laws interpret pure outputs and successive native draws
without conditioning on termination or discarding missing mass.
-/

public section

namespace ProbCompRuntime

universe v

variable {m : Type → Type v} [Monad m]

/-- Native pure and bind semantics on discrete event observations. -/
structure SamplingLaws (runtime : ProbCompRuntime m) : Prop where
  /-- Pure computations denote the Dirac measure. -/
  pure_eq : ∀ {α : Type} (x : α),
    letI : MeasurableSpace α := ⊤
    runtime.evalDist (pure x) = MeasureTheory.Measure.dirac x
  /-- A native bind integrates continuation-event mass without normalization. -/
  bind_eq : ∀ {α β : Type} (c : m α) (f : α → m β) (p : β → Prop),
    letI : MeasurableSpace α := ⊤
    runtime.evalDist (p <$> (c >>= f)) {True} =
      ∫⁻ x, runtime.evalDist (p <$> f x) {True} ∂runtime.evalDist c

/-- The canonical probability runtime preserves pure outputs and sequential sampling. -/
theorem samplingLaws_probComp : SamplingLaws probComp where
  pure_eq x := by simp [probComp_evalDist]
  bind_eq {α} {β} c f p := by
    let : MeasurableSpace α := ⊤
    simpa only [probComp_evalDist, ← prEvent_eq_evalDist_map]
      using prEvent_bind_eq_lintegral_of_discrete c f p

end ProbCompRuntime
