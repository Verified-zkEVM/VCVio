/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.Parallel
public import VCVio.Quantum.Comp.Finisher

/-!
# Fixed-oracle execution as a local observation

A fixed-function parallel oracle has trivial private memory. Its complete execution can be
packaged as a local physical operation which retains its classical output. This preserves the
observed law for arbitrary joint input states, while using no further oracle queries.
-/

public section

open MeasureTheory

namespace Quantum

universe u v w

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The fixed-function run with its trivial private register explicit in the type. -/
@[expose]
noncomputable def parallelRunUnit (I : L.Interp) (H : X → Y)
    (x : QuantumComp L (qromBatchSpec X Y) W A) :
    DSubInstrument (A × Unit) (Σ B, W B) (fun leaf ↦ leaf.1 × Unit) :=
  (parallelOracleRuntime H).run I x

/-- The explicit-unit run is the full parallel execution, with no state discarded. -/
theorem parallelRunUnit_eq (I : L.Interp) (H : X → Y)
    (x : QuantumComp L (qromBatchSpec X Y) W A) :
    parallelRunUnit I H x = (parallelOracleRuntime H).run I x := rfl

/-- Observing a local execution under a fixed oracle preserves its classical output law on
any retained joint input state. -/
theorem map_outcomeMeasure_parallel_localObservation {Out : Type} (H : X → Y)
    (p : DSubInstrument (A × Unit) (Σ _B : QReg, Out) (fun leaf ↦ leaf.1 × Unit))
    (σ : SubState (A × Unit)) :
    letI : MeasurableSpace Out := ⊤
    letI : MeasurableSpace (Σ _B : QReg, Out) := ⊤
    (((parallelOracleRuntime H).run .instruments
      (QuantumComp.localObservation (spec := qromBatchSpec X Y) p)).outcomeMeasure σ).map
        (fun leaf ↦ leaf.2) = (p.outcomeMeasure σ).map (fun leaf ↦ leaf.2) := by
  let : MeasurableSpace Out := ⊤
  let : MeasurableSpace (Σ _B : QReg, Out) := ⊤
  exact (QuantumRuntime.map_outcomeMeasure_run_localObservation
    (parallelOracleRuntime H) p σ).trans
      (DSubInstrument.outcomeMeasure_frame_dropUnit_observe p _ Measurable.of_discrete σ)

end Quantum
