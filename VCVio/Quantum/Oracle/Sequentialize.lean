/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.Sequentialize
public import VCVio.Quantum.Oracle.Parallel

/-!
# Sequentialization in the quantum random-oracle model

Ordered single-point execution of a parallel QROM program preserves its output law and every
observation depending on the sampled function and the classical leaf. Both executions use the
same function `H : X → Y` throughout all slots and rounds, so the equality retains the correlation
between `H` and the returned data.
-/

public section

open MeasureTheory

universe u v w w₁

namespace Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- Sequentializing a parallel QROM program preserves its averaged output law. The random
function is sampled once for the complete execution on each side. -/
theorem qromEvalDist_sequentialize [AddCommGroup Y] [MeasurableSpace (Σ a, W a)] (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A) :
    qromEvalDist .instruments (x.sequentialize I) ρ = qromBatchEvalDist I x ρ := by
  rw [qromEvalDist, qromBatchEvalDist, sampledEvalDist_eq_sum, sampledEvalDist_eq_sum]
  congr 1
  exact Finset.sum_congr rfl fun H _ ↦
    (additiveOracleRuntime H).evalDist_sequentialize I x ρ

/-- Sequentialization preserves every observation of the jointly sampled function and classical
leaf. In particular, a challenger may test a relation between the returned data and the same
hidden function used by all oracle calls; the observation need not be measurable. -/
theorem qromEvalDistMap_sequentialize [AddCommGroup Y] {β : Type w₁}
    [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A)
    (f : (X → Y) → (Σ a, W a) → β) :
    qromEvalDistMap .instruments (x.sequentialize I) ρ f =
      sampledEvalDistMap parallelOracleRuntime I x ρ f := by
  rw [qromEvalDistMap, sampledEvalDistMap_eq_sum, sampledEvalDistMap_eq_sum]
  congr 1
  exact Finset.sum_congr rfl fun H _ ↦
    (additiveOracleRuntime H).evalDistMap_sequentialize I x ρ (f H)

/-- A parallel point budget bounds the single QROM port after sequentialization. -/
theorem QuantumComp.IsPointBound.qrom_sequentialize (I : L.Interp)
    {x : QuantumComp L (qromBatchSpec X Y) W A} {n : ℕ} (hx : x.IsPointBound n) :
    (x.sequentialize I).IsQueryBound (fun _ ↦ n) :=
  (QuantumComp.isTotalQueryBound_iff_isQueryBound
    (s := qromSpec X Y) (x.sequentialize I) n).mp (hx.sequentialize I)

end Quantum
