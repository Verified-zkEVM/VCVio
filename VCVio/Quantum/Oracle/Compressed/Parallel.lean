/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.Compressed.Equivalence
public import VCVio.Quantum.Oracle.Sequentialize

/-!
# Parallel compressed-oracle equivalence

Ordered batches of the compressed runtime use one database throughout every slot and round.
Their laws agree with parallel queries to one uniformly sampled function `H : X → Y`, for
arbitrary adaptive programs and mixed or subnormalized input states over any finite abelian
response group. Widths may vary between calls, including width zero.

The compressed and purified private registers are related by an isometry, which also relates
joint post-states. The comparison with a sampled function uses the sequential purified-oracle
row decomposition through exact stateful sequentialization. It does not identify the compressed
database register with the stateless fixed-function oracle's private register.
-/

public section

open MeasureTheory Matrix
open scoped Kronecker

universe u v w

namespace Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- Compression intertwines each purified oracle step with the compressed oracle step. -/
theorem intertwines_purifiedRuntime_compressedRuntime_step (i : Unit) :
    DSubInstrument.Intertwines
      ((MatrixMap.conj (compressAll X Y *
        basisMatrix (Database.ofFun : (X → Y) → Database X Y))).amplifyLeft (X × Y))
      (fun _ ↦ (MatrixMap.conj (compressAll X Y *
        basisMatrix (Database.ofFun : (X → Y) → Database X Y))).amplifyLeft (X × Y))
      ((purifiedRuntime X Y).step i) ((compressedRuntime X Y).step i) := by
  intro r
  change MatrixMap.conj (compressedOracle X Y) ∘ₗ
      (MatrixMap.conj (compressAll X Y * basisMatrix Database.ofFun)).amplifyLeft (X × Y) =
    (MatrixMap.conj (compressAll X Y * basisMatrix Database.ofFun)).amplifyLeft (X × Y) ∘ₗ
      MatrixMap.conj (tableOracle (id : (X → Y) → X → Y))
  rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
    compressedOracle_mul_one_kronecker_compressAll_mul_basisMatrix]

/-- Compression intertwines whole batches, retaining one shared private database. -/
theorem intertwines_purifiedRuntime_compressedRuntime_batch_step (ik : Unit × ℕ) :
    DSubInstrument.Intertwines
      ((MatrixMap.conj (compressAll X Y *
        basisMatrix (Database.ofFun : (X → Y) → Database X Y))).amplifyLeft
          (Fin ik.2 → X × Y))
      (fun _ ↦ (MatrixMap.conj (compressAll X Y *
        basisMatrix (Database.ofFun : (X → Y) → Database X Y))).amplifyLeft
          (Fin ik.2 → X × Y))
      ((purifiedRuntime X Y).batch.step ik) ((compressedRuntime X Y).batch.step ik) :=
  QuantumRuntime.intertwines_batch_step (In := fun _ : Unit ↦ QReg.of (X × Y))
    (R := purifiedRuntime X Y) (S := compressedRuntime X Y) _
    intertwines_purifiedRuntime_compressedRuntime_step ik

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- At every leaf, the complete compressed joint post-state is the compression isometry
applied to the purified joint post-state, including the runtime's private memory. -/
theorem matrix_jointPost_compressedRuntime_batch (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A) (p : Σ a, W a) :
    ((compressedRuntime X Y).batch.jointPost I x ρ p).matrix =
      (MatrixMap.conj (compressAll X Y *
        basisMatrix (Database.ofFun : (X → Y) → Database X Y))).amplifyLeft p.1
          ((purifiedRuntime X Y).batch.jointPost I x ρ p).matrix :=
  QuantumRuntime.matrix_jointPost_of_simulation (R₁ := (purifiedRuntime X Y).batch)
    (R₂ := (compressedRuntime X Y).batch) I
    intertwines_purifiedRuntime_compressedRuntime_batch_step
    conj_compressAll_mul_basisMatrix_uniformFunctionState x ρ p

/-- Discarding private memory leaves identical program post-states in the compressed and
purified parallel executions. -/
theorem reducedPost_compressedRuntime_batch (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A) (p : Σ a, W a) :
    (compressedRuntime X Y).batch.reducedPost I x ρ p =
      (purifiedRuntime X Y).batch.reducedPost I x ρ p :=
  QuantumRuntime.reducedPost_eq_of_simulation (R₁ := (purifiedRuntime X Y).batch)
    (R₂ := (compressedRuntime X Y).batch) I
    intertwines_purifiedRuntime_compressedRuntime_batch_step
    (MatrixMap.isTP_conj conjTranspose_compressAll_mul_basisMatrix_mul_self)
    conj_compressAll_mul_basisMatrix_uniformFunctionState x ρ p

/-- Every leaf of a parallel program has the same weight against the compressed and purified
runtimes. -/
theorem trace_jointPost_compressedRuntime_batch (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A) (p : Σ a, W a) :
    ((compressedRuntime X Y).batch.jointPost I x ρ p).matrix.trace =
      ((purifiedRuntime X Y).batch.jointPost I x ρ p).matrix.trace := by
  rw [← QuantumRuntime.jointPost_sequentialize, ← QuantumRuntime.jointPost_sequentialize]
  exact trace_jointPost_compressedRuntime .instruments (x.sequentialize I) ρ p

/-- Every classical observation of a parallel program's leaf has the same law against the
compressed and purified runtimes. -/
theorem outcomeLawWith_compressedRuntime_batch_eq_purifiedRuntime {γ : Type*}
    [MeasurableSpace γ] (I : L.Interp) (x : QuantumComp L (qromBatchSpec X Y) W A)
    (ρ : SubState A) (f : (Σ a, W a) → γ) :
    (compressedRuntime X Y).batch.evalDistMap I x ρ f =
      (purifiedRuntime X Y).batch.evalDistMap I x ρ f := by
  rw [← QuantumRuntime.evalDistMap_sequentialize, ← QuantumRuntime.evalDistMap_sequentialize]
  exact outcomeLawWith_compressedRuntime_eq_purifiedRuntime .instruments (x.sequentialize I) ρ f

/-- Each parallel purified leaf weight is the uniform average of fixed-function parallel
leaf weights. The sum over functions is the non-trace-preserving row-decomposition leg. -/
theorem trace_jointPost_purifiedRuntime_batch (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A) (p : Σ a, W a) :
    ((purifiedRuntime X Y).batch.jointPost I x ρ p).matrix.trace =
      ∑ H : X → Y, (Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X *
        ((parallelOracleRuntime H).jointPost I x ρ p).matrix.trace := by
  calc
    _ = ((purifiedRuntime X Y).jointPost .instruments (x.sequentialize I) ρ p).matrix.trace :=
      congrArg (fun σ ↦ σ.matrix.trace)
        ((purifiedRuntime X Y).jointPost_sequentialize I x ρ p).symm
    _ = ∑ H : X → Y, (Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X *
        ((additiveOracleRuntime H).jointPost .instruments (x.sequentialize I) ρ p).matrix.trace :=
      trace_jointPost_purifiedRuntime .instruments (x.sequentialize I) ρ p
    _ = _ := Finset.sum_congr rfl fun H _ ↦ congrArg
      ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X * ·)
      (congrArg (fun σ ↦ σ.matrix.trace)
        ((additiveOracleRuntime H).jointPost_sequentialize I x ρ p))

/-- The purified parallel runtime realizes observations of the parallel QROM law, sampling
one function for all slots and all rounds. -/
theorem outcomeLawWith_purifiedRuntime_batch {γ : Type*} [MeasurableSpace γ]
    (I : L.Interp) (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A)
    (f : (Σ a, W a) → γ) :
    (purifiedRuntime X Y).batch.evalDistMap I x ρ f =
      sampledEvalDistMap parallelOracleRuntime I x ρ (fun _ ↦ f) := by
  rw [← QuantumRuntime.evalDistMap_sequentialize, outcomeLawWith_purifiedRuntime,
    qromEvalDistMap_sequentialize]

/-- The compressed parallel runtime has exactly the parallel QROM law for every classical
observation of the program's leaf, with one random function shared by the complete execution. -/
theorem outcomeLawWith_compressedRuntime_batch {γ : Type*} [MeasurableSpace γ]
    (I : L.Interp) (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A)
    (f : (Σ a, W a) → γ) :
    (compressedRuntime X Y).batch.evalDistMap I x ρ f =
      sampledEvalDistMap parallelOracleRuntime I x ρ (fun _ ↦ f) := by
  rw [outcomeLawWith_compressedRuntime_batch_eq_purifiedRuntime,
    outcomeLawWith_purifiedRuntime_batch]

/-- The output law against the compressed parallel runtime is the parallel QROM output law. -/
theorem outcomeLaw_compressedRuntime_batch [MeasurableSpace (Σ a, W a)] (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A) :
    (compressedRuntime X Y).batch.evalDist I x ρ = qromBatchEvalDist I x ρ := by
  rw [← QuantumRuntime.evalDist_sequentialize, outcomeLaw_compressedRuntime,
    qromEvalDist_sequentialize]

end Quantum
