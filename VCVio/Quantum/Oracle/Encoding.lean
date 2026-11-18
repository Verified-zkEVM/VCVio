/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.Parallel
public import ToMathlib.MeasureTheory.Measure.UniformTable.Encoding

/-!
# Exact table encodings for quantum oracle programs

A bijective change of the sampled oracle parameter preserves the observed law of a complete
quantum execution. The observation may depend jointly on that parameter and the final leaf.
Splitting a raw table into visible encoded responses, fixed response tails and all outside-image
cells therefore preserves every program over the original raw-query signature.

The query signature stays fixed while the sampled table is reparameterized. The adversary
retains coherent access to all raw inputs and full responses. Security against these programs
requires a separate oracle argument.
-/

public section

open MeasureTheory

namespace Quantum

universe u v u₁ v₁ w

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}}
  {W : QReg → Type w} {A : QReg}

/-- A bijective reparameterization of a uniformly sampled runtime preserves the joint observed
law. Runtime-private registers and adaptive branches are retained by each complete execution. -/
theorem sampledEvalDistMap_equiv {Ω Ω' : Type*} [Finite Ω] [Finite Ω']
    (e : Ω ≃ Ω') (R : Ω' → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A) {β : Type*} [MeasurableSpace β]
    (f : Ω' → (Σ B, W B) → β) :
    sampledEvalDistMap R I x ρ f =
      sampledEvalDistMap (fun ω ↦ R (e ω)) I x ρ (fun ω ↦ f (e ω)) := by
  let : MeasurableSpace Ω := ⊤
  let : MeasurableSpace Ω' := ⊤
  exact ProbabilityTheory.uniformOn_univ_bind_equiv e
    (fun ω ↦ (R ω).evalDistMap I x ρ (f ω))

/-- Reparameterization preserves the leaf distribution without a parameter-dependent observer. -/
theorem sampledEvalDist_equiv {Ω Ω' : Type*} [Finite Ω] [Finite Ω']
    (e : Ω ≃ Ω') (R : Ω' → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A) [MeasurableSpace (Σ B, W B)] :
    sampledEvalDist R I x ρ = sampledEvalDist (fun ω ↦ R (e ω)) I x ρ :=
  sampledEvalDistMap_equiv e R I x ρ (fun _ leaf ↦ leaf)

section tableSplit

variable {D I M : Type} {Answer Tail : I → Type}
  [Fintype D] [DecidableEq D] [Fintype M] [DecidableEq M] [AddCommGroup M]

/-- Completing a split finite raw table and running any raw parallel-oracle program gives
exactly its original QROM law. The observation may inspect the same completed table that
answered every query. All mask tails and outside-image responses remain in the parameter. -/
theorem sampledEvalDistMap_tableSplit
    (encode : I → D) (hinj : Function.Injective encode)
    (split : ∀ i, M ≃ Answer i × Tail i) (interp : L.Interp)
    (x : QuantumComp L (qromBatchSpec D M) W A) (ρ : SubState A)
    {β : Type*} [MeasurableSpace β] (f : (D → M) → (Σ B, W B) → β) :
    sampledEvalDistMap (fun H : D → M ↦ parallelOracleRuntime H) interp x ρ f =
      sampledEvalDistMap
        (fun tables ↦ parallelOracleRuntime ((Equiv.tableSplit encode hinj split).symm tables))
        interp x ρ (fun tables ↦ f ((Equiv.tableSplit encode hinj split).symm tables)) := by
  have : Finite (((∀ i, Answer i) × (∀ i, Tail i)) ×
      ({z : D // z ∉ Set.range encode} → M)) :=
    Finite.of_equiv (D → M) (Equiv.tableSplit encode hinj split)
  exact sampledEvalDistMap_equiv (Equiv.tableSplit encode hinj split).symm
    parallelOracleRuntime interp x ρ f

end tableSplit

end Quantum
