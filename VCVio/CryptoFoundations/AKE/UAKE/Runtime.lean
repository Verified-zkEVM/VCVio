/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Coherent interpretations of UAKE computations

The structural protocol constraints and the observed experiment must describe the same
computation. `RuntimeCoherent` connects a bundled runtime to lawful native measure semantics,
certifies the public-randomness interpretation, and places its discrete output measure on
operational support. It asserts concentration, not positive mass for every reachable output.

The certificate applies to direct lawful interpretations. Hiding an evolving state does not
automatically preserve bind; such a runtime needs a joint-state interpretation before this
certificate can be established. Raw experiment scores remain definable for uncertified runtimes.
-/

public section

open MeasureTheory OracleComp

namespace AKE.UAKE

variable {m : Type → Type} [Monad m] [MonadAttach m]
  [EvalDistSemantics m]

/-- The runtime observes the chosen lawful semantics, preserves public sampling, and respects
the computation's structural output set. -/
structure RuntimeCoherent (runtime : ProbCompRuntime m) : Prop where
  /-- The chosen native interpretation satisfies its pure and measurable bind laws. -/
  lawful : LawfulEvalDistSemantics m
  /-- Runtime observation agrees with the native interpretation in every output space. -/
  evalDist_eq : ∀ {α : Type} [MeasurableSpace α] (mx : m α), runtime.evalDist mx = 𝒟[mx]
  /-- Lifting public randomness does not change its distribution. -/
  lift_evalDist_eq : ∀ {α : Type} [MeasurableSpace α] (mx : ProbComp α),
    𝒟[runtime.liftProbComp mx] = 𝒟[mx]
  /-- Observed outputs are structurally reachable almost surely. -/
  ae_mem_support : ∀ {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] (mx : m α),
    ∀ᵐ x ∂𝒟[mx], x ∈ support mx

/-- The canonical native probability runtime is coherent. -/
theorem runtimeCoherent_probComp : RuntimeCoherent ProbCompRuntime.probComp where
  lawful := inferInstance
  evalDist_eq _ := rfl
  lift_evalDist_eq _ := rfl
  ae_mem_support mx := OracleComp.ae_of_forall_mem_support mx _ fun _ hx ↦ hx

/-- A structural invariant holds almost surely under the certified runtime. -/
theorem RuntimeCoherent.ae_of_forall_mem_support {runtime : ProbCompRuntime m}
    (h : RuntimeCoherent runtime) {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (p : α → Prop) (hp : ∀ x ∈ support mx, p x) :
    ∀ᵐ x ∂runtime.evalDist mx, p x := by
  rw [h.evalDist_eq]
  exact (h.ae_mem_support mx).mono fun x hx ↦ hp x hx

end AKE.UAKE
