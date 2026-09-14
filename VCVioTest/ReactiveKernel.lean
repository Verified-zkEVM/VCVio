/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Interaction.UC.ReactiveKernel
public import VCVio.Interaction.UC.ReactiveSecurity

/-!
# Joint-kernel replacement and its response-only counterexample

A two-operation machine stores a bit and reads it back. Both implementations return the
same immediate response to every call, yet their differing retained state changes the final
observation. A separate positive test inserts discarded local randomness while preserving the
joint response/state law; the generic replacement theorem applies to every execution horizon.
-/

public section

namespace Interaction.UC.ReactiveKernel.Tests

open PFunctor ReactiveProcess ReactiveNetwork DynSystem OracleComp MeasureTheory

@[expose] def effect : PFunctor.{0, 0} := ⟨Bool, fun _ => Bool⟩

@[expose] def network : Network Unit PortBoundary.empty Bool where
  effect _ := effect
  ports _ := PortBoundary.empty
  component _ := DynComputation.ofFreeM fun _ =>
    .liftBind (.effect false) fun _ =>
      .liftBind (.effect true) fun bit => .pure (.returned bit)
  route _ packet := packet.1.elim
  ingress packet := packet.1.elim
  environment := ()

attribute [local implicit_reducible] effect network

local instance (node : Unit) (operation : (network.effect node).A) :
    MeasurableSpace ((network.effect node).B operation) := inferInstanceAs (MeasurableSpace Bool)

local instance (node : Unit) (operation : (network.effect node).A) :
    DiscreteMeasurableSpace ((network.effect node).B operation × Bool) :=
  inferInstanceAs (DiscreteMeasurableSpace (Bool × Bool))

@[expose] def implementation (stored : Bool) :
    (node : Unit) → Handler (StateT Bool ProbComp) (network.effect node)
  | _, false => fun _ => pure (false, stored)
  | _, true => fun state => pure (state, state)

@[expose] def experiment (stored : Bool) (fuel : ℕ) : ProbComp ReactiveSecurity.Result :=
  ReactiveSecurity.observe <$> ReactiveRuntime.tokenExperiment network
    (implementation stored) (pure false) fuel

/-- Immediate response laws agree for every operation and every starting service state. -/
theorem response_laws_equal (node : Unit) (operation state : Bool) :
    𝒟[Prod.fst <$> (implementation false node operation).run state] =
      𝒟[Prod.fst <$> (implementation true node operation).run state] := by
  cases operation <;> rfl

/-- The retained service state makes the two complete executions distinguishable. -/
theorem response_only_replacement_false :
    𝒟[experiment false 2] ≠ 𝒟[experiment true 2] := by
  change 𝒟[(pure (some (some false)) : ProbComp ReactiveSecurity.Result)] ≠
    𝒟[(pure (some (some true)) : ProbComp ReactiveSecurity.Result)]
  intro h
  have hevent := congrArg (fun μ : Measure ReactiveSecurity.Result => μ {some (some false)}) h
  simp at hevent

/-- The joint-kernel premise correctly rejects the two response-equivalent handlers. -/
theorem joint_laws_differ :
    ¬ JointHandlerLawEq (network := network) (implementation false) (implementation true) := by
  intro h
  have hcall := h () false false
  have hevent := congrArg (fun μ : Measure (Bool × Bool) => μ {(false, false)}) hcall
  simp [implementation, StateT.run] at hevent

@[expose] def noisyImplementation :
    (node : Unit) → Handler (StateT Bool ProbComp) (network.effect node) :=
  fun node operation state => do
    let _ ← $ᵗ Bool
    (implementation false node operation).run state

/-- Discarded local randomness preserves the joint response and service-state law. -/
theorem noisy_joint_laws :
    JointHandlerLawEq (network := network) noisyImplementation (implementation false) := by
  intro node operation state
  change 𝒟[(($ᵗ Bool) >>= fun _ => (implementation false node operation).run state)] = _
  rw [evalDist_bind_const, measure_univ, one_smul]

/-- The generic theorem preserves every actual finite observation after local kernel replacement. -/
example (fuel : ℕ) :
    𝒟[ReactiveSecurity.observe <$> ReactiveRuntime.tokenExperiment network
      noisyImplementation (pure false) fuel] = 𝒟[experiment false fuel] := by
  let : MeasurableSpace (State network Bool) := ⊤
  let : DiscreteMeasurableSpace (State network Bool) := ⟨fun _ => trivial⟩
  simp only [experiment, ReactiveRuntime.tokenExperiment, pure_bind, bind_pure_comp,
    Functor.map_map]
  exact runToken_observe_congr (network := network) noisy_joint_laws fuel
    (initial network false) (ReactiveSecurity.observe ∘ outcome ())

end Interaction.UC.ReactiveKernel.Tests
