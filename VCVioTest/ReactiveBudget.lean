/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Interaction.UC.ReactiveBudget

/-!
# Probabilistic activation-budget consumer

A polynomial machine samples one local fair bit on each countdown activation. Its global
rank covers every response path and proves zero measure for unfinished execution at the
advertised horizon. A shorter prefix remains unfinished.
-/

public section

namespace Interaction.UC.ReactiveRuntime.BudgetTests

open PFunctor ReactiveProcess ReactiveNetwork DynSystem OracleComp MonadAttach MeasureTheory

@[expose] def effect : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

@[expose] def step : ℕ → Outcome Bool ⊕ (signature effect PortBoundary.empty).Obj ℕ
  | 0 => .inl (.returned true)
  | n + 1 => .inr ⟨.effect (), fun _ => n⟩

@[expose] def network (n : ℕ) : Network Unit PortBoundary.empty Bool where
  effect _ := effect
  ports _ := PortBoundary.empty
  component _ := DynComputation.ofStep step (fun _ => n)
  route _ packet := packet.1.elim
  ingress packet := packet.1.elim
  environment := ()

@[expose] def impl (n : ℕ) :
    (node : Unit) → Handler (StateT Unit ProbComp) ((network n).effect node) :=
  fun _ _ state => do
    let bit ← $ᵗ Bool
    pure (bit, state)

attribute [local implicit_reducible] network step effect signature Response

/-- Each actual response decreases the remaining counter by exactly one. -/
def budget (n : ℕ) : TokenBudgetCertificate (impl n) (fun _ => True) where
  rank state := state.localState ()
  zero state _ hz := by
    exact ⟨.returned true, by simp [outcome, network, DynComputation.view_ofStep, hz, step]⟩
  preserves _ _ _ _ := trivial
  decreases state next _ hout hstep := by
    cases state.focus
    cases hs : state.localState () with
    | zero => simp [outcome, network, DynComputation.view_ofStep, hs, step] at hout
    | succ k =>
      simp only [activate, network, DynComputation.view_ofStep, hs, step,
        canReturn_bind_iff, canReturn_pure_iff] at hstep
      obtain ⟨answer, _, rfl⟩ := hstep
      simp
  progress state _ := by
    have hnonempty : (_root_.support (activate (impl n) .token state.focus state)).Nonempty := by
      simp [Set.nonempty_iff_ne_empty, ← probFailure_eq_one_iff]
    obtain ⟨next, hnext⟩ := hnonempty
    exact ⟨next, (canReturn_iff_mem_support _ _).mpr hnext⟩

local instance : MeasurableSpace (Option (Outcome Bool)) := ⊤
local instance : DiscreteMeasurableSpace (Option (Outcome Bool)) := ⟨fun _ => trivial⟩

/-- The rank bound gives a zero-measure unfinished event for every countdown width. -/
example (n : ℕ) : tokenLaw (network n) (impl n) (pure ()) n {none} = 0 := by
  exact tokenLaw_unfinished_zero (budget n) (pure ()) n (fun _ _ => trivial)
    (fun _ _ => Nat.le_refl _)

/-- A genuinely unfinished prefix has positive unfinished mass. -/
example : tokenLaw (network 1) (impl 1) (pure ()) 0 {none} = 1 := by
  rw [tokenLaw_eq_evalDist]
  simp [tokenExperiment, runToken, initial, outcome, network, DynComputation.view_ofStep, step]

end Interaction.UC.ReactiveRuntime.BudgetTests
