/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Std.WP
public import VCVio.Interaction.UC.Runtime
import VCVio.ProgramLogic.Unary.WP.Necessary

/-!
# Hoare triples for the Interaction / UC runtime

Core `Std.WP` triples for the runtime primitives of `VCVio.Interaction.UC.Runtime`,
`Concurrent.StepOver.sample` and `Concurrent.ProcessOver.runSteps`, so that invariants of UC
executions are proved in the style of `VCVio.ProgramLogic.Unary.HandlerSpecs`.

`StepOver.sample` maps a continuation over `TypeTree.samplePath`, and `ProcessOver.runSteps`
recurses on its fuel; neither is a `do` block that core's `vcgen` walks. `StepOver.sample_eq`
states the map as a bind, and `ProcessOver.runSteps_zero` / `ProcessOver.runSteps_succ` are the
recursion equations, all `@[simp]`. `ProcessOver.runSteps_triple_preserves_invariant` lifts a
per-step invariant triple to any number of steps by induction on the fuel, with
`Std.WP.Triple.pure` and `Std.WP.Triple.bind`.

Every statement is for an arbitrary monad `m` under an arbitrary `WPMonad m Pred EPred` reading,
which covers `m = ProbComp` for coin-flip-only protocols and `m = OracleComp superSpec` for
protocols with a shared random oracle or CRS, under any reading of `OracleComp` such as the
necessary reading of `VCVio.ProgramLogic.Unary.WP.Necessary`.
-/

public section

open Std.WP
open scoped Lean.Order

namespace Interaction

namespace Concurrent

section StepOver

variable {m : Type → Type} [Monad m]
variable {Γ : Interaction.TypeTree.Node.Context.{0, 0}} {P : Type}

/-- One step samples a path through the step's tree and applies the continuation to it. -/
@[simp]
theorem StepOver.sample_eq [LawfulMonad m] (step : StepOver Γ P)
    (sampler : TypeTree.Sampler m step.tree) : step.sample sampler =
      (do let tr ← TypeTree.samplePath step.tree sampler
          return step.next tr) := by
  rw [StepOver.sample, map_eq_pure_bind]

end StepOver

section ProcessOver

variable {m : Type → Type} [Monad m]
variable {Γ : Interaction.TypeTree.Node.Context.{0, 0}}

/-- Running no steps returns the initial state. -/
@[simp]
theorem ProcessOver.runSteps_zero {P : Type} (process : ProcessOver P Γ)
    (sampler : ∀ p : process.Proc, TypeTree.Sampler m (process.step p).tree)
    (s : process.Proc) :
    process.runSteps sampler 0 s = pure s := rfl

/-- Running `n + 1` steps samples one step and runs `n` more from the resulting state. -/
@[simp]
theorem ProcessOver.runSteps_succ {P : Type} (process : ProcessOver P Γ)
    (sampler : ∀ p : process.Proc, TypeTree.Sampler m (process.step p).tree) (n : ℕ)
    (s : process.Proc) :
    process.runSteps sampler (n + 1) s =
      (do let s' ← (process.step s).sample (sampler s)
          process.runSteps sampler n s') := rfl

end ProcessOver

end Concurrent

/-! ## Invariant preservation for `runSteps` -/

namespace Concurrent.ProcessOver

variable {m : Type → Type} [Monad m] {Pred : Type} {EPred : Type} [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred]
variable {Γ : Interaction.TypeTree.Node.Context.{0, 0}}

/-- A per-step triple that preserves an invariant `I` on the process state lifts to `runSteps`
at every fuel, by induction on the fuel. This is the process-runtime analogue of
`OracleComp.ProgramLogic.simulateQ_triple_preserves_invariant`. -/
theorem runSteps_triple_preserves_invariant {P : Type} (process : ProcessOver P Γ)
    (sampler : ∀ p : process.Proc, TypeTree.Sampler m (process.step p).tree)
    (I : process.Proc → Prop) {epost : EPred}
    (hstep : ∀ p : process.Proc,
      Triple ((process.step p).sample (sampler p)) ⌜I p⌝ (fun p' => ⌜I p'⌝) epost)
    (n : ℕ) (s₀ : process.Proc) :
    Triple (process.runSteps sampler n s₀) ⌜I s₀⌝ (fun s' => ⌜I s'⌝) epost := by
  induction n generalizing s₀ with
  | zero =>
    rw [runSteps_zero]
    exact Triple.pure s₀ Lean.Order.PartialOrder.rel_refl
  | succ n ih =>
    rw [runSteps_succ]
    exact Triple.bind _ _ _ (hstep s₀) fun _ => ih _

end Concurrent.ProcessOver

/-! ## Smoke test: increment process

An always-increment process over `Proc := ℕ`: every step advances the counter by one without
consuming any moves. The per-step triple keeps the counter above a threshold, and
`runSteps_triple_preserves_invariant` extends it to the whole execution under the necessary
reading of `ProbComp`. -/

namespace Concurrent.ProcessOver.Example

/-- Compile-time smoke test that locally constructs an always-increment process
and derives that `runSteps` never decreases its counter. -/
private example (p₀ s₀ n : ℕ) : True := by
  let process : ProcessOver ℕ (fun _ => PUnit) :=
    ProcessOver.ofStep ℕ fun p =>
      { tree := .done
        semantics := PUnit.unit
        next := fun _ => p + 1 }
  let sampler : ∀ p : process.Proc,
      Interaction.TypeTree.Sampler ProbComp (process.step p).tree :=
    fun _ => PUnit.unit
  have stepTriple (p : ℕ) :
      Triple ((process.step p).sample (sampler p) : ProbComp ℕ)
        ⌜p₀ ≤ p⌝ (fun p' => ⌜p₀ ≤ p'⌝) estack⟨⟩ := by
    have hsample :
        ((process.step p).sample (sampler p) : ProbComp ℕ) = pure (p + 1) := by
      rw [StepOver.sample_eq]
      simp [process, sampler]
    rw [hsample]
    exact Triple.pure (p + 1)
      (Lean.Order.CompleteLattice.ofProp_imp _ _ fun h => Nat.le_succ_of_le h)
  have _h :
      Triple (process.runSteps sampler n s₀ : ProbComp ℕ)
        ⌜p₀ ≤ s₀⌝ (fun p' => ⌜p₀ ≤ p'⌝) estack⟨⟩ :=
    runSteps_triple_preserves_invariant process sampler (fun s => p₀ ≤ s) stepTriple n s₀
  trivial

end Concurrent.ProcessOver.Example

end Interaction
