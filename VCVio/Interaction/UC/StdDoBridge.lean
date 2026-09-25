/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Std.Tactic.Do
public import PolyFun.Interaction.Basic.Sampler
public import VCVio.Interaction.UC.Runtime
public import VCVio.ProgramLogic.Unary.StdDoBridge

/-!
# `Std.Do` / `mvcgen` bridge for the Interaction / UC runtime

Equip the runtime primitives in `VCVio.Interaction.UC.Runtime`
(`TypeTree.samplePath`, `Concurrent.StepOver.sample`,
`Concurrent.ProcessOver.runSteps`) with the equational and Hoare-triple
machinery `mvcgen` needs, so users can prove triples about UC executions
in the same style as `VCVio.ProgramLogic.Unary.HandlerSpecs`.

## Architecture

The runtime primitives are defined by structural recursion over the
`Interaction.TypeTree` (for path sampling) or over fuel `ℕ` (for
`runSteps`). Neither recursion is walked by `mvcgen`, so we expose the
recursive equations as `@[simp]` lemmas and provide a closed-form
`runSteps_triple_preserves_invariant` for the most common
"fuel-indexed invariant" pattern.

The bridge is intentionally monad-parametric: every result is phrased
for an arbitrary `[Monad m] [WPMonad m ps]`. This covers both
`m = ProbComp` (coin-flip-only protocols) and
`m = OracleComp superSpec` (shared random oracle / CRS protocols),
since both carry `Std.Do.WPMonad` instances via
`VCVio.ProgramLogic.Unary.StdDoBridge`.

## Main results

* `TypeTree.samplePath_done`, `TypeTree.samplePath_node` — rfl-level
  unfolding of `TypeTree.samplePath` for base and step cases.
* `Concurrent.StepOver.sample_eq` — unfolds `StepOver.sample` in terms
  of `samplePath`.
* `Concurrent.ProcessOver.runSteps_zero`,
  `Concurrent.ProcessOver.runSteps_succ` — base and step unfolding of
  `runSteps` on fuel.
* `Concurrent.ProcessOver.runSteps_triple_preserves_invariant` — lifts
  a per-step invariant triple to a whole-`runSteps` triple, by
  induction on fuel.

These equations are tagged `@[simp]` so that `mvcgen` can walk an
exposed `samplePath` / `sample` / `runSteps` body in one simp pass
before the usual `do`-block traversal. The bind-shaped definitions hold
by `rfl`; `Concurrent.StepOver.sample_eq` rephrases the map-shaped
`StepOver.sample` and needs `[LawfulMonad m]`.
-/

@[expose] public section

open Std.Do OracleComp

namespace Interaction

namespace Concurrent

section StepOver

variable {m : Type → Type} [Monad m]
variable {Γ : Interaction.TypeTree.Node.Context.{0, 0}} {P : Type}

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

@[simp]
theorem ProcessOver.runSteps_zero {P : Type} (process : ProcessOver P Γ)
    (sampler : ∀ p : process.Proc, TypeTree.Sampler m (process.step p).tree)
    (s : process.Proc) :
    process.runSteps sampler 0 s = pure s := rfl

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

namespace Concurrent
namespace ProcessOver

variable {m : Type → Type} [Monad m]
variable {ps : PostShape} [WPMonad m ps]
variable {Γ : Interaction.TypeTree.Node.Context.{0, 0}}

/-- If every one-step execution preserves an invariant `I` on the
process state, then `runSteps n` preserves `I` for any fuel `n`.

This is the process-runtime analogue of
`OracleComp.ProgramLogic.StdDo.simulateQ_triple_preserves_invariant`:
a generic invariant lemma that factors out the fuel induction so
downstream proofs stay inside the `Std.Do` world. -/
theorem runSteps_triple_preserves_invariant {P : Type} (process : ProcessOver P Γ)
    (sampler : ∀ p : process.Proc, TypeTree.Sampler m (process.step p).tree)
    (I : process.Proc → Prop) (hstep : ∀ p : process.Proc,
      Std.Do.Triple ((process.step p).sample (sampler p))
        (spred(⌜I p⌝))
        (⇓ p' => ⌜I p'⌝))
    (n : ℕ) (s₀ : process.Proc) :
    Std.Do.Triple
      (process.runSteps sampler n s₀)
      (spred(⌜I s₀⌝))
      (⇓ s' => ⌜I s'⌝) := by
  induction n generalizing s₀ with
  | zero =>
    simp only [runSteps_zero]
    exact Triple.pure s₀ .rfl
  | succ n ih =>
    simp only [runSteps_succ]
    exact Triple.bind _ _ (hstep s₀) ih

end ProcessOver
end Concurrent

end Interaction

/-! ## Smoke test: increment process

A minimal worked example demonstrating the bridge: an always-increment
process over `Proc := ℕ` whose every step advances the counter by one
without consuming any moves. The counter is trivially monotone and the
whole-execution corollary follows directly from
`runSteps_triple_preserves_invariant`. -/

namespace Interaction.Concurrent.ProcessOver

namespace Example

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
      Std.Do.Triple
        ((process.step p).sample (sampler p) : ProbComp _)
        (spred(⌜p₀ ≤ p⌝))
        (⇓ p' => ⌜p₀ ≤ p'⌝) := by
    have hsample :
        ((process.step p).sample (sampler p) : ProbComp ℕ) = pure (p + 1) := by
      rw [StepOver.sample_eq]
      simp [process, sampler]
    rw [hsample]
    refine Std.Do.Triple.pure (m := ProbComp) (p + 1) ?_
    simp only [SPred.entails_nil, SPred.down_pure]
    omega
  have _h :
      Std.Do.Triple
        (process.runSteps sampler n s₀ : ProbComp ℕ)
        (spred(⌜p₀ ≤ s₀⌝))
        (⇓ p' => ⌜p₀ ≤ p'⌝) :=
    runSteps_triple_preserves_invariant (m := ProbComp)
      process sampler (fun s => p₀ ≤ s) stepTriple n s₀
  trivial

end Example

end Interaction.Concurrent.ProcessOver
