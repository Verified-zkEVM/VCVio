/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio

/-!
# `vcgen` and `pvcgen` name canary

Core Lean ships a tactic spelled `vcgen` (`Std.Tactic.Do`), and VCVio's program logic ships its
exhaustive driver as `pvcgen` (`VCVio.ProgramLogic.Tactics.Unary`). Both are in scope in any file
that imports the root `VCVio` module. This file pins that a bare `vcgen` is core's tactic: it
parses to core's syntax kind alone, without a `choice` node, it reports core's error on a
probability goal that only `pvcgen` lowers, and it steps a `StateT` program with core's `@[spec]`
rules. `pvcgen` closes the probability goal and a transformer
program whose precondition is the expectation of an opaque oracle computation.
-/

public section

open ENNReal OracleSpec OracleComp
open Lean.Order
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic Std.WP OracleComp.Lower

namespace VCVioTest.VCGenAmbiguity

universe u

/-- info: [Lean.Parser.Tactic.vcgen, OracleComp.ProgramLogic.tacticPvcgen] -/
#guard_msgs in
open Lean in
run_cmd do
  let kinds ← ["vcgen", "pvcgen"].mapM fun src => do
    let .ok stx := Parser.runParserCategory (← getEnv) `tactic src
      | throwError "`{src}` does not parse as a tactic"
    pure stx.getKind
  logInfo m!"{kinds}"

/-- error: vcgen: could not determine the program type of the goal -/
#guard_msgs in
example : Pr{let b ← $ᵗ Bool}[(b || true) = true] = 1 := by
  vcgen

example : Pr{let b ← $ᵗ Bool}[(b || true) = true] = 1 := by
  pvcgen

variable {ι : Type u} {spec : OracleSpec ι} {α : Type}
  [OracleSpec.AnswerMeasure spec]

example (oa : OracleComp spec α) (post : Nat × α → Nat → ℝ≥0∞) :
    ⦃fun s => wp⟦oa⟧ (fun a => post (s, a) (s + 1))⦄
      (do
        let s ← (MonadStateOf.get : StateT Nat (OracleComp spec) Nat)
        MonadStateOf.set (s + 1)
        let a ← (MonadLift.monadLift oa : StateT Nat (OracleComp spec) α)
        pure (s, a))
    ⦃post⦄ := by
  pvcgen

example (s' : Nat) (oa : OracleComp spec α) (post : α → Nat → ℝ≥0∞) :
    ⦃fun _ => wp⟦oa⟧ (fun a => post a s')⦄
      (do
        MonadStateOf.set s'
        MonadLift.monadLift oa : StateT Nat (OracleComp spec) α)
    ⦃post⦄ := by
  vcgen

end VCVioTest.VCGenAmbiguity
