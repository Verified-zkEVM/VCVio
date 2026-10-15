/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio

/-!
# Unary VC-generator names

Core Lean ships a tactic spelled `vcgen` (`Std.Tactic.Do`), which the root `VCVio` import brings
into scope through the core-triple handler specifications. VCVio's unary tactics are spelled
`prvcgen`, which runs core's `vcgen` under the reading of an oracle computation a goal belongs to,
and `prrw`, which rewrites equalities between two programs' probabilities, so neither shares a
leading token with core's. This file pins that state:

* each spelling parses to a single syntax kind, with no `choice` node: `vcgen` to core's, and
  `prvcgen` and `prrw` to VCVio's;
* `prvcgen` closes quantitative core triples over oracle computations, including `StateT` state
  operations and lifted oracle computations;
* a bare `vcgen` elaborates core's tactic on `Prop`-valued triples under the necessary reading
  `OracleComp.Necessary`, with VCVio's tactics imported.
-/

public section

open ENNReal OracleSpec OracleComp
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic Std.WP

run_cmd do
  for (src, kind) in [("vcgen", ``Lean.Parser.Tactic.vcgen),
      ("prvcgen", ``prvcgenStx),
      ("prrw", ``OracleComp.ProgramLogic.prrw),
      ("prrw move 0 2", ``OracleComp.ProgramLogic.prrwMove)] do
    let .ok stx := Lean.Parser.runParserCategory (← Lean.getEnv) `tactic src
      | throwError "`{src}` does not parse as a tactic"
    unless stx.getKind == kind do
      throwError "`{src}` parses as `{stx.getKind}`, expected `{kind}`"

namespace VCVioTest.ProgramLogic.VCGenNames

universe u

variable {ι : Type u} {spec : OracleSpec ι} {α : Type}

/-! ## `prvcgen` -/

section Probabilistic

variable [OracleSpec.AnswerMeasure spec]

open scoped OracleComp.Lower

example (oa : OracleComp spec α) (post : Nat × α → Nat → ℝ≥0∞) :
    ⦃fun s => wp⟦oa⟧ (fun a => post (s, a) (s + 1))⦄
      (do
        let s ← (MonadStateOf.get : StateT Nat (OracleComp spec) Nat)
        MonadStateOf.set (s + 1)
        let a ← (MonadLift.monadLift oa : StateT Nat (OracleComp spec) α)
        pure (s, a))
    ⦃post⦄ := by
  prvcgen (errorOnMissingSpec := false)
  simp only [Std.WP.StateT.wp_apply_eq, StateT.run_pure, ExactWPMonad.wp_pure, le_refl]

example (s' : Nat) (oa : OracleComp spec α) (post : α → Nat → ℝ≥0∞) :
    ⦃fun _ => wp⟦oa⟧ (fun a => post a s')⦄
      (do
        MonadStateOf.set s'
        MonadLift.monadLift oa : StateT Nat (OracleComp spec) α)
    ⦃post⦄ := by
  prvcgen (errorOnMissingSpec := false)

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    ⦃wp⟦oa⟧ post⦄ oa ⦃post⦄ := by
  prvcgen (errorOnMissingSpec := false)

end Probabilistic

/-! ## Core `vcgen` -/

section Core

example : ⦃ True ⦄ (pure 3 : OracleComp spec Nat) ⦃ fun n => n = 3 ⦄ := by
  vcgen

example (t : spec.Domain) :
    ⦃ fun s : Nat => s = 3 ⦄
      (do
        let s ← (get : StateT Nat (OracleComp spec) Nat)
        let _ ← (liftM (HasQuery.query t : OracleComp spec (spec.Range t)) :
          StateT Nat (OracleComp spec) (spec.Range t))
        set (s + 1)
        pure s)
    ⦃ fun r s => r = 3 ∧ s = 4 ⦄ := by
  vcgen
  grind

end Core

end VCVioTest.ProgramLogic.VCGenNames
