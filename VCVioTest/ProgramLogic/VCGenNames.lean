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
into scope through the core-triple handler specifications. VCVio's unary probabilistic tactics are
spelled `pvcgen` and `pvcstep`, so the two families never share a leading token. This file pins
that state:

* each spelling parses to a single syntax kind, with no `choice` node: `vcgen` to core's, and
  `pvcgen`, `pvcgen?` and `pvcstep` to VCVio's;
* `pvcgen` and `pvcstep` close quantitative core triples over oracle computations, including
  `StateT` state operations and lifted oracle computations;
* a bare `vcgen` elaborates core's tactic on `Prop`-valued triples under the structural reading
  `OracleComp.Qualitative`, with VCVio's tactics imported.
-/

public section

open ENNReal OracleSpec OracleComp
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic Std.WP

run_cmd do
  for (src, kind) in [("vcgen", ``Lean.Parser.Tactic.vcgen),
      ("pvcgen", ``OracleComp.ProgramLogic.pvcgenBasic),
      ("pvcgen?", ``OracleComp.ProgramLogic.pvcgenSuggestion),
      ("pvcstep", ``OracleComp.ProgramLogic.tacticPvcstepUsing_)] do
    let .ok stx := Lean.Parser.runParserCategory (← Lean.getEnv) `tactic src
      | throwError "`{src}` does not parse as a tactic"
    unless stx.getKind == kind do
      throwError "`{src}` parses as `{stx.getKind}`, expected `{kind}`"

namespace VCVioTest.ProgramLogic.VCGenNames

universe u

variable {ι : Type u} {spec : OracleSpec ι} {α : Type}

/-! ## VCVio's probabilistic tactics -/

section Probabilistic

variable [OracleSpec.IsMeasureSpec spec]

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
  pvcgen

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    ⦃wp⟦oa⟧ post⦄ oa ⦃post⦄ := by
  pvcstep

end Probabilistic

/-! ## Core `vcgen` -/

section Core

open scoped OracleComp.Qualitative

set_option experimental.vcgen true

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
