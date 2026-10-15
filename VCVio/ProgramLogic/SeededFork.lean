/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.SeededFork
public import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Seed-Based Forking Lemma — Program Logic Bridge

Wraps the probabilistic seeded forking lemma bounds from
`CryptoFoundations/SeededFork.lean` as quantitative Hoare triples (core's `Std.WP.Triple`) for use
in the program logic framework.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal
open scoped Std.WP
open scoped OracleComp.Lower

namespace OracleComp.ProgramLogic

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ i, SampleableType (spec.Range i)] [∀ i, DecidableEq (spec.Range i)] [unifSpec ⊂ₒ spec]
  {α : Type}

variable (main : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    [unifSpec ˡ⊂ₒ spec]
    [OracleSpec.UniformAnswerMeasure spec]

/-- Seeded forking lemma as a quantitative Hoare triple for the fork-success event. -/
theorem triple_seededFork [Fintype (spec.Range i)] :
    ⦃ let acc : ℝ≥0∞ := ∑ s, Pr{let x ← main}[cf x = some s]
      let h : ℝ≥0∞ := Fintype.card (spec.Range i)
      let q := qb i + 1
      acc * (acc / q - h⁻¹) ⦄
      seededFork main qb js i cf
      ⦃ fun r => if r.isSome then 1 else 0 ⦄ :=
  ⟨le_trans (OracleComp.le_prEvent_isSome_seededFork main qb js i cf)
    (triple_prEvent_indicator (seededFork main qb js i cf) fun r ↦ r.isSome).le_wp⟩

end OracleComp.ProgramLogic
