/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.NotationCore
public import VCVio.ProgramLogic.Relational.Quantitative

/-!
# Ergonomic Notation and Convenience Layer for Program Logic

This file extends `VCVio.ProgramLogic.NotationCore` with the heavier quantitative
bridge lemmas that depend on the full eRHL development.
-/

@[expose] public section

open ENNReal OracleSpec OracleComp

universe u

namespace OracleComp.ProgramLogic

variable {ι₁ : Type u}
variable {spec₁ : OracleSpec.{u, 0} ι₁} [∀ t, MeasurableSpace (spec₁.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec₁.Range t)] [IsMeasureSpec spec₁]
  [∀ t, Finite (spec₁.Range t)]
variable {α : Type}

/-- Game equivalence from zero-error approximate coupling. -/
theorem GameEquiv.of_approxRelTriple_zero
    {g₁ g₂ : OracleComp spec₁ α}
    (h : Relational.ApproxRelTriple (spec₁ := spec₁) (spec₂ := spec₁) 0 g₁ g₂
      (Relational.EqRel α)) :
    GameEquiv g₁ g₂ :=
  Relational.evalDist_eq_of_approxRelTriple_zero h

end OracleComp.ProgramLogic
