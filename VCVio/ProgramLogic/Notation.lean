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
variable {spec₁ : OracleSpec ι₁}
variable [IsUniformSpec spec₁]
variable {α : Type}

/-- Game equivalence from zero-error approximate coupling. -/
theorem GameEquiv.of_approxRelTriple_zero
    {g₁ g₂ : OracleComp spec₁ α}
    (h : Relational.ApproxRelTriple (spec₁ := spec₁) (spec₂ := spec₁) 0 g₁ g₂
      (Relational.EqRel α)) :
    GameEquiv g₁ g₂ := by
  unfold Relational.ApproxRelTriple at h
  rw [tsub_zero] at h
  have htv : tvDist g₁ g₂ = 0 := by
    rw [Relational.tvDist_eq_one_sub_eRelWP_eqRel, tsub_eq_zero_of_le h, ENNReal.toReal_zero]
  exact (tvDist_eq_zero_iff g₁ g₂).1 htv

end OracleComp.ProgramLogic
