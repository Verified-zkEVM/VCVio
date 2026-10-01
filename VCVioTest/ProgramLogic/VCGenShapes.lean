/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# Program shapes read by `prvcgen`

Spellings of an oracle program that differ from a `do` block typed at `OracleComp spec` while
unfolding to one, each read by `prvcgen` without preparation: a fragment typed at the free
monad `PFunctor.FreeM (OracleSpec.toPFunctor spec)` underneath `OracleComp`, a draw ascribed
that type inside a block typed at `OracleComp`, and a bind spelled with the free monad's own
instance. Downstream libraries assemble their programs from fragments typed this way, so the
tests pin that the readings see through the spellings; `OracleComp` and `toPFunctor` are
reducible, which is what makes the free monad's instances the oracle computation's.
-/

public section

open OracleSpec OracleComp Std.WP ENNReal

namespace VCVioTest.ProgramLogic.VCGenShapes

/-- A fragment typed at the free monad underneath `OracleComp`. -/
def fragment : PFunctor.FreeM (OracleSpec.toPFunctor unifSpec) Bool := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let c ← ($ᵗ Bool : ProbComp Bool)
  pure (b && c)

/-- The fragment's binds are read under the necessary reading. -/
example : Pr{let x ← (fragment : ProbComp Bool)}[x = true ∨ x = false] = 1 := by
  prvcgen [fragment]
  exact Bool.eq_false_or_eq_true _

/-- The fragment's binds are read under the upper-bound reading, with the averaging rule. -/
example : Pr{let x ← (fragment : ProbComp Bool)}[x = true] ≤ 1 / 2 := by
  prvcgen [fragment, OracleComp.Upper.Spec.uniformSample_avg]
  simp only [upper_readback, Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton, Fintype.card_bool,
    Nat.cast_ofNat]
  calc _ ≤ ((1 : ℝ≥0∞) + 0) / 2 := by
        gcongr
        · exact prEvent_le_one _
        · prvcgen
          simp
    _ = 1 / 2 := by rw [add_zero]

/-- A draw ascribed the free monad's type inside a block typed at `OracleComp`. -/
def ascribedDraw : ProbComp Bool := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let c ← ($ᵗ Bool : PFunctor.FreeM (OracleSpec.toPFunctor unifSpec) Bool)
  pure (b && c)

example : Pr{let x ← ascribedDraw}[x = true ∨ x = false] = 1 := by
  prvcgen [ascribedDraw]
  exact Bool.eq_false_or_eq_true _

/-- A bind spelled with the free monad's own instance. -/
def freeBind : ProbComp Bool :=
  @Bind.bind (PFunctor.FreeM (OracleSpec.toPFunctor unifSpec)) _ _ _ ($ᵗ Bool : ProbComp Bool)
    (fun b => pure b)

example : Pr{let x ← freeBind}[x = true ∨ x = false] = 1 := by
  prvcgen [freeBind]
  exact Bool.eq_false_or_eq_true _

end VCVioTest.ProgramLogic.VCGenShapes
