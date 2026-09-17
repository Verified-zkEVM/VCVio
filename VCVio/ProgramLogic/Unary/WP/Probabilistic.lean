/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Control.Monad.Algebra.WP
public import PolyFun.Control.Monad.Algebra.Restrict
public import VCVio.ProgramLogic.Unary.HoareTriple
public import VCVio.ProgramLogic.Prob
public import VCVio.ProgramLogic.Unary.WP.Probabilistic.Measure

/-!
# Probability-bounded weakest preconditions

`Prob` is Mathlib's lower interval `Set.Iic (1 : ℝ≥0∞)`. Restricting the expectation
algebra to this interval gives a core `WPMonad` interpretation with probability-valued
assertions. Enable it with `open scoped OracleComp.Probabilistic`.

The underlying value agrees with the quantitative expectation by `wp_val_eq_mAlgOrdered_wp`.
-/

@[expose] public section

universe u

open ENNReal Std.Internal.Do

/-! ## Restricted expectation algebra -/

namespace OracleComp.Probabilistic

variable {ι : Type u} {spec : OracleSpec ι} [IsUniformSpec spec] {α : Type}

/-- Oracle expectation preserves the probability bound. -/
theorem wp_one_le (oa : OracleComp spec α) :
    MAlgOrdered.wp oa (fun _ => (1 : ℝ≥0∞)) ≤ 1 :=
  (OracleComp.ProgramLogic.wp_const oa 1).le

/-- The expectation algebra restricted to probability-valued assertions. -/
noncomputable scoped instance instMAlgOrdered : MAlgOrdered (OracleComp spec) Prob := by
  let : ∀ t, MeasurableSpace (spec.Range t) := fun _ ↦ _root_.Top.top
  exact MeasureProgramLogic.Probabilistic.toMAlgOrdered (OracleComp spec)

/-- Core weakest preconditions for probability-valued assertions. -/
noncomputable scoped instance instWP_prob :
    Std.Internal.Do.WPMonad (OracleComp spec) Prob Std.Internal.Do.EPost.Nil :=
  MAlgOrdered.toWPMonad

/-- Forgetting the bound recovers quantitative expectation. -/
theorem wp_val_eq_mAlgOrdered_wp (oa : OracleComp spec α) (post : α → Prob) :
    (Std.Internal.Do.wp oa post Lean.Order.bot).val =
      MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa (fun a => (post a).val) := by
  let : ∀ t, MeasurableSpace (spec.Range t) := fun _ ↦ _root_.Top.top
  exact MeasureProgramLogic.Probabilistic.wp_val_eq_mAlgOrdered_wp oa post

end OracleComp.Probabilistic
