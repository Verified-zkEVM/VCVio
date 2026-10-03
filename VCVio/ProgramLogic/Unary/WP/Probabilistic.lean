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
assertions. `open scoped OracleComp.Probabilistic` selects it.

Its value is the expectation of the postcondition's values in `ℝ≥0∞`, by `wp_val_eq_wp`.
-/

@[expose] public section

universe u

open ENNReal Std.WP

/-! ## Restricted expectation algebra -/

namespace OracleComp.Probabilistic

variable {ι : Type u} {spec : OracleSpec ι} {α : Type}
  [OracleSpec.AnswerMeasure spec]

/-- Oracle expectation preserves the probability bound. -/
theorem wp_one_le (oa : OracleComp spec α) :
    MAlgOrdered.μ (oa >>= fun _ => pure (1 : ℝ≥0∞)) ≤ 1 :=
  (ExpectationWP.wp_const_of_oracle oa 1).le

/-- The expectation algebra restricted to probability-valued assertions. -/
noncomputable scoped instance (priority := 1100) instMAlgOrdered :
    MAlgOrdered (OracleComp spec) Prob :=
  ExpectationWP.Probabilistic.algebra (OracleComp spec)

/-- Core weakest preconditions for probability-valued assertions. -/
noncomputable scoped instance (priority := 1100) instWP_prob :
    Std.WP.WPMonad (OracleComp spec) Prob EStack⟨⟩ :=
  MAlgOrdered.toWPMonad

/-- The probability-bounded reading as a direct `WP` instance on programs, at the scope's
priority, so that no direct instance of another scope outranks it while this one is open. -/
noncomputable scoped instance (priority := 1100) wpInst :
    Std.WP.WP (OracleComp spec α) α Prob EStack⟨⟩ :=
  (instWP_prob (spec := spec)).toWP α

/-- Forgetting the bound recovers the expectation in `ℝ≥0∞`. -/
theorem wp_val_eq_wp (oa : OracleComp spec α) (post : α → Prob) (epost : EStack⟨⟩) :
    (Std.WP.wp oa post epost).val =
      wp⟦oa⟧ (fun a => (post a).val) :=
  ExpectationWP.Probabilistic.wp_val oa post epost

end OracleComp.Probabilistic
