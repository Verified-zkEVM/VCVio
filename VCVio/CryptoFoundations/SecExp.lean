/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.SecExp.Measure
public import ToMathlib.MeasureTheory.Measure.Bool
public import VCVio.EvalDist.Defs.Instances
public import VCVio.EvalDist.Defs.Semantics.Core
public import VCVio.EvalDist.FailureMeasure
public import VCVio.EvalDist.MeasureTVDist
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.EvalDist.UniformCompatibility
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Security Experiments

This file defines `BoundedAdversary α β`, an oracle computation bundled with a query bound, and
re-exports the Boolean advantages of `VCVio.CryptoFoundations.SecExp.Measure`.
-/

@[expose] public section

universe u v w

open MeasureTheory OracleComp OracleSpec ENNReal Polynomial Prod

/-- Compatibility form of `evalDist_apply_true_le_add_ofReal_boolDistAdvantage`. -/
@[deprecated evalDist_apply_true_le_add_ofReal_boolDistAdvantage (since := "2026-09-15")]
lemma ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage (p q : ProbComp Bool) :
    Pr[= true | p] ≤ Pr[= true | q] + ENNReal.ofReal (p.boolDistAdvantage q) := by
  simpa only [← evalDist_apply_singleton] using
    ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage p q

/-- A security adversary bundling a computation with a bound on the number of queries it makes,
where the bound must be shown to satisfy `IsQueryBound`.
We also require an explicit list of all oracles used in the computation,
which is necessary in order to make certain reductions computable. -/
structure BoundedAdversary {ι : Type u} [DecidableEq ι]
    (spec : OracleSpec ι) (α β : Type u) where
  run : α → OracleComp spec β
  qb : ι → ℕ
  qb_isQueryBound (x : α) : IsPerIndexQueryBound (run x) (qb)
  activeOracles : List ι
  mem_activeOracles_iff (i : ι) : i ∈ activeOracles ↔ qb i ≠ 0

namespace BoundedAdversary

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}

end BoundedAdversary
