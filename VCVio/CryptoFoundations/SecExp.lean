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

This file defines simple security experiments that succeed unless they terminate with failure.
Each experiment carries bundled subprobabilistic semantics, so the experiment can be interpreted
through an internal semantic monad and observed directly as a successful-output measure.

We also define `BoundedAdversary α β` as an oracle computation bundled with a query bound.
-/

@[expose] public section

universe u v w

open MeasureTheory OracleComp OracleSpec ENNReal Polynomial Prod

/-- Bias advantage of a Boolean-valued subdistribution: the gap between the probabilities of
returning `true` and `false`.

This compatibility definition immediately forgets the discrete representation in favor of its
successful-output measure. Any remaining mass corresponds to failure and therefore contributes to
neither Boolean branch. -/
noncomputable def SPMF.boolBiasAdvantage (p : SPMF Bool) : ℝ :=
  p.toMeasure.boolBias

/-- Distinguishing advantage between two Boolean-valued subdistributions, measured after mapping
both values to successful-output measures. -/
noncomputable def SPMF.boolDistAdvantage (p q : SPMF Bool) : ℝ :=
  p.toMeasure.boolDist q.toMeasure

/-- Re-express Boolean bias as twice the absolute deviation of the `true` mass from one half when
the subdistribution has full mass. -/
lemma SPMF.boolBiasAdvantage_eq_two_mul_abs_sub_half (p : SPMF Bool)
    (htotal : p.toMeasure {true} + p.toMeasure {false} = 1) :
    p.boolBiasAdvantage = 2 * |(p.toMeasure {true}).toReal - 1 / 2| :=
  Measure.boolBias_eq_two_mul_abs_sub_half p.toMeasure htotal

/-- Hidden-bit decomposition at the SPMF level: the bias of a coin-flip guessing game equals the
distinguishing advantage between the two branches, assuming the coin is fair and both branches
have full mass (no failure).

The totality hypotheses are required because failure mass breaks the identity between the `false`
mass and the complement of the `true` mass. The proof is inherited from the measure API. -/
lemma SPMF.boolBiasAdvantage_eq_boolDistAdvantage_coin_branch
    (coin p q : SPMF Bool)
    (hcoin_true : coin.toMeasure {true} = 1 / 2)
    (hcoin_false : coin.toMeasure {false} = 1 / 2)
    (hp : p.toMeasure {true} + p.toMeasure {false} = 1)
    (hq : q.toMeasure {true} + q.toMeasure {false} = 1) :
    (coin >>= fun b =>
      (if b then p else q) >>= fun z => pure (b == z)).boolBiasAdvantage =
    p.boolDistAdvantage q := by
  have hbranch (b : Bool) :
      (((if b then p else q) >>= fun z => pure (b == z)) : SPMF Bool).toMeasure =
        (if b then p.toMeasure else q.toMeasure).bind fun z => Measure.dirac (b == z) := by
    rw [SPMF.toMeasure_bind' _ (f := fun z => pure (b == z)) Measurable.of_discrete]
    cases b <;> simp [SPMF.toMeasure_pure]
  unfold SPMF.boolBiasAdvantage SPMF.boolDistAdvantage
  rw [SPMF.toMeasure_bind' coin (f := fun b =>
    (if b then p else q) >>= fun z => pure (b == z)) Measurable.of_discrete]
  simp_rw [hbranch]
  exact Measure.boolBias_bind_coin coin.toMeasure p.toMeasure q.toMeasure
    hcoin_true hcoin_false hp hq

/-- Triangle inequality for SPMF Boolean distinguishing advantage. -/
lemma SPMF.boolDistAdvantage_triangle (p q r : SPMF Bool) :
    p.boolDistAdvantage r ≤ p.boolDistAdvantage q + q.boolDistAdvantage r :=
  Measure.boolDist_triangle _ _ _

/-- Compatibility form of `evalDist_apply_true_le_add_ofReal_boolDistAdvantage`. -/
@[deprecated evalDist_apply_true_le_add_ofReal_boolDistAdvantage (since := "2026-09-15")]
lemma ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage (p q : ProbComp Bool) :
    Pr[= true | p] ≤ Pr[= true | q] + ENNReal.ofReal (p.boolDistAdvantage q) := by
  simpa only [← evalDist_apply_singleton] using
    ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage p q

/-- Compatibility form of `guessAdvantage_eq_abs_half_sub_defect`. -/
@[deprecated guessAdvantage_eq_abs_half_sub_defect (since := "2026-09-15")]
lemma ProbComp.guessAdvantage_eq_half_sub_probFailure (p : ProbComp Unit) :
    p.guessAdvantage = |1 / 2 - (Pr[⊥ | p]).toReal| := by
  rw [ProbComp.guessAdvantage_eq_abs_half_sub_defect,
    probFailure_eq_one_sub_evalDist_univ]
  rfl

/-- Compatibility form of `guessAdvantage_eq_half_mul_abs_defect_sub_apply`. -/
@[deprecated guessAdvantage_eq_half_mul_abs_defect_sub_apply (since := "2026-09-15")]
lemma ProbComp.guessAdvantage_eq_half_of_sub (p : ProbComp Unit) :
    p.guessAdvantage = 2⁻¹ * |(Pr[⊥ | p]).toReal - (Pr[= () | p]).toReal| := by
  simpa only [Measure.defect, probFailure_eq_one_sub_evalDist_univ,
    ← evalDist_apply_singleton] using
    ProbComp.guessAdvantage_eq_half_mul_abs_defect_sub_apply p

/-- Compatibility form of `distAdvantage_eq_abs_sub_defect`. -/
@[deprecated distAdvantage_eq_abs_sub_defect (since := "2026-09-15")]
lemma ProbComp.distAdvantage_eq_abs_sub_probFailure (p q : ProbComp Unit) :
    p.distAdvantage q = |(Pr[⊥ | p]).toReal - (Pr[⊥ | q]).toReal| := by
  simpa only [Measure.defect, probFailure_eq_one_sub_evalDist_univ] using
    ProbComp.distAdvantage_eq_abs_sub_defect p q

/-- Compatibility form of `distAdvantage_eq_measureTVDist`. -/
@[deprecated distAdvantage_eq_measureTVDist (since := "2026-09-15")]
lemma ProbComp.distAdvantage_eq_tvDist (p q : ProbComp Unit) :
    p.distAdvantage q = tvDist p q := by
  simp only [ProbComp.distAdvantage, evalDist_apply_singleton]
  simp only [tvDist, SPMF.tvDist, PMF.tvDist_option_punit]
  simp only [probOutput_def, SPMF.apply_eq_toPMF_some]

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
