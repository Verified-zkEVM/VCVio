/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import ToMathlib.MeasureTheory.Measure.Bool
public import VCVio.EvalDist.Defs.Instances
public import VCVio.EvalDist.Defs.Semantics
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

/-- Bias advantage of a Boolean-valued game: the gap between the probabilities of the two outputs.

This is the canonical single-game formulation for hidden-bit guessing experiments. -/
noncomputable def ProbComp.boolBiasAdvantage (p : ProbComp Bool) : ℝ :=
  |(𝒟[p] {true}).toReal - (𝒟[p] {false}).toReal|

/-- Distinguishing advantage between two Boolean-valued games, measured on the `true` branch.

For Boolean outputs this is equivalent to measuring the gap on `false`; choosing `true` is just a
conventional presentation. -/
noncomputable def ProbComp.boolDistAdvantage (p q : ProbComp Bool) : ℝ :=
  |(𝒟[p] {true}).toReal - (𝒟[q] {true}).toReal|

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

/-- Triangle inequality for Boolean distinguishing advantage. -/
lemma ProbComp.boolDistAdvantage_triangle (p q r : ProbComp Bool) :
    p.boolDistAdvantage r ≤ p.boolDistAdvantage q + q.boolDistAdvantage r :=
  Measure.boolDist_triangle _ _ _

/-- A Boolean game has zero distinguishing advantage against itself. -/
@[simp, grind =]
lemma ProbComp.boolDistAdvantage_self (p : ProbComp Bool) : p.boolDistAdvantage p = 0 :=
  Measure.boolDist_self 𝒟[p]

/-- Boolean distinguishing advantage is symmetric. -/
lemma ProbComp.boolDistAdvantage_comm (p q : ProbComp Bool) :
    p.boolDistAdvantage q = q.boolDistAdvantage p :=
  Measure.boolDist_comm _ _

/-- The `true`-branch probability of one Boolean-valued game is bounded above by the
`true`-branch probability of another game plus their distinguishing advantage.

This is the `ENNReal`-level interpretation of the real-valued identity `a ≤ b + |a - b|`,
packaged for SSP game-hopping: converting an `advantage p q ≤ ε` assumption into a direct
probability inequality `Pr[true|p] ≤ Pr[true|q] + ENNReal.ofReal ε` that plugs into chained
`calc`-style bounds. -/
lemma ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage (p q : ProbComp Bool) :
    𝒟[p] {true} ≤ 𝒟[q] {true} + ENNReal.ofReal (p.boolDistAdvantage q) :=
  Measure.apply_true_le_add_ofReal_boolDist 𝒟[p] 𝒟[q]

/-- Compatibility form of `evalDist_apply_true_le_add_ofReal_boolDistAdvantage`. -/
@[deprecated evalDist_apply_true_le_add_ofReal_boolDistAdvantage (since := "2026-09-15")]
lemma ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage (p q : ProbComp Bool) :
    Pr[= true | p] ≤ Pr[= true | q] + ENNReal.ofReal (p.boolDistAdvantage q) := by
  simpa only [← evalDist_apply_singleton] using
    ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage p q

/-- Re-express Boolean bias as twice the absolute deviation of `Pr[true]` from `1/2`. -/
lemma ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half (p : ProbComp Bool) :
    p.boolBiasAdvantage = 2 * |(𝒟[p] {true}).toReal - 1 / 2| :=
  Measure.boolBias_eq_two_mul_abs_sub_half_of_isProbabilityMeasure 𝒟[p]

/-- A hidden-bit guessing game over two Boolean branches has bias exactly equal to the
distinguishing advantage between those two branches. -/
lemma ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch
    (real rand : ProbComp Bool) :
    (do
      let b ← ($ᵗ Bool)
      let z ← if b then real else rand
      pure (b == z)).boolBiasAdvantage =
    real.boolDistAdvantage rand := by
  rw [ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half,
    evalDist_apply_singleton, probOutput_uniformBool_branch_toReal_sub_half,
    ProbComp.boolDistAdvantage]
  simp only [evalDist_apply_singleton]
  rw [abs_div, abs_two, mul_div_cancel₀ _ two_ne_zero]

/-- Version of `boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch` with a shared sampled
prefix before the real/random branch is chosen. -/
lemma ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage
    {α : Type} (pref : ProbComp α) (real rand : α → ProbComp Bool) :
    (do
      let a ← pref
      let b ← ($ᵗ Bool)
      let z ← if b then real a else rand a
      pure (b == z)).boolBiasAdvantage =
    (do
      let a ← pref
      real a).boolDistAdvantage
      (do
        let a ← pref
        rand a) := by
  let game : ProbComp Bool := do
    let a ← pref
    let b ← ($ᵗ Bool)
    let z ← if b then real a else rand a
    pure (b == z)
  let left : ProbComp Bool := do
    let a ← pref
    real a
  let right : ProbComp Bool := do
    let a ← pref
    rand a
  let branchGame : ProbComp Bool := do
    let b ← ($ᵗ Bool)
    let z ← if b then left else right
    pure (b == z)
  have hbranch : 𝒟[game] = 𝒟[branchGame] := by
    let : MeasurableSpace α := ⊤
    calc
      𝒟[game] = 𝒟[($ᵗ Bool) >>= fun b => pref >>= fun a => do
          let z ← if b then real a else rand a
          pure (b == z)] := by
            simpa [game, monad_norm] using
              (evalDist_bind_bind_swap pref ($ᵗ Bool)
                (fun a b => do
                  let z ← if b then real a else rand a
                  pure (b == z))
                (measurable_from_prod_countable_left fun _ => .of_discrete))
      _ = 𝒟[branchGame] := by
        congr 1
        simp only [branchGame]
        apply bind_congr
        intro b
        cases b <;> simp [left, right]
  rw [show game.boolBiasAdvantage = branchGame.boolBiasAdvantage by
    unfold ProbComp.boolBiasAdvantage
    rw [hbranch]]
  simpa [branchGame, left, right] using
    ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch left right

/-- The **advantage** of a game `p`, assumed to be a probabilistic computation ending with a `guard`
  statement, is the absolute difference between the probability of success and 1/2. -/
noncomputable def ProbComp.guessAdvantage (p : ProbComp Unit) : ℝ :=
  |1 / 2 - (𝒟[p] {()}).toReal|

/-- The guess advantage of `p` is its distance from one half measured using the missing mass. -/
lemma ProbComp.guessAdvantage_eq_abs_half_sub_defect (p : ProbComp Unit) :
    p.guessAdvantage = |1 / 2 - (𝒟[p]).defect.toReal| := by
  have hunit : ({()} : Set Unit) = Set.univ := by
    ext x
    simp
  rw [ProbComp.guessAdvantage, Measure.defect_toReal, hunit]
  rw [show (1 : ℝ) / 2 - (1 - (𝒟[p] Set.univ).toReal) =
    -(1 / 2 - (𝒟[p] Set.univ).toReal) by ring, abs_neg]

/-- Compatibility form of `guessAdvantage_eq_abs_half_sub_defect`. -/
@[deprecated guessAdvantage_eq_abs_half_sub_defect (since := "2026-09-15")]
lemma ProbComp.guessAdvantage_eq_half_sub_probFailure (p : ProbComp Unit) :
    p.guessAdvantage = |1 / 2 - (Pr[⊥ | p]).toReal| := by
  rw [ProbComp.guessAdvantage_eq_abs_half_sub_defect,
    probFailure_eq_one_sub_evalDist_univ]
  rfl

/-- The guess advantage is half the gap between the missing and successful masses. -/
lemma ProbComp.guessAdvantage_eq_half_mul_abs_defect_sub_apply (p : ProbComp Unit) :
    p.guessAdvantage = 2⁻¹ * |(𝒟[p]).defect.toReal - (𝒟[p] {()}).toReal| := by
  have hunit : ({()} : Set Unit) = Set.univ := by
    ext x
    simp
  rw [ProbComp.guessAdvantage, Measure.defect_toReal, hunit]
  grind

/-- Compatibility form of `guessAdvantage_eq_half_mul_abs_defect_sub_apply`. -/
@[deprecated guessAdvantage_eq_half_mul_abs_defect_sub_apply (since := "2026-09-15")]
lemma ProbComp.guessAdvantage_eq_half_of_sub (p : ProbComp Unit) :
    p.guessAdvantage = 2⁻¹ * |(Pr[⊥ | p]).toReal - (Pr[= () | p]).toReal| := by
  simpa only [Measure.defect, probFailure_eq_one_sub_evalDist_univ,
    ← evalDist_apply_singleton] using
    ProbComp.guessAdvantage_eq_half_mul_abs_defect_sub_apply p

/-- The **advantage** between two games `p` and `q`, modeled as probabilistic computations returning
  `Unit`, is the absolute difference between their probabilities of success. -/
noncomputable def ProbComp.distAdvantage (p q : ProbComp Unit) : ℝ :=
  |(𝒟[p] {()}).toReal - (𝒟[q] {()}).toReal|

/-- A game has zero distinguishing advantage against itself. -/
@[simp]
lemma ProbComp.distAdvantage_self (p : ProbComp Unit) : p.distAdvantage p = 0 := by
  simp [ProbComp.distAdvantage]

/-- Distinguishing advantage is symmetric in its two games. -/
lemma ProbComp.distAdvantage_comm (p q : ProbComp Unit) :
    p.distAdvantage q = q.distAdvantage p :=
  abs_sub_comm _ _

/-- Distinguishing advantage equals the gap between the two games' missing masses. -/
lemma ProbComp.distAdvantage_eq_abs_sub_defect (p q : ProbComp Unit) :
    p.distAdvantage q = |(𝒟[p]).defect.toReal - (𝒟[q]).defect.toReal| := by
  have hunit : ({()} : Set Unit) = Set.univ := by
    ext x
    simp
  rw [ProbComp.distAdvantage, Measure.defect_toReal, Measure.defect_toReal, hunit]
  rw [show (1 - (𝒟[p] Set.univ).toReal) - (1 - (𝒟[q] Set.univ).toReal) =
    -((𝒟[p] Set.univ).toReal - (𝒟[q] Set.univ).toReal) by ring, abs_neg]

/-- Compatibility form of `distAdvantage_eq_abs_sub_defect`. -/
@[deprecated distAdvantage_eq_abs_sub_defect (since := "2026-09-15")]
lemma ProbComp.distAdvantage_eq_abs_sub_probFailure (p q : ProbComp Unit) :
    p.distAdvantage q = |(Pr[⊥ | p]).toReal - (Pr[⊥ | q]).toReal| := by
  simpa only [Measure.defect, probFailure_eq_one_sub_evalDist_univ] using
    ProbComp.distAdvantage_eq_abs_sub_defect p q

/-- Distinguishing advantage is nonnegative. -/
lemma ProbComp.distAdvantage_nonneg (p q : ProbComp Unit) : 0 ≤ p.distAdvantage q :=
  abs_nonneg _

/-- Triangle inequality for distinguishing advantage. -/
lemma ProbComp.distAdvantage_triangle (p q r : ProbComp Unit) :
    p.distAdvantage r ≤ p.distAdvantage q + q.distAdvantage r :=
  abs_sub_le _ _ _

/-- The distinguishing advantage between the endpoints of a chain of games is bounded by the
sum of the consecutive advantages along the chain. -/
lemma ProbComp.distAdvantage_le_sum_range {n : ℕ} (games : ℕ → ProbComp Unit) :
    (games 0).distAdvantage (games n) ≤
      ∑ i ∈ Finset.range n, (games i).distAdvantage (games (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (distAdvantage_triangle _ _ _).trans (by gcongr)

/-- Distinguishing advantage is the measure total-variation distance of the two games. -/
lemma ProbComp.distAdvantage_eq_measureTVDist (p q : ProbComp Unit) :
    p.distAdvantage q = measureTVDist p q := by
  unfold ProbComp.distAdvantage measureTVDist
  exact (Measure.tvDist_punit _ _).symm

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

/-- A failure-based security experiment with bundled successful-output measure semantics.

The surface monad can be interpreted through an internal semantic monad before its successful
outputs are observed. Failure or nontermination contributes missing mass. -/
structure SecExp (m : Type → Type w) [Monad m]
    extends MeasureSemanticsVia.{0, w, w} m where
  /-- Main experiment body. Success is interpreted as terminating without failure. -/
  main : m Unit

namespace SecExp

variable {m : Type → Type w} [Monad m]

section advantage

/-- Advantage of a failure-based security experiment: the total mass of successful executions. -/
noncomputable def advantage (exp : SecExp m) : ℝ≥0∞ :=
  exp.toMeasureSemanticsVia.evalDist exp.main Set.univ

/-- A failure-based experiment has zero advantage exactly when its successful-output measure has
zero mass. -/
@[simp]
lemma advantage_eq_zero_iff (exp : SecExp m) :
    exp.advantage = 0 ↔ exp.toMeasureSemanticsVia.evalDist exp.main Set.univ = 0 :=
  Iff.rfl

/-- A failure-based experiment has advantage `1` exactly when its successful-output measure has
full mass. -/
@[simp]
lemma advantage_eq_one_iff (exp : SecExp m) :
    exp.advantage = 1 ↔ exp.toMeasureSemanticsVia.evalDist exp.main Set.univ = 1 :=
  Iff.rfl

/-- Success advantage and failure mass sum to one. -/
@[simp]
lemma advantage_add_probFailure (exp : SecExp m) :
    exp.advantage + exp.toMeasureSemanticsVia.probFailure exp.main = 1 := by
  rw [advantage, MeasureSemanticsVia.probFailure, add_comm,
    tsub_add_cancel_of_le (exp.toMeasureSemanticsVia.evalDist_apply_univ_le_one exp.main)]

end advantage

end SecExp
