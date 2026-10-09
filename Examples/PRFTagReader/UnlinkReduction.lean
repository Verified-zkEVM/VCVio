/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import Examples.PRFTagReader.MultipleBadCollision
public import Examples.PRFTagReader.ReductionBudgets
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Unlinkability PRF Reduction

Top-level PRF reduction for the tag/reader unlinkability game of `Examples.PRFTagReader`. The
unlinkability advantage `unlinkabilityAdvantage` is the Boolean distance between the
multiple-session world `unlinkMultipleExperiment` (all sessions of a tag share one secret) and the
single-session world `unlinkSingleExperiment` (each session uses an independent secret).

The reduction chains three Boolean distances through the triangle inequality:

* a PRF hop replacing `prfs.evalMultiple` by a lazy random function turns `unlinkMultipleExperiment`
  into the ideal-PRF world of `unlinkToMultiplePRFReduction`;
* the coupling `unlinkPRFIdeal_boolDist_le_unlinkBad` bounds the distance between the two
  random-function worlds by the `multipleBadQueryImpl` bad-flag probability (the within-tag
  nonce-collision mass) and three unconditional slack terms;
* a second PRF hop replacing `prfs.evalSingle` turns `unlinkSingleExperiment` into the ideal-PRF
  world of `unlinkToSinglePRFReduction`.

The headline is `unlinkabilityAdvantage_le_two_prf_plus_collision`. Chaining
`multipleBad_bad_le_sessionCollisionBound` yields the explicit session-collision bound
`unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound` and its uniform-Nonce
specialization.

Every bound is stated for the explicit reductions `unlinkToMultiplePRFReduction` and
`unlinkToSinglePRFReduction` applied to the unlinkability adversary. An existentially quantified
PRF adversary would make the bounds trivially satisfiable, since an unbounded PRF distinguisher
has advantage close to `1`. -/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type} {sessionsPerTag : ℕ}
  [DecidableEq TagId] [Fintype TagId] [SampleableType Nonce] [DecidableEq Digest]

/-! ## Main reduction theorem -/

/-- Unlinkability reduction: the Boolean distance between the multiple- and single-session
experiments is bounded by one PRF advantage for each world, the bad-event probability of the
intermediate nonce-collision world, and three unconditional slack terms. The bound holds for every
adversary.

The proof chains `unlinkMultipleExperiment`, the two ideal-PRF worlds and `unlinkSingleExperiment`
through the triangle inequality for `Measure.boolDist`: the outer distances are the two PRF
advantages and the middle distance is `unlinkPRFIdeal_boolDist_le_unlinkBad`. Each slack is charged
by an identified proof step in the direct coupling: the single-session world keys `sessionsPerTag`
times more random-oracle cells than the multiple-session world, an unconditional cell-count gap
unrelated to nonce collisions. They comprise the reader-cell slacks
`qReader * Fintype.card TagId / Fintype.card Digest` and
`qReader * Fintype.card TagId * sessionsPerTag / Fintype.card Digest` (the latter charged at the
discarded reader step via `probEvent_cacheBadReader_uniformSample_le`), and the nonce-aliasing
slack `qReader * qTag / Fintype.card Nonce` (charged at slot-positive tag steps via the
reader-touched-set membership event). There is no tag-side slack.

The efficiency measure for the two reductions is their PRF-oracle query count. Each reduction
issues one PRF query per tag query and one PRF query per slot at every reader query, so the
PRF-oracle query count is bounded by `qTag + qReader · |TagId|` (multiple-session) and
`qTag + qReader · |TagId| · sessionsPerTag` (single-session). The pathwise bounds are proved by
`QueryBudgets.multiple_reduction_bound` and `QueryBudgets.single_reduction_bound`. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_collision [DecidableEq Nonce]
    [SampleableType Digest] [NeZero sessionsPerTag] [Fintype Nonce] [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag) :
    unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) prfs adversary ≤
      PRFScheme.prfAdvantage prfs.multiplePRFScheme
          (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary) +
        PRFScheme.prfAdvantage prfs.singlePRFScheme
          (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary) +
        𝒟[(fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad) <$>
          (simulateQ (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag) adversary).run
            ((UnlinkState.init, ∅), UnlinkBadState.init)] {true} +
        ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
        ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
        ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
          (Fintype.card Digest : ℝ≥0∞) := by
  have hideal := unlinkPRFIdeal_boolDist_le_unlinkBad (sessionsPerTag := sessionsPerTag)
    adversary qReader qTag hqReader hqTag
  rw [unlinkabilityAdvantage, PRFScheme.prfAdvantage, PRFScheme.prfAdvantage,
    prfRealExperiment_unlinkToMultiplePRFReduction_eq_unlinkMultipleExperiment,
    prfRealExperiment_unlinkToSinglePRFReduction_eq_unlinkSingleExperiment]
  set multipleIdeal := 𝒟[PRFScheme.prfIdealExperiment
    (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary)]
  set singleIdeal := 𝒟[PRFScheme.prfIdealExperiment
    (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary)]
  calc _ ≤ _ + multipleIdeal.boolDist _ := Measure.boolDist_triangle _ multipleIdeal _
    _ ≤ _ + (multipleIdeal.boolDist singleIdeal + singleIdeal.boolDist _) := by
      gcongr; exact Measure.boolDist_triangle _ singleIdeal _
    _ ≤ _ := by
      rw [Measure.boolDist_comm singleIdeal]
      grw [hideal]
      exact le_of_eq (by ring)

/-! ## Explicit session-collision bounds -/

/-- Unlinkability bound with the collision term discharged: two PRF advantages, the closed-form
session-collision bound `(sessionsPerTag^2 * |TagId|) * maxNonceProb` from
`multipleBad_bad_le_sessionCollisionBound`, and the three unconditional reader-cell and
nonce-aliasing slack terms of `unlinkabilityAdvantage_le_two_prf_plus_collision`. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound [DecidableEq Nonce]
    [SampleableType Digest] [NeZero sessionsPerTag] [Fintype Nonce] [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag)
    (maxNonceProb : ℝ)
    (hmax : ∀ nonce : Nonce, (Pr{let n ← $ᵗ Nonce}[n = nonce]).toReal ≤ maxNonceProb) :
    (unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) prfs adversary).toReal ≤
      (PRFScheme.prfAdvantage prfs.multiplePRFScheme
          (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary)).toReal +
        (PRFScheme.prfAdvantage prfs.singlePRFScheme
          (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary)).toReal +
        ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) * maxNonceProb +
        ((qReader * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) +
        ((qReader * qTag : ℕ) : ℝ) / (Fintype.card Nonce : ℝ) +
        ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
          (Fintype.card Digest : ℝ) := by
  have hNonce : (Fintype.card Nonce : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hDigest : (Fintype.card Digest : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hdivNonce (n : ℕ) : (n : ℝ≥0∞) / Fintype.card Nonce ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top n) hNonce
  have hdivDigest (n : ℕ) : (n : ℝ≥0∞) / Fintype.card Digest ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top n) hDigest
  have h := ENNReal.toReal_mono (by
    simp only [PRFScheme.prfAdvantage, ne_eq, ENNReal.add_ne_top, Measure.boolDist_ne_top,
      measure_ne_top, hdivNonce, hdivDigest, not_false_eq_true, and_self])
    (unlinkabilityAdvantage_le_two_prf_plus_collision prfs adversary qReader qTag hqReader hqTag)
  simp only [PRFScheme.prfAdvantage, ne_eq, ENNReal.add_ne_top, Measure.boolDist_ne_top,
    measure_ne_top, hdivNonce, hdivDigest, not_false_eq_true, and_self, ENNReal.toReal_add,
    ENNReal.toReal_div, ENNReal.toReal_natCast] at h
  have hbad := multipleBad_bad_le_sessionCollisionBound (sessionsPerTag := sessionsPerTag)
    adversary maxNonceProb hmax
  simp only [PRFScheme.prfAdvantage]
  linarith

/-- Unlinkability bound for uniformly sampled nonces (as enforced by `SampleableType`): the
session-collision term is `sessionsPerTag² · |TagId| / |Nonce|`, plus the three unconditional
reader-cell and nonce-aliasing slack terms. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_uniform_sessionCollisionBound [DecidableEq Nonce]
    [SampleableType Digest] [NeZero sessionsPerTag] [Fintype Nonce] [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag) :
    (unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) prfs adversary).toReal ≤
      (PRFScheme.prfAdvantage prfs.multiplePRFScheme
          (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary)).toReal +
        (PRFScheme.prfAdvantage prfs.singlePRFScheme
          (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary)).toReal +
        ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Nonce : ℝ) +
        ((qReader * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) +
        ((qReader * qTag : ℕ) : ℝ) / (Fintype.card Nonce : ℝ) +
        ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
          (Fintype.card Digest : ℝ) := by
  let : MeasurableSpace Nonce := ⊤
  have hmax : ∀ nonce : Nonce,
      (Pr{let n ← $ᵗ Nonce}[n = nonce]).toReal ≤ (Fintype.card Nonce : ℝ)⁻¹ := by
    intro nonce
    simp only [prEvent_eq_evalDist_singleton, SampleableType.evalDist_uniformSample_singleton,
      ENNReal.toReal_inv, ENNReal.toReal_natCast, le_refl]
  simpa only [div_eq_mul_inv] using unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound
    prfs adversary qReader qTag hqReader hqTag _ hmax

end UnlinkReduction

end PRFTagReader
