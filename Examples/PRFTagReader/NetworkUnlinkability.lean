/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.CacheRepresentation
public import Examples.PRFTagReader.UnlinkReduction
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Real-network unlinkability with association-list caches

The bounded FIFO experiment implements the named PRF reductions. Local cache projections
preserve their ideal worlds and the retained collision flag, and the direct coupling, which bounds
the mass of either verdict, gives a symmetric security bound with explicit oracle-query budgets.
-/

public section

open OracleComp OracleSpec MeasureTheory PRFTagReader PRFTagReader.UnlinkReduction

namespace PRFTagReader.NetworkUnlinkability

variable {TagId Nonce Digest K : Type} {sessionsPerTag : Nat}

/-- Both named distinguishers have the proved fan-out budgets. -/
theorem named_reduction_budgets [DecidableEq TagId] [Fintype TagId] [SampleableType Nonce]
    [DecidableEq Digest] (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : Nat)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    IsQueryBoundP (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary)
      (·.isRight) (qTag + qReader * Fintype.card TagId) ∧
    IsQueryBoundP (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary)
      (·.isRight) (qTag + qReader * Fintype.card TagId * sessionsPerTag) :=
  ⟨QueryBudgets.multiple_reduction_bound _ _ _ hReader hTag,
    QueryBudgets.single_reduction_bound _ _ _ hReader hTag⟩

variable [DecidableEq TagId] [Fintype TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest]

/-- Key generation followed by actual bounded FIFO execution of the multiple-session service. -/
@[expose]
def realMultiple (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest) : ProbComp Bool := do
  let key ← prfs.keygen
  Network.verdict (unlinkMultipleQueryImpl prfs key) budget adversary UnlinkState.init

/-- Key generation followed by actual bounded FIFO execution of the single-session service. -/
@[expose]
def realSingle (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest) : ProbComp Bool := do
  let key ← prfs.keygen
  Network.verdict (unlinkSingleQueryImpl prfs key) budget adversary UnlinkState.init

theorem realMultiple_eq (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    realMultiple prfs budget adversary = unlinkMultipleExp prfs adversary := by
  unfold realMultiple unlinkMultipleExp
  exact bind_congr fun key => Network.verdict_eq _ _ _ hbound _

theorem realSingle_eq (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    realSingle prfs budget adversary = unlinkSingleExp prfs adversary := by
  unfold realSingle unlinkSingleExp
  exact bind_congr fun key => Network.verdict_eq _ _ _ hbound _

/-- The PRF advantages of the two named distinguishers, with no existential witness. -/
@[expose]
noncomputable def prfTerms [SampleableType Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) : Real :=
  (PRFScheme.prfAdvantage prfs.multiplePRFScheme
      (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary)).toReal +
  (PRFScheme.prfAdvantage prfs.singlePRFScheme
      (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary)).toReal

/-- All three reader-cell and nonce-aliasing losses, kept separately in the definition. -/
@[expose]
noncomputable def readerLoss [Fintype Nonce] [Fintype Digest] (qReader qTag : Nat) : Real :=
  ((qReader * Fintype.card TagId : Nat) : Real) / (Fintype.card Digest : Real) +
  ((qReader * qTag : Nat) : Real) / (Fintype.card Nonce : Real) +
  ((qReader * Fintype.card TagId * sessionsPerTag : Nat) : Real) /
    (Fintype.card Digest : Real)

/-- Signed difference of real packet-execution verdict probabilities. -/
@[expose]
noncomputable def gap (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest) : Real :=
  (𝒟[realMultiple prfs budget adversary] {true}).toReal -
  (𝒟[realSingle prfs budget adversary] {true}).toReal

variable [SampleableType Digest]

/-- The collision flag is observed in the instrumented association-list packet service. -/
@[expose]
noncomputable def badExperiment (budget : Nat)
    (adversary : UnlinkAdversary TagId Nonce Digest) : ProbComp Bool :=
  Network.stateEvent (CachedPRF.bad (sessionsPerTag := sessionsPerTag)) budget adversary
    ((UnlinkState.init, []), UnlinkBadState.init) (fun state => state.2.bad)

theorem badExperiment_eq (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    badExperiment (sessionsPerTag := sessionsPerTag) budget adversary =
      (fun out => out.2.2.bad) <$>
        (simulateQ (multipleBadQueryImpl _ _ _ sessionsPerTag) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init) := by
  have h := CachedPRF.stateEvent_projection (CachedPRF.bad (sessionsPerTag := sessionsPerTag))
    (multipleBadQueryImpl _ _ _ sessionsPerTag)
    CachedPRF.projectBad CachedPRF.bad_local budget adversary hbound
    ((UnlinkState.init, []), UnlinkBadState.init) (fun state => state.2.bad)
  simp only [Function.comp_def, CachedPRF.projectBad] at h
  unfold badExperiment
  rw [h, Network.stateEvent_eq _ _ _ hbound, CachedPRF.projectMultiple_init]

/-- The list-cache ideal packet world is the ideal experiment of the same named distinguisher. -/
theorem idealMultiple_eq (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    Network.verdict (CachedPRF.multiple (sessionsPerTag := sessionsPerTag))
      budget adversary (UnlinkState.init, []) =
    PRFScheme.prfIdealExperiment (unlinkToMultiplePRFReduction
      (sessionsPerTag := sessionsPerTag) adversary) := by
  rw [CachedPRF.verdict_projection _ _ CachedPRF.projectMultiple CachedPRF.multiple_local
    _ _ hbound, Network.verdict_eq _ _ _ hbound,
    prfIdealExp_unlinkToMultiplePRFReduction_eq_run', CachedPRF.projectMultiple_init]

theorem idealSingle_eq (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    Network.verdict (CachedPRF.single (sessionsPerTag := sessionsPerTag))
      budget adversary (UnlinkState.init, []) =
    PRFScheme.prfIdealExperiment (unlinkToSinglePRFReduction
      (sessionsPerTag := sessionsPerTag) adversary) := by
  rw [CachedPRF.verdict_projection _ _ CachedPRF.projectSingle CachedPRF.single_local
    _ _ hbound, Network.verdict_eq _ _ _ hbound,
    prfIdealExp_unlinkToSinglePRFReduction_eq_run', CachedPRF.projectSingle_init]

theorem single_prf_hop (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    (PRFScheme.prfAdvantage prfs.singlePRFScheme
      (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary)).toReal =
    |(𝒟[realSingle prfs budget adversary] {true}).toReal -
      (𝒟[Network.verdict (CachedPRF.single (sessionsPerTag := sessionsPerTag))
        budget adversary (UnlinkState.init, [])] {true}).toReal| := by
  rw [realSingle_eq _ _ _ hbound, idealSingle_eq _ _ hbound]
  simp only [PRFScheme.prfAdvantage, MeasureTheory.Measure.toReal_boolDist,
    prfRealExp_unlinkToSinglePRFReduction_eq_unlinkSingleExp]

/-- The actual multiple-world PRF hop ends in the association-list ideal packet experiment. -/
theorem multiple_prf_hop [NeZero sessionsPerTag]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    (PRFScheme.prfAdvantage prfs.multiplePRFScheme
      (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary)).toReal =
    |(𝒟[realMultiple prfs budget adversary] {true}).toReal -
      (𝒟[Network.verdict (CachedPRF.multiple (sessionsPerTag := sessionsPerTag))
        budget adversary (UnlinkState.init, [])] {true}).toReal| := by
  rw [realMultiple_eq _ _ _ hbound, idealMultiple_eq _ _ hbound]
  simp only [PRFScheme.prfAdvantage, MeasureTheory.Measure.toReal_boolDist,
    prfRealExp_unlinkToMultiplePRFReduction_eq_unlinkMultipleExp]

/-- The changed-cache network's collision probability has the same closed-form bound. -/
theorem collision_bound [Fintype Nonce] (adversary : UnlinkAdversary TagId Nonce Digest)
    (budget : Nat) (hbound : IsTotalQueryBound adversary budget) :
    (𝒟[badExperiment (sessionsPerTag := sessionsPerTag) budget adversary] {true}).toReal ≤
      ((sessionsPerTag ^ 2 * Fintype.card TagId : Nat) : Real) / Fintype.card Nonce := by
  rw [badExperiment_eq _ _ hbound]
  let : MeasurableSpace Nonce := ⊤
  have hmax : ∀ nonce : Nonce,
      (Pr{let n ← $ᵗ Nonce}[n = nonce]).toReal ≤ (Fintype.card Nonce : Real)⁻¹ := by
    intro nonce
    simp only [prEvent_eq_evalDist_singleton, SampleableType.evalDist_uniformSample_singleton,
      ENNReal.toReal_inv, ENNReal.toReal_natCast, le_refl]
  simpa only [div_eq_mul_inv] using
    multipleBad_bad_le_sessionCollisionBound (sessionsPerTag := sessionsPerTag)
      adversary _ hmax

variable [Fintype Nonce] [Fintype Digest] [NeZero sessionsPerTag]

/-- Real-network advantage is bounded by the two named PRF hops, the retained collision
flag, and all three reader-cell and nonce-aliasing losses. -/
theorem absolute_bound (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) (qReader qTag : Nat)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    |gap prfs (qReader + qTag) adversary| ≤ prfTerms prfs adversary +
      (𝒟[badExperiment (sessionsPerTag := sessionsPerTag)
        (qReader + qTag) adversary] {true}).toReal +
      readerLoss (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) qReader qTag := by
  have hNonce : (Fintype.card Nonce : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hDigest : (Fintype.card Digest : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hdivNonce (n : Nat) : (n : ENNReal) / Fintype.card Nonce ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top n) hNonce
  have hdivDigest (n : Nat) : (n : ENNReal) / Fintype.card Digest ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top n) hDigest
  have hbound := Network.totalQueryBound adversary qReader qTag hReader hTag
  have hideal := fun out => CachedPRF.preserved_bound (sessionsPerTag := sessionsPerTag)
    out adversary qReader qTag hReader hTag
  simp only [add_assoc] at hideal
  let : IsProbabilityMeasure 𝒟[Network.verdict (CachedPRF.multiple
      (sessionsPerTag := sessionsPerTag)) (qReader + qTag) adversary (UnlinkState.init, [])] :=
    PFunctor.FreeM.isProbabilityMeasure_denote _
  let : IsProbabilityMeasure 𝒟[Network.verdict (CachedPRF.single
      (sessionsPerTag := sessionsPerTag)) (qReader + qTag) adversary (UnlinkState.init, [])] :=
    PFunctor.FreeM.isProbabilityMeasure_denote _
  have h := ENNReal.toReal_mono (by
    simp only [ne_eq, not_false_eq_true, ENNReal.add_ne_top, measure_ne_top,
      hdivNonce, hdivDigest, and_self]) (Measure.boolDist_le_of_apply_le _ _ hideal)
  simp only [ne_eq, not_false_eq_true, ENNReal.toReal_add, ENNReal.add_ne_top,
    measure_ne_top, hdivNonce, hdivDigest, and_self, ENNReal.toReal_div,
    ENNReal.toReal_natCast, Measure.toReal_boolDist] at h
  unfold gap prfTerms readerLoss
  rw [multiple_prf_hop prfs _ _ hbound, single_prf_hop prfs _ _ hbound]
  change _ ≤ _ + (𝒟[Network.stateEvent _ _ _ _ _] {true}).toReal + _
  set realM := (𝒟[realMultiple prfs (qReader + qTag) adversary] {true}).toReal
  set realS := (𝒟[realSingle prfs (qReader + qTag) adversary] {true}).toReal
  set cachedMultiple := (𝒟[Network.verdict (CachedPRF.multiple (sessionsPerTag := sessionsPerTag))
    (qReader + qTag) adversary (UnlinkState.init, [])] {true}).toReal
  set cachedSingle := (𝒟[Network.verdict (CachedPRF.single (sessionsPerTag := sessionsPerTag))
    (qReader + qTag) adversary (UnlinkState.init, [])] {true}).toReal
  have t1 := abs_sub_le realM cachedMultiple realS
  have t2 := abs_sub_le cachedMultiple cachedSingle realS
  rw [abs_sub_comm cachedSingle] at t2
  linarith

/-- Real-network unlinkability with the collision term discharged and every loss explicit. -/
theorem absolute_uniform_bound (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) (qReader qTag : Nat)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    |gap prfs (qReader + qTag) adversary| ≤ prfTerms prfs adversary +
      ((sessionsPerTag ^ 2 * Fintype.card TagId : Nat) : Real) / Fintype.card Nonce +
      ((qReader * Fintype.card TagId : Nat) : Real) / Fintype.card Digest +
      ((qReader * qTag : Nat) : Real) / Fintype.card Nonce +
      ((qReader * Fintype.card TagId * sessionsPerTag : Nat) : Real) / Fintype.card Digest := by
  have h := absolute_bound prfs adversary qReader qTag hReader hTag
  have hc := collision_bound (sessionsPerTag := sessionsPerTag) adversary _
    (Network.totalQueryBound adversary qReader qTag hReader hTag)
  unfold readerLoss at h
  linarith

/-- Final concrete bound under assumptions about the actual two reduction families. Query budgets
are proved in `named_reduction_budgets`; no machine-time/PPT certificate or independent-key
derivation is being assumed proved by that resource result. -/
theorem full_unlinkability (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) (qReader qTag : Nat)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) (epsilonMultiple epsilonSingle : Real)
    (hMultiple : (PRFScheme.prfAdvantage prfs.multiplePRFScheme
      (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary)).toReal ≤
        epsilonMultiple)
    (hSingle : (PRFScheme.prfAdvantage prfs.singlePRFScheme
      (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary)).toReal ≤
        epsilonSingle) :
    |(𝒟[realMultiple prfs (qReader + qTag) adversary] {true}).toReal -
      (𝒟[realSingle prfs (qReader + qTag) adversary] {true}).toReal| ≤
      epsilonMultiple + epsilonSingle +
      ((sessionsPerTag ^ 2 * Fintype.card TagId : Nat) : Real) / Fintype.card Nonce +
      ((qReader * Fintype.card TagId : Nat) : Real) / Fintype.card Digest +
      ((qReader * qTag : Nat) : Real) / Fintype.card Nonce +
      ((qReader * Fintype.card TagId * sessionsPerTag : Nat) : Real) / Fintype.card Digest := by
  have h := absolute_uniform_bound prfs adversary qReader qTag hReader hTag
  have hp : prfTerms prfs adversary ≤ epsilonMultiple + epsilonSingle :=
    add_le_add hMultiple hSingle
  unfold gap at h
  linarith

end PRFTagReader.NetworkUnlinkability
