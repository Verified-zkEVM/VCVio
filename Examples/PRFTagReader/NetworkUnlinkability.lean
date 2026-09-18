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
preserve their ideal worlds and the retained collision flag, and the two output polarities
supply a symmetric security bound with explicit oracle-query budgets.
-/

public section

open OracleComp OracleSpec MeasureTheory PRFTagReader PRFTagReader.UnlinkReduction

namespace PRFTagReader.NetworkUnlinkability

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : Nat}

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

omit [SampleableType Digest] in
theorem realMultiple_eq (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    realMultiple prfs budget adversary = unlinkMultipleExp prfs adversary := by
  unfold realMultiple unlinkMultipleExp
  exact bind_congr fun key => Network.verdict_eq _ _ _ hbound _

omit [SampleableType Digest] in
theorem realSingle_eq (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    realSingle prfs budget adversary = unlinkSingleExp prfs adversary := by
  unfold realSingle unlinkSingleExp
  exact bind_congr fun key => Network.verdict_eq _ _ _ hbound _

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
        (simulateQ (multipleBadQueryImpl (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init) := by
  have h := CachedPRF.stateEvent_projection (CachedPRF.bad (sessionsPerTag := sessionsPerTag))
    (multipleBadQueryImpl (sessionsPerTag := sessionsPerTag))
    CachedPRF.projectBad CachedPRF.bad_local budget adversary hbound
    ((UnlinkState.init, []), UnlinkBadState.init) (fun state => state.2.bad)
  simp only [Function.comp_def, CachedPRF.projectBad] at h
  unfold badExperiment
  rw [h, Network.stateEvent_eq _ _ _ hbound, CachedPRF.projectMultiple_init]

/-- The two specific distinguishers from the original reduction, with no existential witness. -/
@[expose]
noncomputable def prfTerms (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) : Real :=
  PRFScheme.prfAdvantage prfs.multiplePRFScheme
      (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary) +
  PRFScheme.prfAdvantage prfs.singlePRFScheme
      (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary)

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

variable [Fintype Nonce] [Fintype Digest] [NeZero sessionsPerTag]

omit [Fintype Nonce] [Fintype Digest] [NeZero sessionsPerTag] in
/-- The list-cache ideal packet world is the ideal experiment of the same named distinguisher. -/
theorem idealMultiple_eq (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    Network.verdict (CachedPRF.multiple (sessionsPerTag := sessionsPerTag))
      budget adversary (UnlinkState.init, []) =
    PRFScheme.prfIdealExp (unlinkToMultiplePRFReduction
      (sessionsPerTag := sessionsPerTag) adversary) := by
  rw [CachedPRF.verdict_projection _ _ CachedPRF.projectMultiple CachedPRF.multiple_local
    _ _ hbound, Network.verdict_eq _ _ _ hbound,
    prfIdealExp_unlinkToMultiplePRFReduction_eq_run', CachedPRF.projectMultiple_init]

omit [Fintype Nonce] [Fintype Digest] [NeZero sessionsPerTag] in
theorem idealSingle_eq (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    Network.verdict (CachedPRF.single (sessionsPerTag := sessionsPerTag))
      budget adversary (UnlinkState.init, []) =
    PRFScheme.prfIdealExp (unlinkToSinglePRFReduction
      (sessionsPerTag := sessionsPerTag) adversary) := by
  rw [CachedPRF.verdict_projection _ _ CachedPRF.projectSingle CachedPRF.single_local
    _ _ hbound, Network.verdict_eq _ _ _ hbound,
    prfIdealExp_unlinkToSinglePRFReduction_eq_run', CachedPRF.projectSingle_init]

omit [Fintype Nonce] [Fintype Digest] in
/-- The actual multiple-world PRF hop ends in the association-list ideal packet experiment. -/
theorem multiple_prf_hop (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    PRFScheme.prfAdvantage prfs.multiplePRFScheme
      (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary) =
    |(𝒟[realMultiple prfs budget adversary] {true}).toReal -
      (𝒟[Network.verdict (CachedPRF.multiple (sessionsPerTag := sessionsPerTag))
        budget adversary (UnlinkState.init, [])] {true}).toReal| := by
  rw [realMultiple_eq _ _ _ hbound, idealMultiple_eq _ _ hbound]
  simp only [PRFScheme.prfAdvantage, ProbComp.boolDistAdvantage,
    prfRealExp_unlinkToMultiplePRFReduction_eq_unlinkMultipleExp]

omit [Fintype Nonce] [Fintype Digest] [NeZero sessionsPerTag] in
theorem single_prf_hop (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    PRFScheme.prfAdvantage prfs.singlePRFScheme
      (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary) =
    |(𝒟[realSingle prfs budget adversary] {true}).toReal -
      (𝒟[Network.verdict (CachedPRF.single (sessionsPerTag := sessionsPerTag))
        budget adversary (UnlinkState.init, [])] {true}).toReal| := by
  rw [realSingle_eq _ _ _ hbound, idealSingle_eq _ _ hbound]
  simp only [PRFScheme.prfAdvantage, ProbComp.boolDistAdvantage,
    prfRealExp_unlinkToSinglePRFReduction_eq_unlinkSingleExp]

/-- Real-network advantage is bounded by the two named PRF hops, the retained collision
flag, and all three reader-cell and nonce-aliasing losses. -/
theorem signed_bound (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) (qReader qTag : Nat)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    gap prfs (qReader + qTag) adversary ≤ prfTerms prfs adversary +
      (𝒟[badExperiment (sessionsPerTag := sessionsPerTag)
        (qReader + qTag) adversary] {true}).toReal +
      readerLoss (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) qReader qTag := by
  let : Nonempty Nonce := ⟨(SampleableType.selectElem (β := Nonce)).defaultResult⟩
  let : Nonempty Digest := ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  have hNonce : (Fintype.card Nonce : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hDigest : (Fintype.card Digest : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hdivNonce (n : Nat) : (n : ENNReal) / Fintype.card Nonce ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top n) hNonce
  have hdivDigest (n : Nat) : (n : ENNReal) / Fintype.card Digest ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top n) hDigest
  have hbound := Network.totalQueryBound adversary qReader qTag hReader hTag
  have hideal := CachedPRF.preserved_bound (sessionsPerTag := sessionsPerTag)
    adversary qReader qTag hReader hTag
  have h := ENNReal.toReal_mono (by
    simp only [ne_eq, not_false_eq_true, ENNReal.add_ne_top, measure_ne_top,
      hdivNonce, hdivDigest, and_self]) hideal
  simp only [ne_eq, not_false_eq_true, ENNReal.toReal_add, ENNReal.add_ne_top,
    measure_ne_top, hdivNonce, hdivDigest,
    and_self, ENNReal.toReal_div, ENNReal.toReal_natCast] at h
  unfold gap prfTerms readerLoss
  rw [multiple_prf_hop prfs _ _ hbound, single_prf_hop prfs _ _ hbound]
  change _ ≤ _ + (𝒟[Network.stateEvent _ _ _ _ _] {true}).toReal + _
  linarith [le_abs_self ((𝒟[realMultiple prfs (qReader + qTag) adversary] {true}).toReal -
      (𝒟[Network.verdict (CachedPRF.multiple (sessionsPerTag := sessionsPerTag))
        (qReader + qTag) adversary (UnlinkState.init, [])] {true}).toReal),
    neg_le_abs ((𝒟[realSingle prfs (qReader + qTag) adversary] {true}).toReal -
      (𝒟[Network.verdict (CachedPRF.single (sessionsPerTag := sessionsPerTag))
        (qReader + qTag) adversary (UnlinkState.init, [])] {true}).toReal)]

omit [Fintype Nonce] [Fintype Digest] [NeZero sessionsPerTag] in
/-- Output negation preserves the final list-cache bad-state observation exactly. -/
theorem badExperiment_not (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    badExperiment (sessionsPerTag := sessionsPerTag) budget
      (adversary >>= fun b => pure (!b) : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) =
    badExperiment (sessionsPerTag := sessionsPerTag) budget adversary := by
  have hnot : IsTotalQueryBound (adversary >>= fun b => pure (!b) :
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) budget := by
    rw [bind_pure_comp]
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using hbound
  rw [badExperiment_eq _ _ hnot, badExperiment_eq _ _ hbound,
    simulateQ_bind, StateT.run_bind, map_bind]
  simp only [simulateQ_pure, StateT.run_pure, map_pure, bind_pure_comp]


private theorem true_mass_not (program : ProbComp Bool) :
    (𝒟[Bool.not <$> program] {true}).toReal = 1 - (𝒟[program] {true}).toReal := by
  let : IsProbabilityMeasure 𝒟[program] := PFunctor.FreeM.isProbabilityMeasure_denote program
  have hpreimage : Bool.not ⁻¹' ({true} : Set Bool) = {false} := by
    ext b
    cases b <;> simp
  rw [evalDist_map_of_discrete, Measure.map_apply Measurable.of_discrete
    (measurableSet_singleton true), hpreimage]
  have h := congrArg ENNReal.toReal (Measure.apply_true_add_apply_false_eq_one 𝒟[program])
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_one] at h
  exact (eq_sub_iff_add_eq).2 (by simpa only [add_comm] using h)

omit [Fintype Nonce] [Fintype Digest] [NeZero sessionsPerTag] [SampleableType Digest] in
/-- Complementing the final verdict reverses the signed gap. Both real programs denote
probability measures, so their missing mass is zero. -/
theorem gap_not (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (budget : Nat) (adversary : UnlinkAdversary TagId Nonce Digest)
    (hbound : IsTotalQueryBound adversary budget) :
    gap prfs budget (adversary >>= fun b => pure (!b) :
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) = -gap prfs budget adversary := by
  have hnot : IsTotalQueryBound (adversary >>= fun b => pure (!b) :
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) budget := by
    rw [bind_pure_comp]
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using hbound
  simp only [gap, realMultiple_eq _ _ _ hnot, realSingle_eq _ _ _ hnot,
    realMultiple_eq _ _ _ hbound, realSingle_eq _ _ _ hbound,
    unlinkMultipleExp_not_map, unlinkSingleExp_not_map, true_mass_not]
  ring

/-- The symmetric network bound uses the larger of the two explicit reduction pairs,
one for each output polarity, and preserves the observed bad-state term. -/
theorem absolute_bound (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) (qReader qTag : Nat)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    |gap prfs (qReader + qTag) adversary| ≤
      max (prfTerms prfs adversary) (prfTerms prfs (adversary >>= fun b => pure (!b) :
        OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)) +
      (𝒟[badExperiment (sessionsPerTag := sessionsPerTag)
        (qReader + qTag) adversary] {true}).toReal +
      readerLoss (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) qReader qTag := by
  have hb := Network.totalQueryBound adversary qReader qTag hReader hTag
  have hpos := signed_bound prfs adversary qReader qTag hReader hTag
  have hneg := signed_bound prfs (adversary >>= fun b => pure (!b) :
    OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) qReader qTag
      (isQueryBoundP_not_bind adversary hReader) (isQueryBoundP_not_bind adversary hTag)
  rw [badExperiment_not _ _ hb, gap_not _ _ _ hb] at hneg
  have hp := le_max_left (prfTerms prfs adversary)
    (prfTerms prfs (adversary >>= fun b => pure (!b) :
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool))
  have hn := le_max_right (prfTerms prfs adversary)
    (prfTerms prfs (adversary >>= fun b => pure (!b) :
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool))
  rw [abs_le]
  constructor <;> linarith

omit [Fintype Digest] [NeZero sessionsPerTag] in
/-- The changed-cache network's collision probability has the same closed-form bound. -/
theorem collision_bound (adversary : UnlinkAdversary TagId Nonce Digest)
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

/-- Real-network unlinkability with the collision term discharged and every loss explicit. -/
theorem absolute_uniform_bound (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) (qReader qTag : Nat)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    |gap prfs (qReader + qTag) adversary| ≤
      max (prfTerms prfs adversary) (prfTerms prfs (adversary >>= fun b => pure (!b) :
        OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)) +
      ((sessionsPerTag ^ 2 * Fintype.card TagId : Nat) : Real) / Fintype.card Nonce +
      ((qReader * Fintype.card TagId : Nat) : Real) / Fintype.card Digest +
      ((qReader * qTag : Nat) : Real) / Fintype.card Nonce +
      ((qReader * Fintype.card TagId * sessionsPerTag : Nat) : Real) / Fintype.card Digest := by
  have h := absolute_bound prfs adversary qReader qTag hReader hTag
  have hc := collision_bound (sessionsPerTag := sessionsPerTag) adversary _
    (Network.totalQueryBound adversary qReader qTag hReader hTag)
  unfold readerLoss at h
  linarith

/-- Flip only the final bit, retaining every query and all retained service state. -/
@[expose]
def polarity (adversary : UnlinkAdversary TagId Nonce Digest) (flip : Bool) :
    OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool :=
  if flip then adversary >>= fun b => pure (!b) else adversary

omit [DecidableEq TagId] [Fintype TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [Fintype Nonce] [DecidableEq Digest] [SampleableType Digest] [Fintype Digest]
  [NeZero sessionsPerTag] in
theorem polarity_bound (adversary : UnlinkAdversary TagId Nonce Digest)
    (flip : Bool) (p : (UnlinkOracleSpec TagId Nonce Digest).Domain → Prop)
    [DecidablePred p] (budget : Nat) (h : IsQueryBoundP adversary p budget) :
    IsQueryBoundP (polarity adversary flip) p budget := by
  cases flip
  · exact h
  · exact isQueryBoundP_not_bind adversary h

omit [DecidableEq Nonce] [Fintype Nonce] [Fintype Digest] [SampleableType Digest]
  [NeZero sessionsPerTag] in
/-- All distinguishers used by the symmetric bound have the proved fan-out budgets. -/
theorem named_reduction_budgets (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : Nat)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) (flip : Bool) :
    IsQueryBoundP (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag)
      (polarity adversary flip)) (·.isRight) (qTag + qReader * Fintype.card TagId) ∧
    IsQueryBoundP (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag)
      (polarity adversary flip)) (·.isRight)
        (qTag + qReader * Fintype.card TagId * sessionsPerTag) :=
  ⟨QueryBudgets.multiple_reduction_bound _ _ _
      (polarity_bound _ flip _ _ hReader) (polarity_bound _ flip _ _ hTag),
    QueryBudgets.single_reduction_bound _ _ _
      (polarity_bound _ flip _ _ hReader) (polarity_bound _ flip _ _ hTag)⟩

/-- Final concrete bound under assumptions about the actual two reduction families, for both
output polarities. Query budgets are proved in `named_reduction_budgets`; no machine-time/PPT
certificate or independent-key derivation is being assumed proved by that resource result. -/
theorem full_unlinkability (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) (qReader qTag : Nat)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) (epsilonMultiple epsilonSingle : Real)
    (hMultiple : ∀ flip : Bool,
      PRFScheme.prfAdvantage prfs.multiplePRFScheme
        (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag)
          (polarity adversary flip)) ≤ epsilonMultiple)
    (hSingle : ∀ flip : Bool,
      PRFScheme.prfAdvantage prfs.singlePRFScheme
        (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag)
          (polarity adversary flip)) ≤ epsilonSingle) :
    |(𝒟[realMultiple prfs (qReader + qTag) adversary] {true}).toReal -
      (𝒟[realSingle prfs (qReader + qTag) adversary] {true}).toReal| ≤
      epsilonMultiple + epsilonSingle +
      ((sessionsPerTag ^ 2 * Fintype.card TagId : Nat) : Real) / Fintype.card Nonce +
      ((qReader * Fintype.card TagId : Nat) : Real) / Fintype.card Digest +
      ((qReader * qTag : Nat) : Real) / Fintype.card Nonce +
      ((qReader * Fintype.card TagId * sessionsPerTag : Nat) : Real) / Fintype.card Digest := by
  have h := absolute_uniform_bound prfs adversary qReader qTag hReader hTag
  have hp : prfTerms prfs adversary ≤ epsilonMultiple + epsilonSingle :=
    add_le_add (hMultiple false) (hSingle false)
  have hm : prfTerms prfs (adversary >>= fun b => pure (!b) :
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) ≤
      epsilonMultiple + epsilonSingle := add_le_add (hMultiple true) (hSingle true)
  have hmax := max_le hp hm
  unfold gap at h
  linarith

end PRFTagReader.NetworkUnlinkability
