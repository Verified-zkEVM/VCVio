/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierThin
public import HashSig.SLHDSA.SHAKE128s.Proof.SuffixCausal
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierCover
public import HashSig.SLHDSA.SHAKE128s.Proof.CoverageRouted
public import HashSig.SLHDSA.SHAKE128s.Proof.BlockViews
public import HashSig.SLHDSA.SHAKE128s.Proof.SplitCarrierTail
public import HashSig.SLHDSA.SHAKE128s.Proof.CoverageTail
public import HashSig.SLHDSA.SHAKE128s.Proof.AddressBounds
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierLeftRecord
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierCap

/-!
# The answer half at `127`: coverage with fired witnesses, charged at second order

The forgery's coverage event names witnesses: digest inputs the signer served. A served input
the adversary had asked first is in the target recording rather than the disclosing one, and such
a witness is allowed here: it is a target entry that **fired**, its input signer-randomised at
the end. `FiredCoveredRec` is the coverage event with those witnesses admitted;
`prob_carrierTail_firedCovered_le` charges it at the carrier tail, and `join_carrierTail` shows
that off `Target127.late` the answer half's event is a structural hit or fired coverage.

`FiredCoverage.prob_firedCovered_le` charges the fired coverage at
`2 ^ -126 + E[targets] · (2 ^ -129 + rightLength · 2 ^ -303)`, and at any `rightLength ≤ 2 ^ 174`
that is inside `2 ^ -126 + E[targets] / 2 ^ 128` (`second_order_fits`).

**What the run supplies.** The thinning bounds are `CarrierThin.thin1` and `thin2`, the suffix
causality is `SuffixCausal.threeStageCausalGe`, and the cell correspondences are the three-stage
run's own.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.AnswerFired

open Security DigestTape TapeFactor NoticingTape RecorderView PhaseFusion FusedTape TapeWatch
  SignedWatch TapeRunFacts CountedView CarriedWitness RecordedQueries BracketedRun CarrierTail
  CarrierThin

/-! ## Units -/

theorem unit128_sq_eq : unit128 * unit128 = 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  unfold unit128
  simp only [one_div]
  rw [← ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp)), ← Nat.cast_mul, ← pow_add]

set_option exponentiation.threshold 1024 in
/-- **The fired cells' second-order term fits in the half unit the sharper cap frees.** -/
theorem second_order_fits (rightLength : Nat) (hright : rightLength ≤ 2 ^ 174) :
    1 / ((2 ^ 129 : Nat) : ℝ≥0∞) + (rightLength : ℝ≥0∞) * (1 / ((2 ^ 303 : Nat) : ℝ≥0∞)) ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hcast : (rightLength : ℝ≥0∞) ≤ ((2 ^ 174 : Nat) : ℝ≥0∞) := by exact_mod_cast hright
  calc 1 / ((2 ^ 129 : Nat) : ℝ≥0∞) + (rightLength : ℝ≥0∞) * (1 / ((2 ^ 303 : Nat) : ℝ≥0∞))
      ≤ 1 / ((2 ^ 129 : Nat) : ℝ≥0∞) +
          ((2 ^ 174 : Nat) : ℝ≥0∞) * (1 / ((2 ^ 303 : Nat) : ℝ≥0∞)) := by gcongr
    _ = 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul]
        simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
        norm_num

/-! ## Coverage with fired witnesses, in the recordings -/

/-- **The coverage event with fired target entries admitted as witnesses.** Some target entry has
each of its fourteen leaves supplied, at its own instance, by a disclosing entry or by another
target entry that fired. -/
def FiredCoveredRec (walk : Walk)
    (w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) : Prop :=
  ∃ (target : Nat) (targetEntry : Bytes × HashOutput), w.2.2.2[target]? = some targetEntry ∧
    ∀ tree : ForsCoverage.Tree,
      (∃ leftEntry ∈ w.2.2.1, FiredCoverage.Supplies (MessageDigest.parse leftEntry.2)
          (MessageDigest.parse targetEntry.2) tree) ∨
      (∃ (helper : Nat) (helperEntry : Bytes × HashOutput), w.2.2.2[helper]? = some helperEntry ∧
        helper ≠ target ∧ Fired walk w helper ∧
        FiredCoverage.Supplies (MessageDigest.parse helperEntry.2)
          (MessageDigest.parse targetEntry.2) tree)

/-- A cell of a block read through an entry the recording holds at the same position. -/
theorem cellView_of_getElem? {tape : List HashOutput} {index : Nat} {answer : HashOutput}
    (h : tape[index]? = some answer) :
    FiredCoverage.cellView tape index = MessageDigest.parse answer := by
  unfold FiredCoverage.cellView
  rw [List.getD_eq_getElem?_getD, h]
  rfl

set_option maxHeartbeats 4000000 in
open scoped Classical in
/-- **The coverage charge with fired witnesses, at the carrier tail.** -/
theorem prob_carrierTail_firedCovered_le (adversary : Adversary) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hleftBound : ∀ result ∈ support (carrierTail keep127 adversary walk),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (carrierTail keep127 adversary walk),
      result.2.2.2.length ≤ rightLength) :
    Pr{let x ← carrierTail keep127 adversary walk}[(FiredCoveredRec walk) x] ≤
      (1 : ℝ≥0∞) / 2 ^ 126 +
        (∑' result, Pr{let x ← carrierTail keep127 adversary walk}[x = result] *
            ((result.2.2.2.length : Nat) : ℝ≥0∞)) *
          (1 / ((2 ^ 129 : Nat) : ℝ≥0∞) + (rightLength : ℝ≥0∞) * (1 / ((2 ^ 303 : Nat) : ℝ≥0∞))) := by
  classical
  have hlaw : carrierTail keep127 adversary walk =ᵈ
      Prod.snd <$> blockRunOf (tapeRun adversary walk) leftLength rightLength := by
    rw [CarrierCoverage.carrierTail_eq_threeStage]
    exact evalDist_threeStageHandlerRun_eq (σ := CountedAt (keyAt walk)) (leftAt walk)
      (rightAt walk) innerAt ServedAgreement.startServingOn ServedAgreement.stopServingOn
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)
      (fun keys => adversary.main keys.2)
      (fun keys forgery => countRecorded verifierCost
        (Scheme.verify keys.2 forgery.message forgery.signature))
      CarrierCoverage.tailValue ((startAt walk.2, 0) : Counted) [] [] leftLength rightLength
  have hsupport : support (carrierTail keep127 adversary walk) =
      support (Prod.snd <$> blockRunOf (tapeRun adversary walk) leftLength rightLength) :=
    Averaging.support_eq_of_evalDistEq hlaw
  have hevent : Pr{let x ← carrierTail keep127 adversary walk}[(FiredCoveredRec walk) x] =
      Pr{let outcome ← blockRunOf (tapeRun adversary walk) leftLength rightLength}[
        FiredCoveredRec walk outcome.2] := by
    rw [hlaw.prEvent_eq, prEvent_map]
  have hexpect : (∑' result, Pr{let x ← carrierTail keep127 adversary walk}[x = result] *
        ((result.2.2.2.length : Nat) : ℝ≥0∞)) =
      ∑' outcome, Pr{let x ← blockRunOf (tapeRun adversary walk) leftLength rightLength}[
          x = outcome] * ((outcome.2.2.2.2.length : Nat) : ℝ≥0∞) := by
    rw [show (∑' result, Pr{let x ← carrierTail keep127 adversary walk}[x = result] *
          ((result.2.2.2.length : Nat) : ℝ≥0∞)) =
        ∑' result, Pr{let x ←
            Prod.snd <$> blockRunOf (tapeRun adversary walk) leftLength rightLength}[x = result] *
          ((result.2.2.2.length : Nat) : ℝ≥0∞) from
      tsum_congr fun result => by rw [hlaw.prEvent_eq (fun x => x = result)]]
    exact BlockViews.tsum_probOutput_map _ Prod.snd _
  rw [hevent, hexpect]
  refine le_trans (prEvent_mono_of_support _ _ (FiredCoverage.FiredCovered
      (fun w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState => w.2.2.2.length)
      (Fired walk) leftLength rightLength) ?_) ?_
  · rintro outcome hmem ⟨target, targetEntry, htarget, htrees⟩
    obtain ⟨hleftTape, hrightTape, hrun⟩ :=
      NoticingTape.mem_support_blockRunOf _ leftLength rightLength outcome hmem
    have hplain : outcome.2 ∈ support (carrierTail keep127 adversary walk) := by
      rw [hsupport, support_map]
      exact ⟨outcome, hmem, rfl⟩
    have hrightLen := hrightBound _ hplain
    have hleftLen := hleftBound _ hplain
    have hRlen : outcome.1.2.length = rightLength := padding_length rightLength _ hrightTape
    have hLlen : outcome.1.1.length = leftLength := padding_length leftLength _ hleftTape
    have hcellRight : ∀ (index : Nat) (entry : Bytes × HashOutput),
        outcome.2.2.2.2[index]? = some entry → outcome.1.2[index]? = some entry.2 := by
      intro index entry hget
      have hindex : index < outcome.2.2.2.2.length := (List.getElem?_eq_some_iff.mp hget).1
      have hcell := threeStageRightOf_getElem? (σ := CountedAt (keyAt walk)) (leftAt walk)
        (rightAt walk) innerAt ServedAgreement.startServingOn ServedAgreement.stopServingOn
        (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)
        (fun keys => adversary.main keys.2)
        (fun keys forgery => countRecorded verifierCost
          (Scheme.verify keys.2 forgery.message forgery.signature))
        CarrierCoverage.tailValue ((startAt walk.2, 0) : Counted) [] [] outcome.1.1 outcome.1.2
        outcome.2 hrun index (by simpa using hindex) (by omega)
      simp only [List.length_nil, Nat.zero_add] at hcell
      rw [hget] at hcell
      exact hcell.symm
    have hcellLeft : ∀ (index : Nat) (entry : Bytes × HashOutput),
        outcome.2.2.2.1[index]? = some entry → outcome.1.1[index]? = some entry.2 := by
      intro index entry hget
      have hindex : index < outcome.2.2.2.1.length := (List.getElem?_eq_some_iff.mp hget).1
      have hcell := threeStageLeftOf_getElem? (σ := CountedAt (keyAt walk)) (leftAt walk)
        (rightAt walk) innerAt ServedAgreement.startServingOn ServedAgreement.stopServingOn
        (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)
        (fun keys => adversary.main keys.2)
        (fun keys forgery => countRecorded verifierCost
          (Scheme.verify keys.2 forgery.message forgery.signature))
        CarrierCoverage.tailValue ((startAt walk.2, 0) : Counted) [] [] outcome.1.1 outcome.1.2
        outcome.2 hrun index (by simpa using hindex) (by omega)
      simp only [List.length_nil, Nat.zero_add] at hcell
      rw [hget] at hcell
      exact hcell.symm
    have htargetLt : target < outcome.2.2.2.2.length := (List.getElem?_eq_some_iff.mp htarget).1
    refine ⟨target, by omega, htargetLt, fun tree => ?_⟩
    rw [cellView_of_getElem? (hcellRight target targetEntry htarget)]
    rcases htrees tree with ⟨leftEntry, hleftEntry, hsupplies⟩ |
      ⟨helper, helperEntry, hhelper, hne, hfired, hsupplies⟩
    · obtain ⟨cell, hcellLt, hcellGet⟩ := List.getElem_of_mem hleftEntry
      have hget : outcome.2.2.2.1[cell]? = some leftEntry := by
        rw [List.getElem?_eq_getElem hcellLt, hcellGet]
      refine Or.inl ⟨cell, by omega, ?_⟩
      rw [cellView_of_getElem? (hcellLeft cell leftEntry hget)]
      exact hsupplies
    · have hhelperLt : helper < outcome.2.2.2.2.length :=
        (List.getElem?_eq_some_iff.mp hhelper).1
      refine Or.inr ⟨helper, by omega, hhelperLt, hne, hfired, ?_⟩
      rw [cellView_of_getElem? (hcellRight helper helperEntry hhelper)]
      exact hsupplies
  · have hcharge := FiredCoverage.prob_firedCovered_le (tapeRun adversary walk)
      (fun w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState => w.2.2.2)
      (Fired walk) leftLength rightLength hcap
      (fun index cell leftTape rightTape value hle => by
        unfold tapeRun
        exact SuffixCausal.threeStageCausalGe (σ := CountedAt (keyAt walk)) (leftAt walk)
          (rightAt walk) innerAt ServedAgreement.startServingOn ServedAgreement.stopServingOn
          (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)
          (fun keys => adversary.main keys.2)
          (fun keys forgery => countRecorded verifierCost
            (Scheme.verify keys.2 forgery.message forgery.signature))
          CarrierCoverage.tailValue ((startAt walk.2, 0) : Counted) index cell leftTape
          rightTape value hle)
      (fun index leftTape rightTape =>
        thin1 adversary walk hwalk hgood index leftTape rightTape)
      (fun first second leftTape rightTape hlt => by
        rw [← unit128_sq_eq]
        exact thin2 adversary walk hwalk hgood first second hlt leftTape rightTape)
    refine le_trans hcharge (le_of_eq ?_)
    rw [mul_add, add_assoc, mul_assoc (rightLength : ℝ≥0∞),
      mul_left_comm _ (rightLength : ℝ≥0∞)]

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Scheme.sign Security.signingOracle Security.countQueries

/-! ## The join -/

set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
/-- **A served input is a logged request's digest input at the `PRF_msg` answer the cache
holds.** -/
theorem servedLog_logged (adversary : Adversary) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    (w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hw : w ∈ support (carrierTail keep127 adversary walk)) (input : Bytes)
    (hserved : ServedLog.servedLog (keyAt walk) ((w.1.1.1, w.1.2), w.2.1) input) :
    ∃ logged ∈ w.1.1.1.signed, ∃ (framed : Bytes) (answer : HashOutput),
      logged.1.frame = some framed ∧
        w.2.1 (Hashing.randomizerInput walk.1.1.2.1 walk.1.1.2.2 framed) = some answer ∧
        input = Hashing.messageInput (Hashing.truncate answer) (keyAt walk) framed := by
  classical
  have htail : FinalAssembly.forgetFused w ∈ support (WarmedGame.tail adversary walk) := by
    rw [← CarrierTail.forgetFused_carrierTail keep127 adversary walk, support_map]
    exact ⟨w, hw, rfl⟩
  have hkey := keyAt_eq_keyOf adversary walk hwalk _ htail
  have hsigner := ServedBridge.signerRandomised_of_servedLog adversary htail
    (ReplayGate.secretKeyOf ((walk.1, (FinalAssembly.forgetFused w).1),
      (FinalAssembly.forgetFused w).2)) (keyAt walk) rfl hkey input hserved
  obtain ⟨message, answer, hcached, hinput⟩ := hsigner
  obtain ⟨logged, hlogged, framed, bytes, parsed, hframe, -, -, hparsedInput⟩ := hserved
  have hsame := Hashing.messageInput_injective (hinput.symm.trans hparsedInput)
  refine ⟨logged, hlogged, framed, answer, hframe, ?_, ?_⟩
  · rw [← hsame.2.2]
    rw [keyAt_seed] at hcached
    exact hcached
  · rw [hinput, hsame.2.2]

/-- **A served input in the excluded class is the signer's coincidence.** -/
theorem late_of_served_prfClass (adversary : Adversary) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    (w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hw : w ∈ support (carrierTail keep127 adversary walk)) (input : Bytes)
    (hserved : ServedLog.servedLog (keyAt walk) ((w.1.1.1, w.1.2), w.2.1) input)
    (hprf : RandomizerGate.PrfClass walk.1.1.2.1 input) :
    Target127.Late (walk, (w.1, w.2.1)) := by
  obtain ⟨logged, hlogged, framed, answer, hframe, hcached, hinput⟩ :=
    servedLog_logged adversary walk hwalk w hw input hserved
  obtain ⟨seed, message, hmsg⟩ := hprf
  rw [hinput] at hmsg
  have htrunc := RandomizerGate.messageInput_eq_randomizerInput_iff _ walk.1.1.2.1 seed
    (keyAt walk) framed message hmsg
  exact Or.inr ⟨logged, hlogged, framed, answer, hframe, hcached, htrunc⟩

/-- **A served input is signer-randomised at the end.** -/
theorem signerRandomised_of_served (adversary : Adversary) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    (w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hw : w ∈ support (carrierTail keep127 adversary walk)) (input : Bytes)
    (hserved : ServedLog.servedLog (keyAt walk) ((w.1.1.1, w.1.2), w.2.1) input) :
    CacheAvailability.SignerRandomised walk.1.1.2.1 (keyAt walk) w.2.1 input := by
  obtain ⟨-, -, framed, answer, -, hcached, hinput⟩ :=
    servedLog_logged adversary walk hwalk w hw input hserved
  refine ⟨framed, answer, ?_, hinput⟩
  rw [keyAt_seed]
  exact hcached

/-- **The cover at `keep127`**, at the narrowed class, at every view. -/
theorem cover_keep127 (walk : Walk) (probe : Bytes) (view : HandlerCarrier.State)
    (hclass : CombinedCharge.IsMessageInput (keyAt walk) probe ∧
      ¬ RandomizerGate.PrfClass walk.1.1.2.1 probe) :
    disclosingKeep (keyAt walk) probe view ∨ keep127 walk probe view := by
  classical
  rcases CarrierCover.cover_carrierRightKeep walk probe view hclass.1 hclass.2 with hleft | hright
  · exact Or.inl hleft
  · exact Or.inr ⟨hright, hclass.2⟩

set_option maxHeartbeats 4000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **The join.** Off `late`, the answer half's event is a structural hit or coverage with fired
witnesses, at every supported result of the carrier tail. -/
theorem join_carrierTail (adversary : Adversary) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    (w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hw : w ∈ support (carrierTail keep127 adversary walk))
    (hbad : RoutedSplit.AnswerBad ((walk.1, (FinalAssembly.forgetFused w).1),
      (FinalAssembly.forgetFused w).2))
    (hlate : ¬ Target127.late (walk, w)) :
    GrowthCharge.Bad (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2) (w.1, w.2.1) ∨
      FiredCoveredRec walk w := by
  classical
  have hnotLate : ¬ Target127.Late (walk, (w.1, w.2.1)) := hlate
  have htail : FinalAssembly.forgetFused w ∈ support (WarmedGame.tail adversary walk) := by
    rw [← CarrierTail.forgetFused_carrierTail keep127 adversary walk, support_map]
    exact ⟨w, hw, rfl⟩
  have hkey := keyAt_eq_keyOf adversary walk hwalk _ htail
  have hrecorded : (w.1, w.2.1) ∈ support (RecordedTail.recordedTail adversary walk) := by
    rw [← CarrierTail.forget_carrierTail keep127 adversary walk, support_map]
    exact ⟨w, hw, rfl⟩
  rw [RoutedSplit.AnswerBad, RoutedSplit.AnswerBadAt, ← hkey] at hbad
  rcases hbad with ⟨candidates, parent, output, hdeviates, hentry, hcollision⟩ | hcovered
  · exact Or.inl (CanonicalTarget.hit_of_deviating_collision walk.1.1.2.2 walk.1.2 candidates
      parent (w.1, w.2.1) output hdeviates hentry hcollision)
  refine Or.inr ?_
  obtain ⟨message, parsed, answer, hframe, hparsed, hentry, hnotself, hcoveredAt⟩ := hcovered
  have hfreshWalk : ∀ input : Bytes, CombinedCharge.IsMessageInput (keyAt walk) input →
      walk.2 input = none :=
    fun input hclass => CoverageTail.walk_cache_fresh (keyAt walk)
      (AnswerSide.not_possible_generatedKey hwalk hgood.2) withinBounds_structural hwalk input
      hclass
  have hcover : ∀ (input : Bytes) (value : HashOutput),
      CombinedCharge.IsMessageInput (keyAt walk) input →
      ¬ RandomizerGate.PrfClass walk.1.1.2.1 input → w.2.1 input = some value →
        (input, value) ∈ w.2.2.1 ∨ (input, value) ∈ w.2.2.2 :=
    fun input value hclass hprf hfinal => CarrierCover.cover_carrierTail keep127
      (fun probe => CombinedCharge.IsMessageInput (keyAt walk) probe ∧
        ¬ RandomizerGate.PrfClass walk.1.1.2.1 probe) adversary walk
      (fun probe view hc _ => cover_keep127 walk probe view hc) w hw input value ⟨hclass, hprf⟩
      (hfreshWalk input hclass) hfinal
  have hleftServed := CarrierLeftRecord.servedLog_leftRecord_carrierTail keep127 adversary walk
    hwalk hgood.2 w hw w.1.2
  -- the forgery's own digest is a target entry
  set target := Hashing.messageInput parsed.randomizer (keyAt walk) message with htargetDef
  have htargetPrf : ¬ RandomizerGate.PrfClass walk.1.1.2.1 target := by
    intro hprf
    refine hnotLate (Or.inl ?_)
    have hkey2 : keyAt walk = RoutedSplit.keyOf ((walk.1, (w.1.1.1, w.1.2)), w.2.1) := hkey
    refine RandomiserRecord.recordMeetsPrfClass_of_forgeryDigest adversary hrecorded message
      parsed hframe hparsed ?_
    show RandomizerGate.PrfClass walk.1.1.2.1 (Hashing.messageInput parsed.randomizer
      (RoutedSplit.keyOf ((walk.1, (w.1.1.1, w.1.2)), w.2.1)) message)
    rw [← hkey2]
    exact hprf
  rcases hcover target answer ⟨parsed.randomizer, message, rfl⟩ htargetPrf hentry with
    htargetLeft | htargetRight
  · exact absurd (hleftServed _ htargetLeft) hnotself
  obtain ⟨t, htLt, htGet⟩ := List.getElem_of_mem htargetRight
  have htIndex : w.2.2.2[t]? = some (target, answer) := by
    rw [List.getElem?_eq_getElem htLt, htGet]
  refine ⟨t, (target, answer), htIndex, fun tree => ?_⟩
  obtain ⟨other, otherAnswer, hne, hserved, hother, hinstance, hleaf⟩ := hcoveredAt tree
  have hotherPrf : ¬ RandomizerGate.PrfClass walk.1.1.2.1 other := fun hprf =>
    hnotLate (late_of_served_prfClass adversary walk hwalk w hw other hserved hprf)
  rcases hcover other otherAnswer (ServedLog.isMessageInput_of_servedLog _ _ other hserved)
    hotherPrf hother with hotherLeft | hotherRight
  · exact Or.inl ⟨(other, otherAnswer), hotherLeft, hinstance, hleaf⟩
  · obtain ⟨j, hjLt, hjGet⟩ := List.getElem_of_mem hotherRight
    have hjIndex : w.2.2.2[j]? = some (other, otherAnswer) := by
      rw [List.getElem?_eq_getElem hjLt, hjGet]
    refine Or.inr ⟨j, (other, otherAnswer), hjIndex, fun hjt => ?_, ?_, hinstance, hleaf⟩
    · subst hjt
      rw [hjIndex] at htIndex
      exact hne (congrArg Prod.fst (Option.some.inj htIndex))
    · exact ⟨(other, otherAnswer), hjIndex,
        signerRandomised_of_served adversary walk hwalk w hw other hserved, hnotLate⟩

/-! ## The keep predicate's class -/

theorem keep127_class (walk : Walk) (input : Bytes) (view : HandlerCarrier.State)
    (hkeep : keep127 walk input view) : CombinedCharge.IsMessageInput (keyAt walk) input :=
  AnswerCarrier.carrierRightKeep_class walk input view hkeep.1

/-- The two counter slots the split tail uses. -/
theorem hash_ne_verification : Game.QueryKind.hash ≠ Game.QueryKind.verification := by decide

/-! ## The defects' arithmetic -/

set_option exponentiation.threshold 1024 in
theorem defects_le : Target.defectsAt ((1 : ℝ≥0∞) / 2 ^ 126) ≤
    ((6 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  unfold Target.defectsAt
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  norm_num

end SlhDsaSecurity.AnswerFired
