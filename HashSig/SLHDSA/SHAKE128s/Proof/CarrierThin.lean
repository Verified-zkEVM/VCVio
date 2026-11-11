/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierThinStages
import VCVio.OracleComp.EvalDist.Sum

/-!
# The fired cells are thinned by a fresh `PRF_msg` answer

This file proves the two thinning bounds `FiredCoverage.prob_firedCovered_le` asks of the carrier
tail's tape run, with both blocks fixed:

* `thin1`: reaching a target cell and then seeing it fire (`Fired`) costs `2 ^ -128` on top of
  reaching it;
* `thin2`: reaching two target cells and seeing both fire costs `2 ^ -256` on top of reaching the
  first.

Both are assembled from the per-stage supermartingale steps of `CarrierThinStages` by
`SignedWatch.expect_bind_signed_le`, once through each of key generation, the fused adversary phase
and verification. The end of the run is read off the handler (`end_condition`): a reached cell
that fired has watched value one, since its `PRF_msg` answer can be neither in the disclosing
recording (`leftEntry_logged`) nor in the target recording. The pair bound watches two cells at
once; their product is a supermartingale because the run keeps its target entries cached and
distinct (`RightDistinct`), so one fresh answer never makes both fire (`hits_disjoint`).
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.CarrierThin

open Security DigestTape TapeFactor NoticingTape RecorderView PhaseFusion FusedTape TapeWatch
  SignedWatch TapeRunFacts CountedView CarriedWitness RecordedQueries BracketedRun CarrierTail

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Scheme.sign Security.signingOracle Security.countQueries

/-! ## What the run's end holds, read off the handler

A supported result of the tape run is a supported result of the carrier tail, so the facts the
handler already proves about its final results hold here: every disclosing entry is the digest
input of a logged request at the `PRF_msg` answer the cache holds. -/

/-- **The tape run's results are the carrier tail's.** -/
theorem mem_support_carrierTail_of_tapeRun (adversary : Adversary) (walk : Walk)
    (leftTape rightTape : List HashOutput)
    (w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hw : w ∈ support (tapeRun adversary walk leftTape rightTape)) :
    w ∈ support (carrierTail keep127 adversary walk) := by
  rw [CarrierCoverage.carrierTail_eq_threeStage]
  exact mem_support_threeStageHandlerRun_of_tape (σ := CountedAt (keyAt walk)) (leftAt walk)
    (rightAt walk) innerAt ServedAgreement.startServingOn ServedAgreement.stopServingOn
    (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)
    (fun keys => adversary.main keys.2)
    (fun keys forgery => countRecorded verifierCost
      (Scheme.verify keys.2 forgery.message forgery.signature))
    CarrierCoverage.tailValue ((startAt walk.2, 0) : Counted) [] [] leftTape rightTape w hw

/-- **The key a carrier tail's result names is the walk's.** -/
theorem keyAt_eq_keyOf (adversary : Adversary) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    (result : (Outcome × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support (WarmedGame.tail adversary walk)) :
    keyAt walk = RoutedSplit.keyOf ((walk.1, result.1), result.2) :=
  (AnswerSide.generatedKey_eq_walk adversary hwalk hresult).symm

/-- **Every disclosing entry is a logged request's digest input**, at the `PRF_msg` answer the
final cache holds for it. -/
theorem leftEntry_logged (adversary : Adversary) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    (w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hw : w ∈ support (carrierTail keep127 adversary walk))
    (entry : Bytes × HashOutput) (hentry : entry ∈ w.2.2.1) :
    ∃ logged ∈ w.1.1.1.signed, ∃ (framed : Bytes) (answer : HashOutput),
      logged.1.frame = some framed ∧
        w.2.1 (Hashing.randomizerInput walk.1.1.2.1 walk.1.1.2.2 framed) = some answer ∧
        entry.1 = Hashing.messageInput (Hashing.truncate answer) (keyAt walk) framed := by
  classical
  have hserved := CarrierLeftRecord.servedLog_leftRecord_carrierTail keep127 adversary walk
    hwalk hgood.2 w hw w.1.2 entry hentry
  have htail : FinalAssembly.forgetFused w ∈ support (WarmedGame.tail adversary walk) := by
    rw [← CarrierTail.forgetFused_carrierTail keep127 adversary walk, support_map]
    exact ⟨w, hw, rfl⟩
  have hkey := keyAt_eq_keyOf adversary walk hwalk _ htail
  have hsigner := ServedBridge.signerRandomised_of_servedLog adversary htail
    (ReplayGate.secretKeyOf ((walk.1, (FinalAssembly.forgetFused w).1),
      (FinalAssembly.forgetFused w).2)) (keyAt walk) rfl hkey entry.1 hserved
  obtain ⟨message, answer, hcached, hinput⟩ := hsigner
  obtain ⟨logged, hlogged, framed, bytes, parsed, hframe, -, -, hparsedInput⟩ := hserved
  have hsame := Hashing.messageInput_injective (hinput.symm.trans hparsedInput)
  refine ⟨logged, hlogged, framed, answer, hframe, ?_, ?_⟩
  · rw [← hsame.2.2]
    rw [keyAt_seed] at hcached
    exact hcached
  · rw [hinput, hsame.2.2]

/-! ## The end of the run -/

/-- **Target cell `index` fired**: its input is signer-randomised at the end, and `late` did not
happen. -/
@[expose] def Fired (walk : Walk) (w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (index : Nat) : Prop :=
  ∃ entry, w.2.2.2[index]? = some entry ∧
    CacheAvailability.SignerRandomised walk.1.1.2.1 (keyAt walk) w.2.1 entry.1 ∧
    ¬ Target127.Late (walk, (w.1, w.2.1))

/-- The run's record holds a seed guess. -/
theorem prfHit_of_mem (walk : Walk)
    (w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (y : Bytes) (hy : y ∈ w.1.1.2) (hprf : RandomizerGate.PrfClass walk.1.1.2.1 y) :
    Target127.Late (walk, (w.1, w.2.1)) :=
  Or.inl ⟨y, Multiset.mem_toFinset.mpr hy, hprf⟩

open scoped Classical in
/-- **At the end, a reached cell that fired has watched value one, and `late` so far is off.** -/
theorem end_condition (adversary : Adversary) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk) (index : Nat)
    (leftTape rightTape : List HashOutput) (middle : Forgery × FState walk)
    (final : (Bool × Tally) × SplitTapeState (CountedAt (keyAt walk)))
    (hfinal : final ∈ support ((simulateQ (noticingSplitTapeRecorder (leftAt walk)
      (rightAt walk)) (countRecorded verifierCost
        (Scheme.verify (keyAt walk) middle.1.message middle.1.signature))).run middle.2.2.2))
    (hinv : Inv3 walk (Late2 walk middle.2) (cacheF walk middle.2) final.2)
    (hw : (CarrierCoverage.tailValue (skAt walk, keyAt walk) middle.1 middle.2.1 middle.2.2.1
        final.1 final.2.1, forgetViewTape final.2) ∈
      support (tapeRun adversary walk leftTape rightTape)) :
    (if index < (forgetViewTape final.2).2.2.length ∧
        Fired walk (CarrierCoverage.tailValue (skAt walk, keyAt walk) middle.1 middle.2.1
          middle.2.2.1 final.1 final.2.1, forgetViewTape final.2) index then 1 else 0) ≤
      value3 walk index (Late2 walk middle.2) (cacheF walk middle.2) final.2 := by
  classical
  set w := (CarrierCoverage.tailValue (skAt walk, keyAt walk) middle.1 middle.2.1 middle.2.2.1
    final.1 final.2.1, forgetViewTape final.2) with hwDef
  split_ifs with hevent
  swap
  · exact zero_le
  obtain ⟨-, entry, hget, hsigner, hnotLate⟩ := hevent
  have hcacheW : w.2.1 = CacheView.cacheOf final.2.1 := rfl
  have hrightW : w.2.2.2 = final.2.2.2.2 := rfl
  have hrecordW : w.1.1.2 = (Multiplicative.toAdd middle.2.1).2 + final.1.2.2 := rfl
  have hsignedW : w.1.1.1.signed = middle.2.2.1 := rfl
  -- `late` so far is off
  have hnotLate3 : ¬ Late3 walk (Late2 walk middle.2) (cacheF walk middle.2) final.2 := by
    rintro ((⟨y, hy, hprf⟩ | hhit) | ⟨y, hprf, hpresent, hfresh⟩)
    · exact hnotLate (prfHit_of_mem walk w y
        (by rw [hrecordW]; exact Multiset.mem_add.mpr (Or.inl hy)) hprf)
    · refine hnotLate (Or.inr ?_)
      change RandomiserProvenance.SignerHitsSeed walk.1.1.2.1 walk.1.1.2.2 w.2.1 w.1.1.1.signed
      rw [hcacheW, hsignedW]
      exact signerHitsSeed_mono (fun input answer h => run_cache_persists _ _ _ _ final hfinal
        input answer h) (fun e h => h) hhit
    · have hrom := tape_run_rom (leftAt walk) (rightAt walk) _ _ final hfinal
      have hmem := LateProvenance.mem_record_countRecorded _ _
        (final.1, CacheView.cacheOf final.2.1)
        hrom y hfresh hpresent
      exact hnotLate (prfHit_of_mem walk w y
        (by rw [hrecordW]; exact Multiset.mem_add.mpr (Or.inr hmem)) hprf)
  -- the watched value is one
  obtain ⟨answer, hcached, hhits⟩ := (signerRandomised_iff _ _ _ entry.1).mp hsigner
  have hgetFinal : final.2.2.2.2[index]? = some entry := by rw [← hrightW]; exact hget
  unfold value3 watchAt
  rw [hgetFinal, ite_eq_right hnotLate3, mul_one]
  dsimp only
  unfold watchValue
  rw [show CacheView.cacheOf final.2.1 (targetOf walk.1.1.2.1 (keyAt walk) entry.1) =
    some answer from hcached]
  dsimp only
  rw [ite_eq_left]
  refine ⟨hhits, ?_, ?_⟩
  · -- not in the disclosing recording: that would be the signer's coincidence
    intro hleft
    obtain ⟨leftEntry, hleftEntry, hfst⟩ := List.mem_map.mp hleft
    obtain ⟨logged, hlogged, framed, prfAnswer, hframe, hprfCached, hinput⟩ :=
      leftEntry_logged adversary walk hwalk hgood w
        (mem_support_carrierTail_of_tapeRun adversary walk leftTape rightTape w hw) leftEntry
        hleftEntry
    rw [hfst] at hinput
    have htrunc := RandomizerGate.messageInput_eq_randomizerInput_iff _ walk.1.1.2.1
      (keyAt walk).seed (keyAt walk) framed (msgOf entry.1) hinput.symm
    exact hnotLate (Or.inr ⟨logged, hlogged, framed, prfAnswer, hframe, hprfCached, htrunc⟩)
  · -- not in the target recording: its entries are outside the class
    intro hright
    obtain ⟨rightEntry, hrightEntry, hfst⟩ := List.mem_map.mp hright
    exact hinv.2.1 rightEntry hrightEntry (hfst ▸ prfClass_targetOf _ _ entry.1)

/-! ## The thinning, one cell -/

/-- One fresh coin's mass is at most one. -/
theorem unit128_le_one : unit128 ≤ 1 := by
  unfold unit128
  exact ENNReal.div_le_of_le_mul (by simp)

/-- The fused phase's bound is at most one. -/
theorem bound2_le_one (walk : Walk) (index : Nat) (state : FState walk) :
    bound2 walk index state ≤ 1 := by
  unfold bound2; split_ifs
  · exact unit128_le_one
  · exact zero_le

/-- Verification's bound is at most one. -/
theorem bound3_le_one (walk : Walk) (index : Nat)
    (state : SplitTapeState (CountedAt (keyAt walk))) : bound3 walk index state ≤ 1 := by
  unfold bound3; split_ifs
  · exact unit128_le_one
  · exact zero_le

/-- **The phase starts with the invariant**: the walk's cache holds no `PRF_msg` input at the
real seed, and nothing is filed. -/
theorem inv2_start (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : Target.GoodWalk walk) (state : SplitTapeState (CountedAt (keyAt walk)))
    (hcache : CacheView.cacheOf state.1 = walk.2) (hright : state.2.2.2 = []) :
    Inv2 walk ((1 : Multiplicative Tally), ([] : SigningLog), state) := by
  refine ⟨fun x hx => ?_, fun entry hentry => ?_⟩
  · obtain ⟨answer, hcached, -⟩ := (signerRandomised_iff _ _ _ x).mp hx
    have hcached' : walk.2 (targetOf walk.1.1.2.1 (keyAt walk) x) = some answer := by
      rw [← hcache]; exact hcached
    rw [targetOf, RandomiserCharge.walk_cache_prf_fresh hwalk hgood] at hcached'
    exact absurd hcached' (by simp)
  · show ¬ RandomizerGate.PrfClass walk.1.1.2.1 entry.1
    have : entry ∈ state.2.2.2 := hentry
    rw [hright] at this
    exact absurd this (by simp)

open scoped Classical in
/-- **Reaching a target cell and then seeing it fire costs `2 ^ -128` on top of reaching it**,
at the carrier tail's tape run with both blocks fixed. -/
theorem thin1 (adversary : Adversary) (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : Target.GoodWalk walk) (index : Nat) (leftTape rightTape : List HashOutput) :
    Pr{let w ← tapeRun adversary walk leftTape rightTape}[
        index < w.2.2.2.length ∧ Fired walk w index] ≤
      unit128 * Pr{let w ← tapeRun adversary walk leftTape rightTape}[index < w.2.2.2.length] := by
  classical
  set F : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState → ℝ≥0∞ :=
    fun w => if index < w.2.2.2.length ∧ Fired walk w index then 1 else 0 with hFdef
  set G : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState → ℝ≥0∞ :=
    fun w => if index < w.2.2.2.length then unit128 else 0 with hGdef
  rw [← FiredCoverage.tsum_ite_eq_probEvent, ← FiredCoverage.tsum_ite_eq_probEvent,
    ← ENNReal.tsum_mul_left]
  have hG : ∀ w, unit128 * (Pr{let x ← tapeRun adversary walk leftTape rightTape}[x = w] *
      (if index < w.2.2.2.length then 1 else 0)) =
      Pr{let x ← tapeRun adversary walk leftTape rightTape}[x = w] * G w := fun w => by
    rw [hGdef]; dsimp only; split_ifs <;> ring
  rw [tsum_congr hG]
  suffices h : (∑' w, Pr{let x ← tapeRun adversary walk leftTape rightTape}[x = w] * F w) + 0 ≤
      0 + ∑' w, Pr{let x ← tapeRun adversary walk leftTape rightTape}[x = w] * G w by
    rw [add_zero, zero_add] at h
    exact h
  -- key generation: nothing to pay
  refine expect_bind_signed_le (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
    (fun _ => True) (fun _ => 0) (fun _ => 0) (fun _ => zero_le_one)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ => by simp) _ _ trivial _ F G ?_
  rintro ⟨⟨sk, pk⟩, keyState⟩ hkeys
  obtain ⟨hk, hcache1, hright1⟩ := keygen_stage walk hwalk leftTape rightTape _ hkeys
  obtain ⟨hsk, hpk⟩ := Prod.mk.inj hk
  subst hsk
  subst hpk
  dsimp only
  have hstart := inv2_start walk hwalk hgood keyState hcache1 hright1
  have hb0 : bound2 walk index ((1 : Multiplicative Tally), ([] : SigningLog), keyState) = 0 := by
    unfold bound2; rw [ite_eq_right]; change ¬ index < keyState.2.2.2.length; rw [hright1]; simp
  have hv0 : value2 walk index ((1 : Multiplicative Tally), ([] : SigningLog), keyState) = 0 := by
    unfold value2 watchAt
    rw [show keyState.2.2.2[index]? = none by rw [hright1]; simp]
    simp
  -- the phase
  have hphase := expect_bind_signed_le (fusedAt walk) (Inv2 walk) (value2 walk index)
    (bound2 walk index) (bound2_le_one walk index)
    (fun queried state hinv z hz => inv2_step walk hwalk hgood queried state hinv z hz)
    (fun queried state hinv => stage2_step walk hwalk hgood index queried state hinv)
    (adversary.main (keyAt walk)) ((1 : Multiplicative Tally), ([] : SigningLog), keyState) hstart
    (fun middle => (simulateQ (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
        (countRecorded verifierCost
          (Scheme.verify (keyAt walk) middle.1.message middle.1.signature))).run
          middle.2.2.2 >>= fun final =>
        (pure (CarrierCoverage.tailValue (skAt walk, keyAt walk) middle.1 middle.2.1
          middle.2.2.1 final.1 final.2.1, forgetViewTape final.2) :
          ProbComp (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)))
    F G ?_
  · rw [hb0, hv0] at hphase
    exact hphase
  intro middle hmiddle
  have hinv2 : Inv2 walk middle.2 := run_invariant (fusedAt walk) (Inv2 walk)
    (fun queried state hinv z hz => inv2_step walk hwalk hgood queried state hinv z hz)
    _ _ hstart middle hmiddle
  have hinv3 : Inv3 walk (Late2 walk middle.2) (cacheF walk middle.2) middle.2.2.2 :=
    ⟨fun x hx => (hinv2.1 x hx).imp id Or.inl, hinv2.2, fun _ _ h => h⟩
  -- verification
  have hverify := expect_bind_signed_le (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
    (Inv3 walk (Late2 walk middle.2) (cacheF walk middle.2))
    (value3 walk index (Late2 walk middle.2) (cacheF walk middle.2)) (bound3 walk index)
    (bound3_le_one walk index)
    (fun queried state hinv z hz => inv3_step walk _ _ queried state hinv z hz)
    (fun queried state hinv => stage3_step walk index _ _ queried state hinv)
    (countRecorded verifierCost (Scheme.verify (keyAt walk) middle.1.message middle.1.signature))
    middle.2.2.2 hinv3
    (fun final => (pure (CarrierCoverage.tailValue (skAt walk, keyAt walk) middle.1 middle.2.1
      middle.2.2.1 final.1 final.2.1, forgetViewTape final.2) :
      ProbComp (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)))
    F G ?_
  · refine le_trans (le_of_eq_of_le (by rfl) hverify) (add_le_add ?_ le_rfl)
    unfold value3 value2
    refine mul_le_mul' le_rfl ?_
    by_cases hlate : Late2 walk middle.2
    · rw [ite_eq_left (show Late3 walk (Late2 walk middle.2) (cacheF walk middle.2)
        middle.2.2.2 from Or.inl hlate), ite_eq_left hlate]
    · rw [ite_eq_right hlate]; split_ifs <;> simp
  intro final hfinal
  have hinvFinal := run_invariant (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
    (Inv3 walk (Late2 walk middle.2) (cacheF walk middle.2))
    (fun queried state hinv z hz => inv3_step walk _ _ queried state hinv z hz)
    _ _ hinv3 final hfinal
  refine pure_signed_le _ final.2 _ _ F G (add_le_add ?_ (le_of_eq rfl))
  refine end_condition adversary walk hwalk hgood index leftTape rightTape middle final hfinal
    hinvFinal ?_
  unfold tapeRun threeStageTapeRun
  rw [mem_support_bind_iff]
  refine ⟨((skAt walk, keyAt walk), keyState), hkeys, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨middle, hmiddle, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨final, hfinal, by simp⟩

/-! ## Two cells

The pair bound watches two cells' `PRF_msg` inputs at once. Their product is a supermartingale
because one query moves at most one of them — or, when the two inputs are the same, a fresh answer
cannot make both cells fire, the cells being distinct inputs. So the run has to keep its target
entries distinct, which it does because an entry is filed only while uncached. -/

/-- **The target recording's inputs are cached and distinct.** -/
@[expose]
def RightDistinct (walk : Walk) (state : SplitTapeState (CountedAt (keyAt walk))) : Prop :=
  (∀ entry ∈ state.2.2.2, CacheView.cacheOf state.1 entry.1 ≠ none) ∧
    (state.2.2.2.map Prod.fst).Nodup

/-- **One recorder step keeps the target entries cached and distinct.** -/
theorem rightDistinct_tapeStep (walk : Walk) (queried : OracleWorld.Domain)
    (state : SplitTapeState (CountedAt (keyAt walk))) (hdistinct : RightDistinct walk state)
    (step : OracleWorld.Range queried × SplitTapeState (CountedAt (keyAt walk)))
    (hstep : step ∈ support (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
      queried).run state)) :
    RightDistinct walk step.2 := by
  have hpersist := tapeStep_persists walk queried state step hstep
  have hkeepCached : ∀ entry ∈ state.2.2.2, CacheView.cacheOf step.2.1 entry.1 ≠ none :=
    fun entry hentry hnone => by
      obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp (hdistinct.1 entry hentry)
      rw [hpersist _ value hvalue] at hnone
      exact absurd hnone (by simp)
  rcases queried with coin | input
  · rw [tapeStep_inl _ _ coin state step hstep]; exact hdistinct
  · rcases tapeStep_inr_cases (leftAt walk) (rightAt walk) input state step hstep with
      ⟨-, hst⟩ | ⟨-, -, hst⟩ | ⟨hfresh, -, -, hst⟩ | ⟨-, -, -, hst⟩
    · refine ⟨fun entry hentry => hkeepCached entry (by rw [hst] at hentry; exact hentry), ?_⟩
      rw [hst]; exact hdistinct.2
    · refine ⟨fun entry hentry => hkeepCached entry (by rw [hst] at hentry; exact hentry), ?_⟩
      rw [hst]; exact hdistinct.2
    · have hcachedInput := tapeStep_cache_self _ _ input state step hstep
      refine ⟨fun entry hentry => ?_, ?_⟩
      · rw [hst] at hentry
        rcases List.mem_append.mp hentry with hold | hnew
        · exact hkeepCached entry hold
        · rw [List.mem_singleton] at hnew
          subst hnew
          rw [hcachedInput]; simp
      · rw [hst, List.map_append, List.nodup_append]
        refine ⟨hdistinct.2, List.nodup_singleton _, ?_⟩
        intro a ha b hb hab
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        subst hab
        obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp ha
        exact hdistinct.1 entry hentry
          (by rw [← CacheView.cache_onQuery state.1 entry.1]; exact hfresh)
    · refine ⟨fun entry hentry => hkeepCached entry (by rw [hst] at hentry; exact hentry), ?_⟩
      rw [hst]; exact hdistinct.2

/-- **One recorder step appends at most one target entry**, and only at an input the noticed
carrier did not hold and the target test kept. -/
theorem tapeStep_right_shape (walk : Walk) (queried : OracleWorld.Domain)
    (state : SplitTapeState (CountedAt (keyAt walk)))
    (step : OracleWorld.Range queried × SplitTapeState (CountedAt (keyAt walk)))
    (hstep : step ∈ support (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
      queried).run state)) :
    step.2.2.2.2 = state.2.2.2 ∨
      ∃ (input : Bytes) (answer : HashOutput), queried = Sum.inr input ∧
        step.2.2.2.2 = state.2.2.2 ++ [(input, answer)] ∧
        CacheView.cacheOf state.1 input = none ∧
        ¬ RandomizerGate.PrfClass walk.1.1.2.1 input ∧
        CacheView.cacheOf step.2.1 (targetOf walk.1.1.2.1 (keyAt walk) input) =
          CacheView.cacheOf state.1 (targetOf walk.1.1.2.1 (keyAt walk) input) := by
  rcases queried with coin | input
  · left; rw [tapeStep_inl _ _ coin state step hstep]
  · rcases tapeStep_inr_cases (leftAt walk) (rightAt walk) input state step hstep with
      ⟨-, hst⟩ | ⟨-, -, hst⟩ | ⟨hfresh, -, hkeep, hst⟩ | ⟨-, -, -, hst⟩
    · left; rw [hst]
    · left; rw [hst]
    · right
      have hfresh' : CacheView.cacheOf state.1 input = none := by
        rw [← CacheView.cache_onQuery state.1 input]; exact hfresh
      have hne : targetOf walk.1.1.2.1 (keyAt walk) input ≠ input := fun h =>
        hkeep.2 (h ▸ prfClass_targetOf _ _ input)
      exact ⟨input, step.1, rfl, by rw [hst], hfresh', hkeep.2,
        tapeStep_cache_ne _ _ input _ hne state step hstep⟩
    · left; rw [hst]

/-- **One fused step appends at most one target entry**, the adversary's own query, and keeps the
target entries cached and distinct. -/
theorem fused_right_shape (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : Target.GoodWalk walk) (queried : (OracleWorld + SigningSpec).Domain)
    (state : FState walk) (hdistinct : RightDistinct walk state.2.2)
    (z : (OracleWorld + SigningSpec).Range queried × FState walk)
    (hz : z ∈ support (((fusedAt walk) queried).run state)) :
    RightDistinct walk z.2.2.2 ∧
      (z.2.2.2.2.2.2 = state.2.2.2.2.2 ∨
        ∃ (input : Bytes) (answer : HashOutput),
          z.2.2.2.2.2.2 = state.2.2.2.2.2 ++ [(input, answer)] ∧
          CacheView.cacheOf state.2.2.1 input = none ∧
          ¬ RandomizerGate.PrfClass walk.1.1.2.1 input ∧
          CacheView.cacheOf z.2.2.2.1 (targetOf walk.1.1.2.1 (keyAt walk) input) =
            CacheView.cacheOf state.2.2.1 (targetOf walk.1.1.2.1 (keyAt walk) input) ∧
          recordF walk z.2 = recordF walk state + {input}) := by
  rcases queried with world | request
  · obtain ⟨step, hstep, hz2⟩ := adversary_step_shape walk world state z hz
    have hcarrier : z.2.2.2 = step.2 := by rw [hz2]
    have hdist := rightDistinct_tapeStep walk world state.2.2 hdistinct step hstep
    rw [← hcarrier] at hdist
    refine ⟨hdist, ?_⟩
    rcases tapeStep_right_shape walk world state.2.2 step hstep with hsame |
      ⟨input, answer, rfl, happend, hfresh, hnotPrf, htarget⟩
    · left; rw [hcarrier]; exact hsame
    · right
      have happend' : z.2.2.2.2.2.2 = state.2.2.2.2.2 ++ [(input, answer)] := by
        rw [hcarrier]; exact happend
      have htarget' : CacheView.cacheOf z.2.2.2.1 (targetOf walk.1.1.2.1 (keyAt walk) input) =
          CacheView.cacheOf state.2.2.1 (targetOf walk.1.1.2.1 (keyAt walk) input) := by
        rw [hcarrier]; exact htarget
      refine ⟨input, answer, happend', hfresh, hnotPrf, htarget', ?_⟩
      rw [hz2]
      rfl
  · have hright := signing_step_right walk hwalk hgood request state z hz
    obtain ⟨answer, inner, hinner, hz2⟩ := signing_step_shape walk request state z hz
    obtain ⟨-, -, hcache, -⟩ := fused_step_grows walk (Sum.inr request) state z hz
    refine ⟨⟨fun entry hentry hnone => ?_, ?_⟩, Or.inl hright⟩
    · have hentry' : entry ∈ state.2.2.2.2.2 := by rw [← hright]; exact hentry
      obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp (hdistinct.1 entry hentry')
      have := hcache entry.1 value hvalue
      simp only [cacheF] at this
      rw [this] at hnone
      exact absurd hnone (by simp)
    · show (z.2.2.2.2.2.2.map Prod.fst).Nodup
      rw [hright]
      exact hdistinct.2

open scoped Classical in
/-- **A freshly filed cell's watched value**, read off the cache its `PRF_msg` input had before. -/
theorem watch_after_filing (walk : Walk) (state : SplitTapeState (CountedAt (keyAt walk)))
    (cache : QueryCache HashSpec) (input : Bytes)
    (hcache : CacheView.cacheOf state.1 (targetOf walk.1.1.2.1 (keyAt walk) input) =
      cache (targetOf walk.1.1.2.1 (keyAt walk) input)) :
    watchValue (targetOf walk.1.1.2.1 (keyAt walk) input) (HitsOf (keyAt walk) input) state ≤
        unit128 ∨
      CacheAvailability.SignerRandomised walk.1.1.2.1 (keyAt walk) cache input := by
  classical
  cases hcached : cache (targetOf walk.1.1.2.1 (keyAt walk) input) with
  | none =>
    refine Or.inl ?_
    unfold watchValue
    rw [hcache, hcached]
    exact prob_hitsOf_le (keyAt walk) input
  | some answer =>
    by_cases hhits : HitsOf (keyAt walk) input answer
    · exact Or.inr ((signerRandomised_iff _ _ _ input).mpr ⟨answer, hcached, hhits⟩)
    · refine Or.inl (le_trans (watchValue_le_of_cache _ _ state answer
        (by rw [hcache, hcached])) ?_)
      rw [ite_eq_right hhits]
      exact zero_le

/-- **A fused step that reaches a cell files it, at a watched value of one coin — or `late`.** -/
theorem fused_filing (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : Target.GoodWalk walk) (queried : (OracleWorld + SigningSpec).Domain)
    (state : FState walk) (hinv : Inv2 walk state) (hdistinct : RightDistinct walk state.2.2)
    (index : Nat) (hnot : ¬ index < state.2.2.2.2.2.length)
    (z : (OracleWorld + SigningSpec).Range queried × FState walk)
    (hz : z ∈ support (((fusedAt walk) queried).run state))
    (hreach : index < z.2.2.2.2.2.2.length) :
    index = state.2.2.2.2.2.length ∧ ∃ entry, z.2.2.2.2.2.2[index]? = some entry ∧
      (watchValue (targetOf walk.1.1.2.1 (keyAt walk) entry.1) (HitsOf (keyAt walk) entry.1)
          z.2.2.2 ≤ unit128 ∨ Late2 walk z.2) := by
  rcases (fused_right_shape walk hwalk hgood queried state hdistinct z hz).2 with hsame |
    ⟨input, answer, happend, hfresh, hnotPrf, htarget, -⟩
  · rw [hsame] at hreach; exact absurd hreach hnot
  · have hindex : index = state.2.2.2.2.2.length := by
      rw [happend] at hreach
      simp only [List.length_append, List.length_singleton] at hreach
      omega
    refine ⟨hindex, (input, answer), by rw [happend, hindex]; simp, ?_⟩
    rcases watch_after_filing walk z.2.2.2 (CacheView.cacheOf state.2.2.1) input htarget with
      hle | hsigner
    · exact Or.inl hle
    · rcases hinv.1 input hsigner with hpresent | hlate
      · exact absurd hfresh hpresent
      · exact Or.inr (late2_step walk queried state z hz hlate)

/-- **And the same at a recorder step of verification.** -/
theorem tape_filing (walk : Walk) (phaseLate : Prop) (phaseCache : QueryCache HashSpec)
    (queried : OracleWorld.Domain) (state : SplitTapeState (CountedAt (keyAt walk)))
    (hinv : Inv3 walk phaseLate phaseCache state) (index : Nat)
    (hnot : ¬ index < state.2.2.2.length)
    (z : OracleWorld.Range queried × SplitTapeState (CountedAt (keyAt walk)))
    (hz : z ∈ support (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk)) queried).run
      state))
    (hreach : index < z.2.2.2.2.length) :
    index = state.2.2.2.length ∧ ∃ entry, z.2.2.2.2[index]? = some entry ∧
      (watchValue (targetOf walk.1.1.2.1 (keyAt walk) entry.1) (HitsOf (keyAt walk) entry.1)
          z.2 ≤ unit128 ∨ Late3 walk phaseLate phaseCache z.2) := by
  rcases tapeStep_right_shape walk queried state z hz with hsame |
    ⟨input, answer, -, happend, hfresh, -, htarget⟩
  · rw [hsame] at hreach; exact absurd hreach hnot
  · have hindex : index = state.2.2.2.length := by
      rw [happend] at hreach
      simp only [List.length_append, List.length_singleton] at hreach
      omega
    refine ⟨hindex, (input, answer), by rw [happend, hindex]; simp, ?_⟩
    rcases watch_after_filing walk z.2 (CacheView.cacheOf state.1) input htarget with
      hle | hsigner
    · exact Or.inl hle
    · rcases hinv.1 input hsigner with hpresent | hlate
      · exact absurd hfresh hpresent
      · exact Or.inr (late3_step walk phaseLate phaseCache queried state z hz hlate)

/-! ### The pair's value -/

/-- Two distinct target entries cannot both fire on one answer to a shared `PRF_msg` input. -/
theorem hits_disjoint (walk : Walk) (first second : Bytes) (hne : first ≠ second) :
    targetOf walk.1.1.2.1 (keyAt walk) first = targetOf walk.1.1.2.1 (keyAt walk) second →
      ∀ answer, HitsOf (keyAt walk) first answer → HitsOf (keyAt walk) second answer → False := by
  intro htarget answer hfirst hsecond
  have hmsg : msgOf first = msgOf second := (Hashing.randomizerInput_injective htarget).2.2
  rw [HitsOf, hmsg] at hfirst
  exact hne (hfirst.symm.trans hsecond)

/-- Distinct positions of a distinct recording hold distinct inputs. -/
theorem fst_ne_of_nodup (record : Record) (hnodup : (record.map Prod.fst).Nodup)
    {first second : Nat} (hne : first ≠ second) {e1 e2 : Bytes × HashOutput}
    (h1 : record[first]? = some e1) (h2 : record[second]? = some e2) : e1.1 ≠ e2.1 := by
  intro heq
  obtain ⟨hlt1, hget1⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨hlt2, hget2⟩ := List.getElem?_eq_some_iff.mp h2
  have hm1 : (record.map Prod.fst)[first]'(by simpa using hlt1) = e1.1 := by simp [hget1]
  have hm2 : (record.map Prod.fst)[second]'(by simpa using hlt2) = e2.1 := by simp [hget2]
  exact hne ((hnodup.getElem_inj_iff).mp (hm1.trans (heq.trans hm2.symm)))

open scoped Classical in
/-- The second cell's factor: its watched value once filed, one coin's mass before. -/
@[expose] noncomputable def secondFactor (walk : Walk) (second : Nat)
    (state : SplitTapeState (CountedAt (keyAt walk))) : ℝ≥0∞ :=
  match state.2.2.2[second]? with
  | some entry => watchValue (targetOf walk.1.1.2.1 (keyAt walk) entry.1)
      (HitsOf (keyAt walk) entry.1) state
  | none => unit128

open scoped Classical in
/-- **The pair's watched value**: zero until the first cell is filed. -/
@[expose] noncomputable def pairAt (walk : Walk) (first second : Nat)
    (state : SplitTapeState (CountedAt (keyAt walk))) : ℝ≥0∞ :=
  match state.2.2.2[first]? with
  | some entry => watchValue (targetOf walk.1.1.2.1 (keyAt walk) entry.1)
      (HitsOf (keyAt walk) entry.1) state * secondFactor walk second state
  | none => 0

open scoped Classical in
/-- **The pair value of the fused phase**: the pair's watched value, zeroed once `late` has
begun. -/
@[expose]
noncomputable def value2P (walk : Walk) (first second : Nat) (state : FState walk) : ℝ≥0∞ :=
  pairAt walk first second state.2.2 * (if Late2 walk state then 0 else 1)

open scoped Classical in
/-- **The pair bound of the fused phase**: two coins' mass once the first cell is reached. -/
@[expose] noncomputable def bound2P (walk : Walk) (first : Nat) (state : FState walk) : ℝ≥0∞ :=
  if first < state.2.2.2.2.2.length then unit128 * unit128 else 0

/-- The fused phase's pair invariant. -/
@[expose] def Inv2P (walk : Walk) (state : FState walk) : Prop :=
  Inv2 walk state ∧ RightDistinct walk state.2.2

/-- **The fused phase keeps the pair invariant.** -/
theorem inv2P_step (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : Target.GoodWalk walk) (queried : (OracleWorld + SigningSpec).Domain)
    (state : FState walk) (hinv : Inv2P walk state)
    (z : (OracleWorld + SigningSpec).Range queried × FState walk)
    (hz : z ∈ support (((fusedAt walk) queried).run state)) : Inv2P walk z.2 :=
  ⟨inv2_step walk hwalk hgood queried state hinv.1 z hz,
    (fused_right_shape walk hwalk hgood queried state hinv.2 z hz).1⟩

/-- Two fresh coins' mass is at most one. -/
theorem unit128_sq_le_one : unit128 * unit128 ≤ 1 :=
  le_trans (mul_le_mul' unit128_le_one unit128_le_one) (by simp)

/-- The fused phase's pair bound is at most one. -/
theorem bound2P_le_one (walk : Walk) (first : Nat) (state : FState walk) :
    bound2P walk first state ≤ 1 := by
  unfold bound2P; split_ifs
  · exact unit128_sq_le_one
  · exact zero_le

/-- An entry already filed stays at its position. -/
theorem getElem?_of_prefix {record longer : Record} (hprefix : record <+: longer) {index : Nat}
    {entry : Bytes × HashOutput} (hget : record[index]? = some entry) :
    longer[index]? = some entry := by
  obtain ⟨tail, htail⟩ := hprefix
  rw [← htail]
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp hget).1).trans hget

/-- A factor of the form `if late then 0 else 1` only falls as `late` begins. -/
theorem ite_late_le {p q : Prop} [Decidable p] [Decidable q] (h : p → q) :
    (if q then (0 : ℝ≥0∞) else 1) ≤ if p then 0 else 1 := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left (h hp)]
  · rw [ite_eq_right hp]; split_ifs <;> simp

/-- A factor of the form `if late then 0 else 1` is at most one. -/
theorem ite_late_le_one {p : Prop} [Decidable p] : (if p then (0 : ℝ≥0∞) else 1) ≤ 1 := by
  split_ifs <;> simp

open scoped Classical in
/-- **The fused phase pays for the pair's watched value as it is earned.** -/
theorem stage2P_step (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : Target.GoodWalk walk) (first second : Nat) (hlt : first < second)
    (queried : (OracleWorld + SigningSpec).Domain) (state : FState walk)
    (hinv : Inv2P walk state) :
    (∑' z, Pr{let x ← ((fusedAt walk) queried).run state}[x = z] * value2P walk first second z.2) +
        bound2P walk first state ≤
      value2P walk first second state +
        ∑' z, Pr{let x ← ((fusedAt walk) queried).run state}[x = z] * bound2P walk first z.2 := by
  classical
  set step := ((fusedAt walk) queried).run state with hstepDef
  have hprefix : ∀ z ∈ support step, state.2.2.2.2.2 <+: z.2.2.2.2.2.2 :=
    fun z hz => (fused_step_grows walk queried state z hz).2.2.2
  have hlen : ∀ z ∈ support step, z.2.2.2.2.2.2.length ≤ state.2.2.2.2.2.length + 1 := by
    intro z hz
    rcases (fused_right_shape walk hwalk hgood queried state hinv.2 z hz).2 with hsame |
      ⟨input, answer, happend, -⟩
    · rw [hsame]; omega
    · rw [happend]; simp
  by_cases hA : first < state.2.2.2.2.2.length
  · set e1 := state.2.2.2.2.2[first] with he1
    have hget1 : state.2.2.2.2.2[first]? = some e1 := List.getElem?_eq_getElem hA
    have hz1 : ∀ z ∈ support step, z.2.2.2.2.2.2[first]? = some e1 :=
      fun z hz => getElem?_of_prefix (hprefix z hz) hget1
    set W1 := watchValue (σ := CountedAt (keyAt walk)) (targetOf walk.1.1.2.1 (keyAt walk) e1.1)
      (HitsOf (keyAt walk) e1.1)
    have hW1 : ∀ s : SplitTapeState (CountedAt (keyAt walk)),
        ∑' z, Pr{let x ← (fusedAt walk queried).run state}[x = z] * W1 z.2.2.2 ≤ W1 state.2.2 :=
      fun _ => fused_step_le (leftAt walk) (rightAt walk) (innerAt (skAt walk, keyAt walk))
        ServedAgreement.startServingOn ServedAgreement.stopServingOn W1
        (fun queried state => watchValue_step_le _ _ _ _ queried state)
        (fun request state => watchValue_onCarrierTape _ _ _
          (cacheOf_startServingOn (keyAt walk) request) state)
        (fun state => watchValue_onCarrierTape _ _ _ (cacheOf_stopServingOn (keyAt walk)) state)
        queried state
    have hboundZ : ∀ z ∈ support step, bound2P walk first z.2 = unit128 * unit128 := by
      intro z hz
      unfold bound2P
      rw [ite_eq_left (List.getElem?_eq_some_iff.mp (hz1 z hz)).1]
    have hboundEnd :
        ∑' z, Pr{let x ← step}[x = z] * bound2P walk first z.2 = unit128 * unit128 := by
      rw [show (∑' z, Pr{let x ← step}[x = z] * bound2P walk first z.2) =
          ∑' z, Pr{let x ← step}[x = z] * (unit128 * unit128) from tsum_congr fun z => by
            by_cases hz : z ∈ support step
            · rw [hboundZ z hz]
            · rw [(prEvent_eq_zero_of_not_mem_support _) hz, zero_mul, zero_mul]]
      exact tsum_prEvent_mul_const step _
    have hboundStart : bound2P walk first state = unit128 * unit128 := by
      unfold bound2P; rw [ite_eq_left hA]
    rw [hboundEnd, hboundStart]
    refine add_le_add ?_ le_rfl
    by_cases hB : second < state.2.2.2.2.2.length
    · set e2 := state.2.2.2.2.2[second] with he2
      have hget2 : state.2.2.2.2.2[second]? = some e2 := List.getElem?_eq_getElem hB
      have hz2 : ∀ z ∈ support step, z.2.2.2.2.2.2[second]? = some e2 :=
        fun z hz => getElem?_of_prefix (hprefix z hz) hget2
      set W2 := watchValue (σ := CountedAt (keyAt walk)) (targetOf walk.1.1.2.1 (keyAt walk) e2.1)
        (HitsOf (keyAt walk) e2.1)
      have hdisjoint := hits_disjoint walk e1.1 e2.1
        (fst_ne_of_nodup _ hinv.2.2 (Nat.ne_of_lt hlt) hget1 hget2)
      have hstart : value2P walk first second state =
          (W1 state.2.2 * W2 state.2.2) * (if Late2 walk state then 0 else 1) := by
        unfold value2P pairAt secondFactor
        rw [hget1, hget2]
      rw [hstart]
      calc ∑' z, Pr{let x ← step}[x = z] * value2P walk first second z.2
          ≤ ∑' z, Pr{let x ← step}[x = z] *
              ((W1 z.2.2.2 * W2 z.2.2.2) * (if Late2 walk state then 0 else 1)) := by
            refine tsum_le_of_support step _ _ fun z hz => ?_
            unfold value2P pairAt secondFactor
            rw [hz1 z hz, hz2 z hz]
            exact mul_le_mul' le_rfl (ite_late_le (late2_step walk queried state z hz))
        _ = (∑' z, Pr{let x ← step}[x = z] * (W1 z.2.2.2 * W2 z.2.2.2)) *
              (if Late2 walk state then 0 else 1) := by
            rw [← ENNReal.tsum_mul_right]
            exact tsum_congr fun z => by ring
        _ ≤ (W1 state.2.2 * W2 state.2.2) * (if Late2 walk state then 0 else 1) := by
            refine mul_le_mul' ?_ le_rfl
            exact fused_step_le (leftAt walk) (rightAt walk) (innerAt (skAt walk, keyAt walk))
              ServedAgreement.startServingOn ServedAgreement.stopServingOn
              (fun s => W1 s * W2 s)
              (fun queried state => watchPair_step_le _ _ _ _ _ _ hdisjoint queried state)
              (fun request state => watchPair_onCarrierTape _ _ _ _ _
                (cacheOf_startServingOn (keyAt walk) request) state)
              (fun state => watchPair_onCarrierTape _ _ _ _ _
                (cacheOf_stopServingOn (keyAt walk)) state)
              queried state
    · have hgetNone : state.2.2.2.2.2[second]? = none :=
        List.getElem?_eq_none (Nat.le_of_not_lt hB)
      have hstart : value2P walk first second state =
          (W1 state.2.2 * unit128) * (if Late2 walk state then 0 else 1) := by
        unfold value2P pairAt secondFactor
        rw [hget1, hgetNone]
      rw [hstart]
      calc ∑' z, Pr{let x ← step}[x = z] * value2P walk first second z.2
          ≤ ∑' z, Pr{let x ← step}[x = z] *
              ((W1 z.2.2.2 * unit128) * (if Late2 walk state then 0 else 1)) := by
            refine tsum_le_of_support step _ _ fun z hz => ?_
            unfold value2P pairAt
            rw [hz1 z hz]
            dsimp only
            by_cases hBz : second < z.2.2.2.2.2.2.length
            · obtain ⟨-, e2, hgetZ, hcase⟩ := fused_filing walk hwalk hgood queried state hinv.1
                hinv.2 second hB z hz hBz
              unfold secondFactor
              rw [hgetZ]
              dsimp only
              rcases hcase with hle | hlate
              · exact mul_le_mul' (mul_le_mul' le_rfl hle)
                  (ite_late_le (late2_step walk queried state z hz))
              · rw [ite_eq_left hlate, mul_zero]; exact zero_le
            · unfold secondFactor
              rw [List.getElem?_eq_none (Nat.le_of_not_lt hBz)]
              exact mul_le_mul' le_rfl (ite_late_le (late2_step walk queried state z hz))
        _ = (∑' z, Pr{let x ← step}[x = z] * W1 z.2.2.2) * unit128 *
              (if Late2 walk state then 0 else 1) := by
            rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
            exact tsum_congr fun z => by ring
        _ ≤ (W1 state.2.2 * unit128) * (if Late2 walk state then 0 else 1) :=
            mul_le_mul' (mul_le_mul' (hW1 state.2.2) le_rfl) le_rfl
  · have hgetNone : state.2.2.2.2.2[first]? = none :=
      List.getElem?_eq_none (Nat.le_of_not_lt hA)
    have hvalueStart : value2P walk first second state = 0 := by
      unfold value2P pairAt; rw [hgetNone]; simp
    have hboundStart : bound2P walk first state = 0 := by
      unfold bound2P; rw [ite_eq_right hA]
    rw [hvalueStart, hboundStart, add_zero, zero_add]
    refine tsum_le_of_support step _ _ fun z hz => ?_
    by_cases hAz : first < z.2.2.2.2.2.2.length
    swap
    · unfold value2P pairAt
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hAz)]
      simp
    obtain ⟨hindex, e1, hgetZ, hcase⟩ := fused_filing walk hwalk hgood queried state hinv.1
      hinv.2 first hA z hz hAz
    have hBz : ¬ second < z.2.2.2.2.2.2.length := by
      have := hlen z hz; omega
    unfold bound2P
    rw [ite_eq_left hAz]
    unfold value2P pairAt secondFactor
    rw [hgetZ, List.getElem?_eq_none (Nat.le_of_not_lt hBz)]
    dsimp only
    rcases hcase with hle | hlate
    · calc watchValue (targetOf walk.1.1.2.1 (keyAt walk) e1.1) (HitsOf (keyAt walk) e1.1)
            z.2.2.2 * unit128 * (if Late2 walk z.2 then 0 else 1)
          ≤ unit128 * unit128 * 1 := mul_le_mul' (mul_le_mul' hle le_rfl) ite_late_le_one
        _ = unit128 * unit128 := mul_one _
    · rw [ite_eq_left hlate, mul_zero]; exact zero_le

open scoped Classical in
/-- **The pair value of verification**: the pair's watched value, zeroed once `late` as far as
verification has got has begun. -/
@[expose] noncomputable def value3P (walk : Walk) (first second : Nat) (phaseLate : Prop)
    (phaseCache : QueryCache HashSpec) (state : SplitTapeState (CountedAt (keyAt walk))) :
    ℝ≥0∞ :=
  pairAt walk first second state * (if Late3 walk phaseLate phaseCache state then 0 else 1)

open scoped Classical in
/-- **The pair bound of verification**: two coins' mass once the first cell is reached. -/
@[expose] noncomputable def bound3P (walk : Walk) (first : Nat)
    (state : SplitTapeState (CountedAt (keyAt walk))) : ℝ≥0∞ :=
  if first < state.2.2.2.length then unit128 * unit128 else 0

/-- Verification's pair invariant. -/
@[expose] def Inv3P (walk : Walk) (phaseLate : Prop) (phaseCache : QueryCache HashSpec)
    (state : SplitTapeState (CountedAt (keyAt walk))) : Prop :=
  Inv3 walk phaseLate phaseCache state ∧ RightDistinct walk state

/-- **Verification keeps the pair invariant.** -/
theorem inv3P_step (walk : Walk) (phaseLate : Prop) (phaseCache : QueryCache HashSpec)
    (queried : OracleWorld.Domain) (state : SplitTapeState (CountedAt (keyAt walk)))
    (hinv : Inv3P walk phaseLate phaseCache state)
    (z : OracleWorld.Range queried × SplitTapeState (CountedAt (keyAt walk)))
    (hz : z ∈ support (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk)) queried).run
      state)) : Inv3P walk phaseLate phaseCache z.2 :=
  ⟨inv3_step walk phaseLate phaseCache queried state hinv.1 z hz,
    rightDistinct_tapeStep walk queried state hinv.2 z hz⟩

/-- Verification's pair bound is at most one. -/
theorem bound3P_le_one (walk : Walk) (first : Nat)
    (state : SplitTapeState (CountedAt (keyAt walk))) : bound3P walk first state ≤ 1 := by
  unfold bound3P; split_ifs
  · exact unit128_sq_le_one
  · exact zero_le

open scoped Classical in
/-- **Verification pays for the pair's watched value as it is earned.** -/
theorem stage3P_step (walk : Walk) (first second : Nat) (hlt : first < second)
    (phaseLate : Prop) (phaseCache : QueryCache HashSpec) (queried : OracleWorld.Domain)
    (state : SplitTapeState (CountedAt (keyAt walk)))
    (hinv : Inv3P walk phaseLate phaseCache state) :
    (∑' z, Pr{let x ← (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk)) queried).run
          state)}[x = z] *
        value3P walk first second phaseLate phaseCache z.2) + bound3P walk first state ≤
      value3P walk first second phaseLate phaseCache state +
        ∑' z, Pr{let x ← (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk)) queried).run
          state)}[x = z] * bound3P walk first z.2 := by
  classical
  set step := ((noticingSplitTapeRecorder (leftAt walk) (rightAt walk)) queried).run state
    with hstepDef
  have hprefix : ∀ z ∈ support step, state.2.2.2 <+: z.2.2.2.2 :=
    fun z hz => noticingSplitTapeRecorder_step (leftAt walk) (rightAt walk) queried state z hz
  have hlen : ∀ z ∈ support step, z.2.2.2.2.length ≤ state.2.2.2.length + 1 := by
    intro z hz
    rcases tapeStep_right_shape walk queried state z hz with hsame | ⟨input, answer, -, happend, -⟩
    · rw [hsame]; omega
    · rw [happend]; simp
  have hlate := late3_step walk phaseLate phaseCache queried state
  by_cases hA : first < state.2.2.2.length
  · set e1 := state.2.2.2[first] with he1
    have hget1 : state.2.2.2[first]? = some e1 := List.getElem?_eq_getElem hA
    have hz1 : ∀ z ∈ support step, z.2.2.2.2[first]? = some e1 :=
      fun z hz => getElem?_of_prefix (hprefix z hz) hget1
    set W1 := watchValue (σ := CountedAt (keyAt walk)) (targetOf walk.1.1.2.1 (keyAt walk) e1.1)
      (HitsOf (keyAt walk) e1.1)
    have hboundZ : ∀ z ∈ support step, bound3P walk first z.2 = unit128 * unit128 := by
      intro z hz
      unfold bound3P
      rw [ite_eq_left (List.getElem?_eq_some_iff.mp (hz1 z hz)).1]
    have hboundEnd :
        ∑' z, Pr{let x ← step}[x = z] * bound3P walk first z.2 = unit128 * unit128 := by
      rw [show (∑' z, Pr{let x ← step}[x = z] * bound3P walk first z.2) =
          ∑' z, Pr{let x ← step}[x = z] * (unit128 * unit128) from tsum_congr fun z => by
            by_cases hz : z ∈ support step
            · rw [hboundZ z hz]
            · rw [(prEvent_eq_zero_of_not_mem_support _) hz, zero_mul, zero_mul]]
      exact tsum_prEvent_mul_const step _
    have hboundStart : bound3P walk first state = unit128 * unit128 := by
      unfold bound3P; rw [ite_eq_left hA]
    rw [hboundEnd, hboundStart]
    refine add_le_add ?_ le_rfl
    by_cases hB : second < state.2.2.2.length
    · set e2 := state.2.2.2[second] with he2
      have hget2 : state.2.2.2[second]? = some e2 := List.getElem?_eq_getElem hB
      have hz2 : ∀ z ∈ support step, z.2.2.2.2[second]? = some e2 :=
        fun z hz => getElem?_of_prefix (hprefix z hz) hget2
      set W2 := watchValue (σ := CountedAt (keyAt walk)) (targetOf walk.1.1.2.1 (keyAt walk) e2.1)
        (HitsOf (keyAt walk) e2.1)
      have hdisjoint := hits_disjoint walk e1.1 e2.1
        (fst_ne_of_nodup _ hinv.2.2 (Nat.ne_of_lt hlt) hget1 hget2)
      have hstart : value3P walk first second phaseLate phaseCache state =
          (W1 state * W2 state) * (if Late3 walk phaseLate phaseCache state then 0 else 1) := by
        unfold value3P pairAt secondFactor
        rw [hget1, hget2]
      rw [hstart]
      calc ∑' z, Pr{let x ← step}[x = z] * value3P walk first second phaseLate phaseCache z.2
          ≤ ∑' z, Pr{let x ← step}[x = z] *
              ((W1 z.2 * W2 z.2) * (if Late3 walk phaseLate phaseCache state then 0 else 1)) := by
            refine tsum_le_of_support step _ _ fun z hz => ?_
            unfold value3P pairAt secondFactor
            rw [hz1 z hz, hz2 z hz]
            exact mul_le_mul' le_rfl (ite_late_le (hlate z hz))
        _ = (∑' z, Pr{let x ← step}[x = z] * (W1 z.2 * W2 z.2)) *
              (if Late3 walk phaseLate phaseCache state then 0 else 1) := by
            rw [← ENNReal.tsum_mul_right]
            exact tsum_congr fun z => by ring
        _ ≤ (W1 state * W2 state) * (if Late3 walk phaseLate phaseCache state then 0 else 1) :=
            mul_le_mul' (watchPair_step_le _ _ _ _ _ _ hdisjoint queried state) le_rfl
    · have hgetNone : state.2.2.2[second]? = none :=
        List.getElem?_eq_none (Nat.le_of_not_lt hB)
      have hstart : value3P walk first second phaseLate phaseCache state =
          (W1 state * unit128) * (if Late3 walk phaseLate phaseCache state then 0 else 1) := by
        unfold value3P pairAt secondFactor
        rw [hget1, hgetNone]
      rw [hstart]
      calc ∑' z, Pr{let x ← step}[x = z] * value3P walk first second phaseLate phaseCache z.2
          ≤ ∑' z, Pr{let x ← step}[x = z] *
              ((W1 z.2 * unit128) * (if Late3 walk phaseLate phaseCache state then 0 else 1)) := by
            refine tsum_le_of_support step _ _ fun z hz => ?_
            unfold value3P pairAt
            rw [hz1 z hz]
            dsimp only
            by_cases hBz : second < z.2.2.2.2.length
            · obtain ⟨-, e2, hgetZ, hcase⟩ := tape_filing walk phaseLate phaseCache queried state
                hinv.1 second hB z hz hBz
              unfold secondFactor
              rw [hgetZ]
              dsimp only
              rcases hcase with hle | hlateZ
              · exact mul_le_mul' (mul_le_mul' le_rfl hle) (ite_late_le (hlate z hz))
              · rw [ite_eq_left hlateZ, mul_zero]; exact zero_le
            · unfold secondFactor
              rw [List.getElem?_eq_none (Nat.le_of_not_lt hBz)]
              exact mul_le_mul' le_rfl (ite_late_le (hlate z hz))
        _ = (∑' z, Pr{let x ← step}[x = z] * W1 z.2) * unit128 *
              (if Late3 walk phaseLate phaseCache state then 0 else 1) := by
            rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
            exact tsum_congr fun z => by ring
        _ ≤ (W1 state * unit128) * (if Late3 walk phaseLate phaseCache state then 0 else 1) :=
            mul_le_mul' (mul_le_mul' (watchValue_step_le _ _ _ _ queried state) le_rfl) le_rfl
  · have hgetNone : state.2.2.2[first]? = none :=
      List.getElem?_eq_none (Nat.le_of_not_lt hA)
    have hvalueStart : value3P walk first second phaseLate phaseCache state = 0 := by
      unfold value3P pairAt; rw [hgetNone]; simp
    have hboundStart : bound3P walk first state = 0 := by
      unfold bound3P; rw [ite_eq_right hA]
    rw [hvalueStart, hboundStart, add_zero, zero_add]
    refine tsum_le_of_support step _ _ fun z hz => ?_
    by_cases hAz : first < z.2.2.2.2.length
    swap
    · unfold value3P pairAt
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hAz)]
      simp
    obtain ⟨hindex, e1, hgetZ, hcase⟩ := tape_filing walk phaseLate phaseCache queried state
      hinv.1 first hA z hz hAz
    have hBz : ¬ second < z.2.2.2.2.length := by
      have := hlen z hz; omega
    unfold bound3P
    rw [ite_eq_left hAz]
    unfold value3P pairAt secondFactor
    rw [hgetZ, List.getElem?_eq_none (Nat.le_of_not_lt hBz)]
    dsimp only
    rcases hcase with hle | hlateZ
    · calc watchValue (targetOf walk.1.1.2.1 (keyAt walk) e1.1) (HitsOf (keyAt walk) e1.1)
            z.2 * unit128 * (if Late3 walk phaseLate phaseCache z.2 then 0 else 1)
          ≤ unit128 * unit128 * 1 := mul_le_mul' (mul_le_mul' hle le_rfl) ite_late_le_one
        _ = unit128 * unit128 := mul_one _
    · rw [ite_eq_left hlateZ, mul_zero]; exact zero_le

open scoped Classical in
/-- **At the end, two reached cells that both fired have pair value one.** -/
theorem end_conditionP (adversary : Adversary) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    (first second : Nat) (hlt : first < second)
    (leftTape rightTape : List HashOutput) (middle : Forgery × FState walk)
    (final : (Bool × Tally) × SplitTapeState (CountedAt (keyAt walk)))
    (hfinal : final ∈ support ((simulateQ (noticingSplitTapeRecorder (leftAt walk)
      (rightAt walk)) (countRecorded verifierCost
        (Scheme.verify (keyAt walk) middle.1.message middle.1.signature))).run middle.2.2.2))
    (hinv : Inv3 walk (Late2 walk middle.2) (cacheF walk middle.2) final.2)
    (hw : (CarrierCoverage.tailValue (skAt walk, keyAt walk) middle.1 middle.2.1 middle.2.2.1
        final.1 final.2.1, forgetViewTape final.2) ∈
      support (tapeRun adversary walk leftTape rightTape)) :
    (if second < (forgetViewTape final.2).2.2.length ∧
        Fired walk (CarrierCoverage.tailValue (skAt walk, keyAt walk) middle.1 middle.2.1
          middle.2.2.1 final.1 final.2.1, forgetViewTape final.2) first ∧
        Fired walk (CarrierCoverage.tailValue (skAt walk, keyAt walk) middle.1 middle.2.1
          middle.2.2.1 final.1 final.2.1, forgetViewTape final.2) second then 1 else 0) ≤
      value3P walk first second (Late2 walk middle.2) (cacheF walk middle.2) final.2 := by
  classical
  split_ifs with hevent
  swap
  · exact zero_le
  obtain ⟨hreach2, hfired1, hfired2⟩ := hevent
  have hreach1 : first < (forgetViewTape final.2).2.2.length := lt_trans hlt hreach2
  have hv1 := end_condition adversary walk hwalk hgood first leftTape rightTape middle final hfinal
    hinv hw
  have hv2 := end_condition adversary walk hwalk hgood second leftTape rightTape middle final
    hfinal hinv hw
  rw [ite_eq_left ⟨hreach1, hfired1⟩] at hv1
  rw [ite_eq_left ⟨hreach2, hfired2⟩] at hv2
  obtain ⟨e1, hget1, -⟩ := hfired1
  obtain ⟨e2, hget2, -⟩ := hfired2
  have hget1' : final.2.2.2.2[first]? = some e1 := hget1
  have hget2' : final.2.2.2.2[second]? = some e2 := hget2
  unfold value3 watchAt at hv1 hv2
  rw [hget1'] at hv1
  rw [hget2'] at hv2
  unfold value3P pairAt secondFactor
  rw [hget1', hget2']
  dsimp only at hv1 hv2 ⊢
  by_cases hlate : Late3 walk (Late2 walk middle.2) (cacheF walk middle.2) final.2
  · rw [ite_eq_left hlate, mul_zero] at hv1
    exact absurd hv1 (by simp)
  · rw [ite_eq_right hlate, mul_one] at hv1 hv2 ⊢
    calc (1 : ℝ≥0∞) = 1 * 1 := (mul_one 1).symm
      _ ≤ _ := mul_le_mul' hv1 hv2

open scoped Classical in
/-- **Reaching two target cells and seeing both fire costs `2 ^ -256` on top of reaching the
first**, at the carrier tail's tape run with both blocks fixed. -/
theorem thin2 (adversary : Adversary) (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : Target.GoodWalk walk) (first second : Nat) (hlt : first < second)
    (leftTape rightTape : List HashOutput) :
    Pr{let w ← tapeRun adversary walk leftTape rightTape}[
        second < w.2.2.2.length ∧ Fired walk w first ∧ Fired walk w second] ≤
      (unit128 * unit128) *
        Pr{let w ← tapeRun adversary walk leftTape rightTape}[first < w.2.2.2.length] := by
  classical
  set F : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState → ℝ≥0∞ :=
    fun w => if second < w.2.2.2.length ∧ Fired walk w first ∧ Fired walk w second then 1 else 0
    with hFdef
  set G : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState → ℝ≥0∞ :=
    fun w => if first < w.2.2.2.length then unit128 * unit128 else 0 with hGdef
  rw [← FiredCoverage.tsum_ite_eq_probEvent, ← FiredCoverage.tsum_ite_eq_probEvent,
    ← ENNReal.tsum_mul_left]
  have hG : ∀ w, (unit128 * unit128) *
      (Pr{let x ← tapeRun adversary walk leftTape rightTape}[x = w] *
      (if first < w.2.2.2.length then 1 else 0)) =
      Pr{let x ← tapeRun adversary walk leftTape rightTape}[x = w] * G w := fun w => by
    rw [hGdef]; dsimp only; split_ifs <;> ring
  rw [tsum_congr hG]
  suffices h : (∑' w, Pr{let x ← tapeRun adversary walk leftTape rightTape}[x = w] * F w) + 0 ≤
      0 + ∑' w, Pr{let x ← tapeRun adversary walk leftTape rightTape}[x = w] * G w by
    rw [add_zero, zero_add] at h
    exact h
  refine expect_bind_signed_le (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
    (fun _ => True) (fun _ => 0) (fun _ => 0) (fun _ => zero_le_one)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ => by simp) _ _ trivial _ F G ?_
  rintro ⟨⟨sk, pk⟩, keyState⟩ hkeys
  obtain ⟨hk, hcache1, hright1⟩ := keygen_stage walk hwalk leftTape rightTape _ hkeys
  obtain ⟨hsk, hpk⟩ := Prod.mk.inj hk
  subst hsk
  subst hpk
  dsimp only
  have hstart : Inv2P walk ((1 : Multiplicative Tally), ([] : SigningLog), keyState) :=
    ⟨inv2_start walk hwalk hgood keyState hcache1 hright1,
      ⟨fun entry hentry => by
        have : entry ∈ keyState.2.2.2 := hentry
        rw [hright1] at this; exact absurd this (by simp),
       by change (keyState.2.2.2.map Prod.fst).Nodup; rw [hright1]; simp⟩⟩
  have hb0 : bound2P walk first ((1 : Multiplicative Tally), ([] : SigningLog), keyState) = 0 := by
    unfold bound2P; rw [ite_eq_right]; change ¬ first < keyState.2.2.2.length; rw [hright1]; simp
  have hv0 : value2P walk first second
      ((1 : Multiplicative Tally), ([] : SigningLog), keyState) = 0 := by
    unfold value2P pairAt
    rw [show keyState.2.2.2[first]? = none by rw [hright1]; simp]
    simp
  have hphase := expect_bind_signed_le (fusedAt walk) (Inv2P walk) (value2P walk first second)
    (bound2P walk first) (bound2P_le_one walk first)
    (fun queried state hinv z hz => inv2P_step walk hwalk hgood queried state hinv z hz)
    (fun queried state hinv => stage2P_step walk hwalk hgood first second hlt queried state hinv)
    (adversary.main (keyAt walk)) ((1 : Multiplicative Tally), ([] : SigningLog), keyState) hstart
    (fun middle => (simulateQ (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
        (countRecorded verifierCost
          (Scheme.verify (keyAt walk) middle.1.message middle.1.signature))).run
          middle.2.2.2 >>= fun final =>
        (pure (CarrierCoverage.tailValue (skAt walk, keyAt walk) middle.1 middle.2.1
          middle.2.2.1 final.1 final.2.1, forgetViewTape final.2) :
          ProbComp (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)))
    F G ?_
  · rw [hb0, hv0] at hphase
    exact hphase
  intro middle hmiddle
  have hinv2 : Inv2P walk middle.2 := run_invariant (fusedAt walk) (Inv2P walk)
    (fun queried state hinv z hz => inv2P_step walk hwalk hgood queried state hinv z hz)
    _ _ hstart middle hmiddle
  have hinv3 : Inv3P walk (Late2 walk middle.2) (cacheF walk middle.2) middle.2.2.2 :=
    ⟨⟨fun x hx => (hinv2.1.1 x hx).imp id Or.inl, hinv2.1.2, fun _ _ h => h⟩, hinv2.2⟩
  have hverify := expect_bind_signed_le (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
    (Inv3P walk (Late2 walk middle.2) (cacheF walk middle.2))
    (value3P walk first second (Late2 walk middle.2) (cacheF walk middle.2)) (bound3P walk first)
    (bound3P_le_one walk first)
    (fun queried state hinv z hz => inv3P_step walk _ _ queried state hinv z hz)
    (fun queried state hinv => stage3P_step walk first second hlt _ _ queried state hinv)
    (countRecorded verifierCost (Scheme.verify (keyAt walk) middle.1.message middle.1.signature))
    middle.2.2.2 hinv3
    (fun final => (pure (CarrierCoverage.tailValue (skAt walk, keyAt walk) middle.1 middle.2.1
      middle.2.2.1 final.1 final.2.1, forgetViewTape final.2) :
      ProbComp (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)))
    F G ?_
  · refine le_trans (le_of_eq_of_le (by rfl) hverify) (add_le_add ?_ le_rfl)
    unfold value3P value2P
    exact mul_le_mul' le_rfl (ite_late_le (fun hlate => Or.inl hlate))
  intro final hfinal
  have hinvFinal := run_invariant (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
    (Inv3P walk (Late2 walk middle.2) (cacheF walk middle.2))
    (fun queried state hinv z hz => inv3P_step walk _ _ queried state hinv z hz)
    _ _ hinv3 final hfinal
  refine pure_signed_le _ final.2 _ _ F G (add_le_add ?_ (le_of_eq rfl))
  refine end_conditionP adversary walk hwalk hgood first second hlt leftTape rightTape middle
    final hfinal hinvFinal.1 ?_
  unfold tapeRun threeStageTapeRun
  rw [mem_support_bind_iff]
  refine ⟨((skAt walk, keyAt walk), keyState), hkeys, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨middle, hmiddle, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨final, hfinal, by simp⟩

end SLHDSA.SHAKE128s.CarrierThin
