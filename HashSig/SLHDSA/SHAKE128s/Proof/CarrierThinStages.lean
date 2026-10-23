/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.TapeRunFacts
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierCoverage
public import HashSig.SLHDSA.SHAKE128s.Proof.Target127
public import HashSig.SLHDSA.SHAKE128s.Proof.AnswerCarrier
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierLeftRecord
import VCVio.OracleComp.EvalDist.Sum

/-!
# The fired-cell thinning: watched values and their per-step bounds

`FiredCoverage.prob_firedCovered_le` asks the carrier tail's run for two thinning bounds: a target
cell that is reached and then **fires** — its input turns out to be signer-randomised, so a later
signature serves it — costs `2 ^ -128` on top of being reached, and two such cells cost `2 ^ -256`.
This file sets up the run at fixed tape blocks (`tapeRun`) and proves the one-step facts both
bounds are assembled from; `CarrierThin` assembles them into `CarrierThin.thin1` and `thin2`.

**Why it holds.** A target cell `x = messageInput r pk m` fires when the `PRF_msg` answer at
`targetOf x = randomizerInput SK.prf PK.seed m` truncates to `r`. When `x` is filed that answer
is either not yet drawn — and then it is drawn fresh later, or filed, which the watch excludes —
or already drawn. In the second case the answer was drawn by the signer (who then also asked `x`,
so `x` was cached and could not have been filed), by the adversary (which is the seed guess
`PrfHit`), or by the signer's digest query landing on a `PRF_msg` input (which is `SignerHit`).
So off `late` the second case never fires, and the first is a fresh `2 ^ -128`.

**How it is proved.** A compensated supermartingale (`SignedWatch`): the watched value of the
cell's target (`watchAt`), zeroed once `late` has begun, against a bound that jumps to `2 ^ -128`
when the cell is reached. The invariant that makes the filing step cheap is *every
signer-randomised input is cached, or `late` has begun* (`Covered`), and the three stages each
keep it for their own reason: key generation files nothing (`keygen_stage`), the fused adversary
phase keeps `Inv2` and pays as it goes (`inv2_step`, `stage2_step`), and verification keeps
`Inv3` (`inv3_step`, `stage3_step`).

The right keep is the carrier's with the `PRF_msg` class at the real seed taken out
(`keep127`). That costs nothing — a seed guess is excluded by `late` anyway — and it is what
keeps a watched target out of the target recording.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CarrierThin

open Security DigestTape TapeFactor NoticingTape RecorderView PhaseFusion FusedTape TapeWatch
  SignedWatch TapeRunFacts CountedView CarriedWitness RecordedQueries BracketedRun CarrierTail

/-! ## The watched input of a target cell -/

/-- The framed message an `H_msg` input carries. -/
def msgOf (input : Bytes) : Bytes := input.drop (3 * n)

/-- The framed message of a message input is the message it frames. -/
theorem msgOf_messageInput (randomizer : Digest) (pk : PublicKey) (message : Bytes) :
    msgOf (Hashing.messageInput randomizer pk message) = message := by
  unfold msgOf Hashing.messageInput
  rw [List.drop_left']
  simp only [List.length_append, length_bytesBE]
  ring

/-- **The answer that makes a target cell fire**: its `PRF_msg` answer truncates to the cell's
own randomiser. -/
def HitsOf (pk : PublicKey) (input : Bytes) (answer : HashOutput) : Prop :=
  Hashing.messageInput (Hashing.truncate answer) pk (msgOf input) = input

/-- **The input whose answer decides it**: the `PRF_msg` input at the real seed and the cell's
own framed message. -/
def targetOf (prf : Digest) (pk : PublicKey) (input : Bytes) : Bytes :=
  Hashing.randomizerInput prf pk.seed (msgOf input)

/-- A cell's target lies in the `PRF_msg` class at the real seed. -/
theorem prfClass_targetOf (prf : Digest) (pk : PublicKey) (input : Bytes) :
    RandomizerGate.PrfClass prf (targetOf prf pk input) :=
  ⟨pk.seed, msgOf input, rfl⟩

/-- **Signer-randomised is the watched event, read at a cache.** -/
theorem signerRandomised_iff (prf : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input : Bytes) :
    CacheAvailability.SignerRandomised prf pk cache input ↔
      ∃ answer, cache (targetOf prf pk input) = some answer ∧ HitsOf pk input answer := by
  constructor
  · rintro ⟨message, answer, hcached, rfl⟩
    refine ⟨answer, ?_, ?_⟩
    · rw [targetOf, msgOf_messageInput]
      exact hcached
    · rw [HitsOf, msgOf_messageInput]
  · rintro ⟨answer, hcached, hhits⟩
    exact ⟨msgOf input, answer, hcached, hhits.symm⟩

/-- **One fresh answer makes a fixed cell fire with probability at most `2 ^ -128`.** -/
theorem prob_hitsOf_le (pk : PublicKey) (input : Bytes) :
    Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[(HitsOf pk input) x] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  by_cases hsome : ∃ first, HitsOf pk input first
  · obtain ⟨first, hfirst⟩ := hsome
    refine le_trans (prEvent_mono _ _ _ fun answer hanswer => ?_)
      (le_of_eq (RandomizerGate.prob_truncate_eq (Hashing.truncate first)))
    exact (Hashing.messageInput_injective (hanswer.trans hfirst.symm)).1
  · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _
      fun answer _ hanswer => hsome ⟨answer, hanswer⟩)) zero_le

/-! ## The run, at fixed blocks -/

/-- The carrier with its counter, as a cache view at one key. A synonym, so that the view is an
instance. -/
def CountedAt (_pk : PublicKey) : Type := Counted

/-- The counted carrier at key `pk` is a cache view through `countedView pk`. -/
noncomputable instance (pk : PublicKey) : CacheView (CountedAt pk) := countedView pk

/-- **The target test the `127` route uses**: the carrier's, less the `PRF_msg` class at the
real seed. -/
def keep127 (walk : Walk) (input : Bytes) (state : HandlerCarrier.State) : Prop :=
  AnswerCarrier.carrierRightKeep walk input state ∧
    ¬ RandomizerGate.PrfClass walk.1.1.2.1 input

/-- The left test, at the counted view. -/
def leftAt (walk : Walk) : Bytes → CountedAt (keyAt walk) → Prop :=
  liftTest (disclosingKeep (keyAt walk))

/-- The right test, at the counted view. -/
def rightAt (walk : Walk) : Bytes → CountedAt (keyAt walk) → Prop :=
  liftTest (keep127 walk)

/-- The walk's secret key. -/
noncomputable def skAt (walk : Walk) : SecretKey :=
  { seed := walk.1.1.1, prf := walk.1.1.2.1, publicKey := keyAt walk }

/-- The handler the phase is fused over. -/
noncomputable def innerAt (keys : SecretKey × PublicKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT (Multiplicative Tally) (StateT SigningLog (OracleComp OracleWorld))) :=
  recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1)

/-- **The carrier tail's tape run, at fixed blocks.** -/
noncomputable def tapeRun (adversary : Adversary) (walk : Walk)
    (leftTape rightTape : List HashOutput) :
    ProbComp (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) :=
  threeStageTapeRun (σ := CountedAt (keyAt walk)) (leftAt walk) (rightAt walk) innerAt
    ServedAgreement.startServingOn ServedAgreement.stopServingOn
    (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)
    (fun keys => adversary.main keys.2)
    (fun keys forgery => countRecorded verifierCost
      (Scheme.verify keys.2 forgery.message forgery.signature))
    CarrierCoverage.tailValue ((startAt walk.2, 0) : Counted) [] [] leftTape rightTape

/-! ## Key generation files nothing and changes no answer -/

set_option maxHeartbeats 400000 in
-- Unfolding key generation through the noticing tape recorder exceeds the default budget.
/-- **Key generation, run from the walk's cache, leaves the cache as it was and the target
recording empty**, and returns the walk's own key. -/
theorem keygen_stage (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (leftTape rightTape : List HashOutput)
    (keys : (SecretKey × PublicKey) × SplitTapeState (CountedAt (keyAt walk)))
    (hkeys : keys ∈ support ((simulateQ (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
        (((startAt walk.2, 0) : Counted), (leftTape, rightTape), ([], [])))) :
    keys.1 = (skAt walk, keyAt walk) ∧
      CacheView.cacheOf keys.2.1 = walk.2 ∧ keys.2.2.2.2 = [] := by
  classical
  have hrom := tape_run_rom (leftAt walk) (rightAt walk) _ _ keys hkeys
  obtain ⟨outputs, hwarm⟩ := HonestGrowth.walk_cache_eq_warmCache hwalk
  have hstart : CacheView.cacheOf (σ := CountedAt (keyAt walk))
      ((startAt walk.2, 0) : Counted) = walk.2 := rfl
  rw [hstart, hwarm, HonestProbes.run_keygenInternal_world_eq_pure, support_pure,
    Set.mem_singleton_iff, Prod.mk.injEq] at hrom
  obtain ⟨hvalue, hcache⟩ := hrom
  rw [← hwarm] at hvalue hcache
  have hcacheEq : CacheView.cacheOf keys.2.1 = walk.2 := hcache
  refine ⟨by rw [hvalue]; exact Prod.ext (SigningFaithful.keygen_secretKey _ _ _ _) rfl,
    hcacheEq, ?_⟩
  obtain ⟨suffix, hsuffix, hentries⟩ := run_right_suffix (leftAt walk) (rightAt walk)
    (fun _ => True) ⟨fun _ _ _ => trivial, fun _ _ _ _ => trivial⟩ _ _ trivial keys hkeys
  rw [hsuffix]
  cases suffix with
  | nil => rfl
  | cons entry rest =>
    obtain ⟨hfresh, hfinal, -⟩ := hentries entry List.mem_cons_self
    rw [hcacheEq] at hfinal
    rw [hstart, hfinal] at hfresh
    exact absurd hfresh (by simp)

/-! ## What a signing sub-run caches and files

The signer's queries are of three kinds — structural inputs, its own `PRF_msg` input and its own
digest input — and none of them passes `keep127` while its request is in flight: a structural
input is not a message input on a good walk, the `PRF_msg` input is in the excluded class, and the
digest input is the disclosing test's. So a signing sub-run files nothing as a target. -/

/-- The public seed of the walk's key is the walk's own. -/
theorem keyAt_seed (walk : Walk) : (keyAt walk).seed = walk.1.1.2.2 := rfl

/-- A hash query, simulated, is the implementation at that input. -/
theorem simulateQ_hashQuery {S : Type} (impl : QueryImpl OracleWorld (StateT S ProbComp))
    (input : Bytes) :
    simulateQ impl (query (spec := OracleWorld) (Sum.inr input) :
        OracleComp OracleWorld HashOutput) = impl (Sum.inr input) := by
  simp

/-- The framing is a property the notice and the installation keep. -/
theorem kept_framing (pk : PublicKey) (framed : Option Bytes) :
    Kept (σ := CountedAt pk) (fun carrier : CountedAt pk => carrier.1.framing = framed) :=
  ⟨fun carrier input h => by
      change (servingNotice pk carrier.1 input).framing = framed
      rw [framing_servingNotice]; exact h,
    fun carrier input answer h => by
      change (HandlerCarrier.cacheAnswer carrier.1 input answer).framing = framed
      rw [HandlerCarrier.framing_cacheAnswer]; exact h⟩

/-- **Every input a signing sub-run newly caches is structural, or one of its request's two.** -/
theorem sign_new_cached (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : Target.GoodWalk walk) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed)
    (state : SplitTapeState (CountedAt (keyAt walk)))
    (z : Option Bytes × SplitTapeState (CountedAt (keyAt walk)))
    (hz : z ∈ support ((simulateQ (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
      (Scheme.sign (m := OracleComp OracleWorld) (skAt walk) request)).run state))
    (probe : Bytes) (hfresh : CacheView.cacheOf state.1 probe = none)
    (hpresent : CacheView.cacheOf z.2.1 probe ≠ none) :
    (¬ CombinedCharge.IsMessageInput (keyAt walk) probe ∧
        ¬ RandomizerGate.PrfClass walk.1.1.2.1 probe) ∨
      probe = Hashing.randomizerInput walk.1.1.2.1 walk.1.1.2.2 framed ∨
      probe = Hashing.messageInput
        (HonestProbes.replayRandomizer (CacheView.cacheOf z.2.1) (skAt walk) framed) (keyAt walk)
        framed := by
  classical
  have hrom := tape_run_rom (leftAt walk) (rightAt walk) _ state z hz
  rw [StrippedGame.sign_lift] at hrom
  have hquery := CacheProvenance.queriesUnder_of_fresh_liftComp _ _ _
    (CacheView.cacheOf z.2.1) z.1 hrom (fun _ _ h => h) probe hfresh hpresent
  rcases HonestProbes.probes_sign _ (skAt walk) request framed hframe probe hquery with
    ⟨parent, hcanonical⟩ | hmessage
  · refine Or.inl ⟨?_, ?_⟩
    · rw [hcanonical]
      exact WarmedCharges.not_messageInput_canonical _ _ (keyAt walk)
        (AnswerSide.not_possible_generatedKey hwalk hgood.2) withinBounds_structural parent
    · rintro ⟨seed, message, hinput⟩
      rw [hcanonical] at hinput
      exact RandomizerGate.canonicalInput_ne_randomizerInput _ walk.1.1.2.1 seed _ parent
        message hgood.1 hinput
  · rcases hmessage with hrandomiser | hdigest
    · exact Or.inr (Or.inl hrandomiser)
    · exact Or.inr (Or.inr hdigest)

/-- **A signing sub-run files nothing as a target**, and leaves its request's `PRF_msg` answer
and its digest input both cached. -/
theorem sign_stage (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : Target.GoodWalk walk) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed)
    (state : SplitTapeState (CountedAt (keyAt walk))) (hframing : state.1.1.framing = some framed)
    (z : Option Bytes × SplitTapeState (CountedAt (keyAt walk)))
    (hz : z ∈ support ((simulateQ (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
      (Scheme.sign (m := OracleComp OracleWorld) (skAt walk) request)).run state)) :
    z.2.2.2.2 = state.2.2.2 ∧
      ∃ seed : HashOutput,
        CacheView.cacheOf z.2.1 (Hashing.randomizerInput walk.1.1.2.1 walk.1.1.2.2 framed) =
          some seed ∧
        CacheView.cacheOf z.2.1
          (Hashing.messageInput (Hashing.truncate seed) (keyAt walk) framed) ≠ none := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨suffix, hsuffix, hentries⟩ := run_right_suffix (leftAt walk) (rightAt walk)
      (fun carrier : CountedAt (keyAt walk) => carrier.1.framing = some framed)
      (kept_framing (keyAt walk) (some framed)) _ state hframing z hz
    rw [hsuffix]
    cases suffix with
    | nil => rw [List.append_nil]
    | cons entry rest =>
      exfalso
      obtain ⟨hfresh, hfinal, mid, hmidFraming, -, -, hright⟩ :=
        hentries entry List.mem_cons_self
      obtain ⟨⟨⟨hmessage, -⟩, hnotLeft⟩, hnotPrf⟩ := hright
      rcases sign_new_cached walk hwalk hgood request framed hframe state z hz
        entry.1 hfresh (by rw [hfinal]; simp) with ⟨hnotMessage, -⟩ | hrandomiser | hdigest
      · exact hnotMessage hmessage
      · exact hnotPrf ⟨walk.1.1.2.2, framed, hrandomiser⟩
      · exact hnotLeft ⟨framed, hmidFraming, _, hdigest⟩
  · obtain ⟨rest, hshape⟩ := ServedAgreement.sign_shape (skAt walk) request framed hframe
    rw [hshape, simulateQ_bind, simulateQ_hashQuery, StateT.run_bind, mem_support_bind_iff]
      at hz
    obtain ⟨first, hfirst, hz⟩ := hz
    rw [simulateQ_bind, simulateQ_hashQuery, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨second, hsecond, hz⟩ := hz
    have hseed := tapeStep_cache_self (leftAt walk) (rightAt walk) _ state first hfirst
    have hdigest := tapeStep_cache_self (leftAt walk) (rightAt walk) _ first.2 second hsecond
    refine ⟨first.1, ?_, ?_⟩
    · exact run_cache_persists (leftAt walk) (rightAt walk) _ second.2 z hz _ first.1
        (tapeStep_cache_persists (leftAt walk) (rightAt walk) _ _ first.1 first.2 hseed second
          hsecond)
    · have h : CacheView.cacheOf z.2.1
          (Hashing.messageInput (Hashing.truncate first.1) (keyAt walk) framed) = some second.1 :=
        run_cache_persists (leftAt walk) (rightAt walk) _ second.2 z hz _ second.1 hdigest
      rw [h]
      simp

/-! ## The fused phase, one step at a time -/

/-- The fused handler the adversary's phase runs under. -/
noncomputable abbrev fusedAt (walk : Walk) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (Multiplicative Tally × SigningLog × SplitTapeState (CountedAt (keyAt walk)))
        ProbComp) :=
  fuseServing (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
    (innerAt (skAt walk, keyAt walk))
    (fun request => onCarrierTape (ServedAgreement.startServingOn request))
    (onCarrierTape ServedAgreement.stopServingOn)

/-- The fused handler's state. -/
abbrev FState (walk : Walk) : Type :=
  Multiplicative Tally × SigningLog × SplitTapeState (CountedAt (keyAt walk))

/-- **An adversary query is one step of the tape recorder**, its input added to the record. -/
theorem adversary_step_shape (walk : Walk) (world : OracleWorld.Domain) (state : FState walk)
    (z : (OracleWorld + SigningSpec).Range (Sum.inl world) × FState walk)
    (hz : z ∈ support (((fusedAt walk) (Sum.inl world)).run state)) :
    ∃ step ∈ support (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk)) world).run
        state.2.2),
      z.2 = (state.1 * Multiplicative.ofAdd
          ((Counts.single .hash (hashCost world) : Counts), recordOf world),
        state.2.1, step.2) := by
  rw [fusedAt, FusedTape.fuseServing_run_inl, mem_support_bind_iff] at hz
  obtain ⟨sub, hsub, hpure⟩ := hz
  rw [support_pure, Set.mem_singleton_iff] at hpure
  have hinner : (innerAt (skAt walk, keyAt walk)) (Sum.inl world) = recordedAdversaryImpl world :=
    rfl
  rw [hinner, run_recordedAdversaryImpl, simulateQ_map, StateT.run_map,
    PhaseRightRecord.simulateQ_worldQuery, support_map] at hsub
  obtain ⟨step, hstep, rfl⟩ := hsub
  exact ⟨step, hstep, by rw [hpure]⟩

/-- **A signing request is one signing sub-run**, bracketed, with the request logged. -/
theorem signing_step_shape (walk : Walk) (request : Message) (state : FState walk)
    (z : (OracleWorld + SigningSpec).Range (Sum.inr request) × FState walk)
    (hz : z ∈ support (((fusedAt walk) (Sum.inr request)).run state)) :
    ∃ (answer : Option Bytes) (inner : SplitTapeState (CountedAt (keyAt walk))),
      (answer, inner) ∈ support ((simulateQ (noticingSplitTapeRecorder (leftAt walk)
        (rightAt walk)) (Scheme.sign (m := OracleComp OracleWorld) (skAt walk) request)).run
          (onCarrierTape (ServedAgreement.startServingOn request) state.2.2)) ∧
      z.2 = (state.1 * Multiplicative.ofAdd
          ((Counts.single .signing 1 : Counts), (0 : Multiset Bytes)),
        state.2.1 ++ [⟨request, answer⟩], onCarrierTape ServedAgreement.stopServingOn inner) := by
  rw [fusedAt, FusedTape.fuseServing_run_inr, mem_support_bind_iff] at hz
  obtain ⟨sub, hsub, hpure⟩ := hz
  rw [support_pure, Set.mem_singleton_iff] at hpure
  have hinner : (innerAt (skAt walk, keyAt walk)) (Sum.inr request) =
      recordedSigningOracle (Scheme.sign (skAt walk)) request := rfl
  rw [hinner, run_recordedSigningOracle, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hsub
  obtain ⟨signed, hsigned, hrest⟩ := hsub
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  refine ⟨signed.1, signed.2, hsigned, ?_⟩
  rw [hpure, hrest]
  rfl

/-! ## `late`, as far as the run has got -/

/-- **The defect so far, at the fused state**: an adversary query in the `PRF_msg` class at the
real seed, or a signature whose randomiser is the seed. -/
def Late2 (walk : Walk) (state : FState walk) : Prop :=
  (∃ y ∈ (Multiplicative.toAdd state.1).2, RandomizerGate.PrfClass walk.1.1.2.1 y) ∨
    RandomiserProvenance.SignerHitsSeed walk.1.1.2.1 walk.1.1.2.2
      (CacheView.cacheOf state.2.2.1) state.2.1

/-- **Every signer-randomised input is cached, or `late` has begun.** -/
def Covered (walk : Walk) (cache : QueryCache HashSpec) (late : Prop) : Prop :=
  ∀ input, CacheAvailability.SignerRandomised walk.1.1.2.1 (keyAt walk) cache input →
    cache input ≠ none ∨ late

/-- No target entry is in the excluded class. -/
def RightClean (walk : Walk) (record : Record) : Prop :=
  ∀ entry ∈ record, ¬ RandomizerGate.PrfClass walk.1.1.2.1 entry.1

/-- **The invariant of the fused phase.** -/
def Inv2 (walk : Walk) (state : FState walk) : Prop :=
  Covered walk (CacheView.cacheOf state.2.2.1) (Late2 walk state) ∧
    RightClean walk state.2.2.2.2.2

/-- **A signer coincidence survives growth** of the cache and of the log. -/
theorem signerHitsSeed_mono {prf publicSeed : Digest} {cache later : QueryCache HashSpec}
    {log longer : SigningLog}
    (hcache : ∀ input answer, cache input = some answer → later input = some answer)
    (hlog : ∀ entry ∈ log, entry ∈ longer)
    (hhit : RandomiserProvenance.SignerHitsSeed prf publicSeed cache log) :
    RandomiserProvenance.SignerHitsSeed prf publicSeed later longer := by
  obtain ⟨entry, hentry, framed, answer, hframe, hcached, htrunc⟩ := hhit
  exact ⟨entry, hlog entry hentry, framed, answer, hframe, hcache _ _ hcached, htrunc⟩

/-- **`late` so far only grows**, given the cache does, the log does and the record does. -/
theorem late2_mono (walk : Walk) (state later : FState walk)
    (hrecord : (Multiplicative.toAdd state.1).2 ≤ (Multiplicative.toAdd later.1).2)
    (hlog : ∀ entry ∈ state.2.1, entry ∈ later.2.1)
    (hcache : ∀ input answer, CacheView.cacheOf state.2.2.1 input = some answer →
      CacheView.cacheOf later.2.2.1 input = some answer)
    (hlate : Late2 walk state) : Late2 walk later := by
  rcases hlate with ⟨y, hy, hprf⟩ | hhit
  · exact Or.inl ⟨y, Multiset.mem_of_le hrecord hy, hprf⟩
  · exact Or.inr (signerHitsSeed_mono hcache hlog hhit)

/-- The record a step adds to. -/
theorem toAdd_mul_record (tally : Multiplicative Tally) (counts : Counts)
    (record : Multiset Bytes) :
    (Multiplicative.toAdd (tally * Multiplicative.ofAdd (counts, record))).2 =
      (Multiplicative.toAdd tally).2 + record := rfl

/-- The brackets keep the cache. -/
theorem cacheOf_startServingOn (pk : PublicKey) (request : Message) (carrier : CountedAt pk) :
    CacheView.cacheOf (σ := CountedAt pk) (ServedAgreement.startServingOn request carrier) =
      CacheView.cacheOf carrier := by
  change (ServedAgreement.startServingOn request carrier).1.cache = carrier.1.cache
  unfold ServedAgreement.startServingOn
  split <;> rfl

/-- Lowering the frame keeps the cache. -/
theorem cacheOf_stopServingOn (pk : PublicKey) (carrier : CountedAt pk) :
    CacheView.cacheOf (σ := CountedAt pk) (ServedAgreement.stopServingOn carrier) =
      CacheView.cacheOf carrier := rfl

/-! ## What one fused step grows, and what it keeps -/

/-- The cache of a fused state. -/
noncomputable abbrev cacheF (walk : Walk) (state : FState walk) : QueryCache HashSpec :=
  CacheView.cacheOf state.2.2.1

/-- The target recording of a fused state. -/
abbrev rightF (walk : Walk) (state : FState walk) : Record := state.2.2.2.2.2

/-- The record of a fused state. -/
abbrev recordF (walk : Walk) (state : FState walk) : Multiset Bytes :=
  (Multiplicative.toAdd state.1).2

/-- **A fused step never fails.** -/
theorem fused_step_neverFails (walk : Walk) (queried : (OracleWorld + SigningSpec).Domain)
    (state : FState walk) : prFail (((fusedAt walk) queried).run state) = 0 :=
  OracleComp.prFail_eq_zero _

/-- A request with no frame makes no query. -/
theorem sign_none_run (walk : Walk) (request : Message) (hframe : request.frame = none)
    (state : SplitTapeState (CountedAt (keyAt walk)))
    (z : Option Bytes × SplitTapeState (CountedAt (keyAt walk)))
    (hz : z ∈ support ((simulateQ (noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
      (Scheme.sign (m := OracleComp OracleWorld) (skAt walk) request)).run state)) :
    z.2 = state := by
  rw [Scheme.sign, hframe, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  rw [hz]

/-- And its bracket does nothing. -/
theorem startServingOn_none (request : Message) (hframe : request.frame = none) {τ : Type}
    (state : HandlerCarrier.State × τ) : ServedAgreement.startServingOn request state = state := by
  rw [ServedAgreement.startServingOn, hframe]

/-- A framed request's bracket raises the frame. -/
theorem framing_startServingOn (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed) {τ : Type} (state : HandlerCarrier.State × τ) :
    (ServedAgreement.startServingOn request state).1.framing = some framed := by
  rw [ServedAgreement.startServingOn, hframe]
  rfl

/-- **One fused step grows the record, the log, the cache and the target recording.** -/
theorem fused_step_grows (walk : Walk) (queried : (OracleWorld + SigningSpec).Domain)
    (state : FState walk) (z : (OracleWorld + SigningSpec).Range queried × FState walk)
    (hz : z ∈ support (((fusedAt walk) queried).run state)) :
    recordF walk state ≤ recordF walk z.2 ∧ (∀ entry ∈ state.2.1, entry ∈ z.2.2.1) ∧
      (∀ input answer, cacheF walk state input = some answer →
        cacheF walk z.2 input = some answer) ∧
      rightF walk state <+: rightF walk z.2 := by
  classical
  rcases queried with world | request
  · obtain ⟨step, hstep, hz2⟩ := adversary_step_shape walk world state z hz
    rw [hz2]
    refine ⟨by dsimp only [recordF]; rw [toAdd_mul_record]; exact Multiset.le_add_right _ _,
      fun entry h => h, ?_,
      (noticingSplitTapeRecorder_step _ _ world state.2.2).2 step hstep⟩
    intro input answer hcached
    rcases world with coin | queriedInput
    · rw [tapeStep_inl _ _ coin state.2.2 step hstep]
      exact hcached
    · exact tapeStep_cache_persists _ _ queriedInput input answer state.2.2 hcached step hstep
  · obtain ⟨answer, inner, hinner, hz2⟩ := signing_step_shape walk request state z hz
    rw [hz2]
    refine ⟨by dsimp only [recordF]; rw [toAdd_mul_record, add_zero],
      fun entry h => List.mem_append_left _ h, ?_,
      noticingRightOf_prefix _ _ _
        (onCarrierTape (σ := CountedAt (keyAt walk)) (ServedAgreement.startServingOn request)
          state.2.2) (answer, inner) hinner⟩
    intro input value hcached
    exact run_cache_persists _ _ _ _ (answer, inner) hinner input value
      (by rw [show CacheView.cacheOf (onCarrierTape (σ := CountedAt (keyAt walk))
          (ServedAgreement.startServingOn request) state.2.2).1 = CacheView.cacheOf state.2.2.1 from
            cacheOf_startServingOn (keyAt walk) request state.2.2.1]
          exact hcached)

/-- **`late` so far survives a fused step.** -/
theorem late2_step (walk : Walk) (queried : (OracleWorld + SigningSpec).Domain)
    (state : FState walk) (z : (OracleWorld + SigningSpec).Range queried × FState walk)
    (hz : z ∈ support (((fusedAt walk) queried).run state)) (hlate : Late2 walk state) :
    Late2 walk z.2 := by
  obtain ⟨hrecord, hlog, hcache, -⟩ := fused_step_grows walk queried state z hz
  exact late2_mono walk state z.2 hrecord hlog hcache hlate

/-- **The fused phase keeps the invariant.** An adversary query that caches a `PRF_msg` input at
the real seed is a seed guess; a signing request caches its own `PRF_msg` input together with the
digest input that answer makes signer-randomised, or its digest input lands on a `PRF_msg` input,
which is the signer's coincidence. -/
theorem inv2_step (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : Target.GoodWalk walk) (queried : (OracleWorld + SigningSpec).Domain)
    (state : FState walk) (hinv : Inv2 walk state)
    (z : (OracleWorld + SigningSpec).Range queried × FState walk)
    (hz : z ∈ support (((fusedAt walk) queried).run state)) : Inv2 walk z.2 := by
  classical
  obtain ⟨-, -, hcache, -⟩ := fused_step_grows walk queried state z hz
  simp only [cacheF] at hcache
  have hlate := late2_step walk queried state z hz
  rcases queried with world | request
  · obtain ⟨step, hstep, hz2⟩ := adversary_step_shape walk world state z hz
    rcases world with coin | input
    · have hsame := tapeStep_inl (leftAt walk) (rightAt walk) coin state.2.2 step hstep
      refine ⟨fun x hx => ?_, ?_⟩
      · have hcacheEq : CacheView.cacheOf z.2.2.2.1 = CacheView.cacheOf state.2.2.1 := by
          rw [hz2]; dsimp only; rw [hsame]
        rw [hcacheEq] at hx ⊢
        exact (hinv.1 x hx).imp id hlate
      · intro entry hentry
        have hrightEq : z.2.2.2.2.2.2 = state.2.2.2.2.2 := by
          rw [hz2]; dsimp only; rw [hsame]
        rw [hrightEq] at hentry
        exact hinv.2 entry hentry
    · refine ⟨fun x hx => ?_, ?_⟩
      · obtain ⟨answer, hcached, hhits⟩ := (signerRandomised_iff _ _ _ x).mp hx
        by_cases htarget : targetOf walk.1.1.2.1 (keyAt walk) x = input
        · refine Or.inr (Or.inl ⟨input, ?_, ?_⟩)
          · rw [hz2]
            dsimp only [recordF]
            rw [toAdd_mul_record]
            exact Multiset.mem_add.mpr (Or.inr (by simp [recordOf]))
          · rw [← htarget]
            exact prfClass_targetOf _ _ x
        · have hbefore : CacheView.cacheOf state.2.2.1 (targetOf walk.1.1.2.1 (keyAt walk) x) =
              some answer := by
            have hne := tapeStep_cache_ne (leftAt walk) (rightAt walk) input _ htarget state.2.2
              step hstep
            have hz' : CacheView.cacheOf z.2.2.2.1 = CacheView.cacheOf step.2.1 := by rw [hz2]
            rw [hz'] at hcached
            rw [← hne]
            exact hcached
          rcases hinv.1 x ((signerRandomised_iff _ _ _ x).mpr ⟨answer, hbefore, hhits⟩) with
            hpresent | hlateBefore
          · refine Or.inl fun hnone => hpresent ?_
            cases hold : CacheView.cacheOf state.2.2.1 x with
            | none => rfl
            | some value => rw [hcache x value hold] at hnone; exact absurd hnone (by simp)
          · exact Or.inr (hlate hlateBefore)
      · intro entry hentry
        have hright : z.2.2.2.2.2.2 = step.2.2.2.2 := by rw [hz2]
        rw [hright] at hentry
        rcases tapeStep_inr_cases (leftAt walk) (rightAt walk) input state.2.2 step hstep with
          ⟨-, hst⟩ | ⟨-, -, hst⟩ | ⟨-, -, hkeep, hst⟩ | ⟨-, -, -, hst⟩
        · rw [hst] at hentry; exact hinv.2 entry hentry
        · rw [hst] at hentry; exact hinv.2 entry hentry
        · rw [hst] at hentry
          rcases List.mem_append.mp hentry with hold | hnew
          · exact hinv.2 entry hold
          · rw [List.mem_singleton] at hnew
            subst hnew
            exact hkeep.2
        · rw [hst] at hentry; exact hinv.2 entry hentry
  · obtain ⟨answer, inner, hinner, hz2⟩ := signing_step_shape walk request state z hz
    have hcacheZ : CacheView.cacheOf z.2.2.2.1 = CacheView.cacheOf inner.1 := by rw [hz2]; rfl
    have hrightZ : z.2.2.2.2.2.2 = inner.2.2.2 := by rw [hz2]; rfl
    have hlogZ : z.2.2.1 = state.2.1 ++ [⟨request, answer⟩] := by rw [hz2]
    have hstartCache : CacheView.cacheOf (onCarrierTape (σ := CountedAt (keyAt walk))
        (ServedAgreement.startServingOn request) state.2.2).1 = CacheView.cacheOf state.2.2.1 :=
      cacheOf_startServingOn (keyAt walk) request state.2.2.1
    cases hframe : request.frame with
    | none =>
      have hinnerEq := sign_none_run walk request hframe _ (answer, inner) hinner
      have hsame : inner = state.2.2 := by
        have h1 : inner = onCarrierTape (σ := CountedAt (keyAt walk))
            (ServedAgreement.startServingOn request) state.2.2 := hinnerEq
        rw [h1]
        exact congrArg (fun carrier => (carrier, state.2.2.2))
          (startServingOn_none request hframe state.2.2.1)
      refine ⟨fun x hx => ?_, fun entry hentry => ?_⟩
      · rw [hcacheZ, hsame] at hx ⊢
        exact (hinv.1 x hx).imp id hlate
      · rw [hrightZ, hsame] at hentry
        exact hinv.2 entry hentry
    | some framed =>
      obtain ⟨hrightInner, seed, hseed, hdigest⟩ := sign_stage walk hwalk hgood request framed
        hframe _ (framing_startServingOn request framed hframe state.2.2.1) (answer, inner) hinner
      refine ⟨fun x hx => ?_, fun entry hentry => ?_⟩
      · obtain ⟨value, hcached, hhits⟩ := (signerRandomised_iff _ _ _ x).mp hx
        rw [hcacheZ] at hcached
        cases hold : CacheView.cacheOf state.2.2.1 (targetOf walk.1.1.2.1 (keyAt walk) x) with
        | some old =>
          have hpersist := run_cache_persists _ _ _ _ (answer, inner) hinner _ old
            (by rw [hstartCache]; exact hold)
          rw [hcached] at hpersist
          cases Option.some.inj hpersist
          rcases hinv.1 x ((signerRandomised_iff _ _ _ x).mpr ⟨value, hold, hhits⟩) with
            hpresent | hlateBefore
          · refine Or.inl fun hnone => hpresent ?_
            cases hx' : CacheView.cacheOf state.2.2.1 x with
            | none => rfl
            | some v => rw [hcache x v hx'] at hnone; exact absurd hnone (by simp)
          · exact Or.inr (hlate hlateBefore)
        | none =>
          rcases sign_new_cached walk hwalk hgood request framed hframe _ (answer, inner) hinner
            (targetOf walk.1.1.2.1 (keyAt walk) x) (by rw [hstartCache]; exact hold)
            (by rw [hcached]; simp) with ⟨-, hnotPrf⟩ | hrandomiser | hdigestShape
          · exact absurd (prfClass_targetOf _ _ x) hnotPrf
          · -- the request's own `PRF_msg` input: its digest input is cached
            have hmsg : msgOf x = framed :=
              (Hashing.randomizerInput_injective hrandomiser).2.2
            rw [hrandomiser] at hcached
            rw [hseed] at hcached
            cases Option.some.inj hcached
            refine Or.inl ?_
            rw [hcacheZ]
            rw [HitsOf, hmsg] at hhits
            rw [← hhits]
            exact hdigest
          · -- the digest input lands on a `PRF_msg` input: the signer's coincidence
            have hprfEq := RandomizerGate.messageInput_eq_randomizerInput_iff _ walk.1.1.2.1
              (keyAt walk).seed (keyAt walk) framed (msgOf x) hdigestShape.symm
            have hreplay := ServedAgreement.replayRandomizer_of_cached (CacheView.cacheOf inner.1)
              (skAt walk) framed seed hseed
            rw [hreplay] at hprfEq
            refine Or.inr (Or.inr ⟨⟨request, answer⟩, ?_, framed, seed, hframe, ?_, hprfEq⟩)
            · rw [hlogZ]; exact List.mem_append_right _ (List.mem_singleton_self _)
            · rw [hcacheZ]; exact hseed
      · rw [hrightZ, hrightInner] at hentry
        exact hinv.2 entry hentry

/-- **A signing request files nothing as a target.** -/
theorem signing_step_right (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : Target.GoodWalk walk) (request : Message) (state : FState walk)
    (z : (OracleWorld + SigningSpec).Range (Sum.inr request) × FState walk)
    (hz : z ∈ support (((fusedAt walk) (Sum.inr request)).run state)) :
    z.2.2.2.2.2.2 = state.2.2.2.2.2 := by
  obtain ⟨answer, inner, hinner, hz2⟩ := signing_step_shape walk request state z hz
  have hrightZ : z.2.2.2.2.2.2 = inner.2.2.2 := by rw [hz2]; rfl
  rw [hrightZ]
  cases hframe : request.frame with
  | none =>
    have hinnerEq := sign_none_run walk request hframe _ (answer, inner) hinner
    have h1 : inner = onCarrierTape (σ := CountedAt (keyAt walk))
        (ServedAgreement.startServingOn request) state.2.2 := hinnerEq
    rw [h1]
    rfl
  | some framed =>
    exact (sign_stage walk hwalk hgood request framed hframe _
      (framing_startServingOn request framed hframe state.2.2.1) (answer, inner) hinner).1

/-! ## The watched value of one target cell -/

open scoped Classical in
/-- **The watched value of target cell `index`**: zero until the cell is filed, then the watched
value of its `PRF_msg` input. -/
noncomputable def watchAt (walk : Walk) (index : Nat)
    (state : SplitTapeState (CountedAt (keyAt walk))) : ℝ≥0∞ :=
  match state.2.2.2[index]? with
  | some entry => watchValue (targetOf walk.1.1.2.1 (keyAt walk) entry.1)
      (HitsOf (keyAt walk) entry.1) state
  | none => 0

/-- The unit one fresh `PRF_msg` coin costs. -/
noncomputable abbrev unit128 : ℝ≥0∞ := 1 / ((2 ^ 128 : Nat) : ℝ≥0∞)

open scoped Classical in
/-- **The value of the fused phase**: the cell's watched value, zeroed once `late` has begun. -/
noncomputable def value2 (walk : Walk) (index : Nat) (state : FState walk) : ℝ≥0∞ :=
  watchAt walk index state.2.2 * (if Late2 walk state then 0 else 1)

open scoped Classical in
/-- **The bound of the fused phase**: one unit once the cell is reached. -/
noncomputable def bound2 (walk : Walk) (index : Nat) (state : FState walk) : ℝ≥0∞ :=
  if index < state.2.2.2.2.2.length then unit128 else 0

/-- A weighted sum of a pointwise inequality on the support. -/
theorem tsum_le_of_support {β : Type} (computation : ProbComp β) (left right : β → ℝ≥0∞)
    (h : ∀ z ∈ support computation, left z ≤ right z) :
    ∑' z, Pr{let x ← computation}[x = z] * left z ≤
      ∑' z, Pr{let x ← computation}[x = z] * right z := by
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : z ∈ support computation
  · exact mul_le_mul' le_rfl (h z hz)
  · rw [(prEvent_eq_zero_of_not_mem_support _) hz, zero_mul, zero_mul]

/-- A constant, averaged over a computation that never fails. -/
theorem tsum_const_of_neverFails {β : Type} (computation : ProbComp β)
    (hfail : prFail computation = 0) (constant : ℝ≥0∞) :
    ∑' z, Pr{let x ← computation}[x = z] * constant = constant := by
  rw [ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one, one_mul]

open scoped Classical in
/-- **Right after a cell is filed, its watched value is one fresh coin's mass — unless its
`PRF_msg` answer was already drawn and makes it signer-randomised.** -/
theorem filing_watch_le (walk : Walk) (state : SplitTapeState (CountedAt (keyAt walk)))
    (input : Bytes) (hnotPrf : ¬ RandomizerGate.PrfClass walk.1.1.2.1 input)
    (step : HashOutput × SplitTapeState (CountedAt (keyAt walk)))
    (hstep : step ∈ support (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
      (Sum.inr input)).run state)) :
    watchValue (targetOf walk.1.1.2.1 (keyAt walk) input) (HitsOf (keyAt walk) input) step.2 ≤
        unit128 ∨
      CacheAvailability.SignerRandomised walk.1.1.2.1 (keyAt walk)
        (CacheView.cacheOf state.1) input := by
  classical
  have hne : targetOf walk.1.1.2.1 (keyAt walk) input ≠ input := fun h =>
    hnotPrf (h ▸ prfClass_targetOf walk.1.1.2.1 (keyAt walk) input)
  have hsame := tapeStep_cache_ne (leftAt walk) (rightAt walk) input _ hne state step hstep
  cases hcached : CacheView.cacheOf state.1 (targetOf walk.1.1.2.1 (keyAt walk) input) with
  | none =>
    refine Or.inl ?_
    unfold watchValue
    rw [hsame, hcached]
    exact prob_hitsOf_le (keyAt walk) input
  | some answer =>
    by_cases hhits : HitsOf (keyAt walk) input answer
    · exact Or.inr ((signerRandomised_iff _ _ _ input).mpr ⟨answer, hcached, hhits⟩)
    · refine Or.inl (le_trans (watchValue_le_of_cache _ _ step.2 answer
        (by rw [hsame, hcached])) ?_)
      rw [ite_eq_right hhits]
      exact zero_le

open scoped Classical in
/-- **The fused phase pays for its watched value as it is earned.** -/
theorem stage2_step (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk)
    (hgood : Target.GoodWalk walk) (index : Nat)
    (queried : (OracleWorld + SigningSpec).Domain) (state : FState walk)
    (hinv : Inv2 walk state) :
    (∑' z, Pr{let x ← ((fusedAt walk) queried).run state}[x = z] * value2 walk index z.2) +
        bound2 walk index state ≤
      value2 walk index state +
        ∑' z, Pr{let x ← ((fusedAt walk) queried).run state}[x = z] * bound2 walk index z.2 := by
  classical
  set step := ((fusedAt walk) queried).run state with hstepDef
  have hfail : prFail step = 0 := fused_step_neverFails walk queried state
  by_cases hreached : index < state.2.2.2.2.2.length
  · -- the cell is already filed: a supermartingale, and the bound does not move
    set entry := state.2.2.2.2.2[index] with hentry
    have hget : state.2.2.2.2.2[index]? = some entry := List.getElem?_eq_getElem hreached
    set target := targetOf walk.1.1.2.1 (keyAt walk) entry.1
    set hits := HitsOf (keyAt walk) entry.1
    have hwatch : ∀ z ∈ support step, watchAt walk index z.2.2.2 = watchValue target hits z.2.2.2 ∧
        bound2 walk index z.2 = unit128 := by
      intro z hz
      have hprefix := (fused_step_grows walk queried state z hz).2.2.2
      have hgetZ : z.2.2.2.2.2.2[index]? = some entry := by
        obtain ⟨tail, htail⟩ := hprefix
        change (rightF walk z.2)[index]? = some entry
        rw [← htail, List.getElem?_append_left hreached]
        exact hget
      refine ⟨?_, ?_⟩
      · unfold watchAt
        rw [hgetZ]
      · unfold bound2
        rw [ite_eq_left (List.getElem?_eq_some_iff.mp hgetZ).1]
    have hvalueStart : value2 walk index state =
        watchValue target hits state.2.2 * (if Late2 walk state then 0 else 1) := by
      unfold value2 watchAt
      rw [hget]
    have hboundStart : bound2 walk index state = unit128 := by
      unfold bound2; rw [ite_eq_left hreached]
    rw [hvalueStart, hboundStart]
    have hboundEnd : ∑' z, Pr{let x ← step}[x = z] * bound2 walk index z.2 = unit128 := by
      rw [show (∑' z, Pr{let x ← step}[x = z] * bound2 walk index z.2) =
          ∑' z, Pr{let x ← step}[x = z] * unit128 from tsum_congr fun z => by
            by_cases hz : z ∈ support step
            · rw [(hwatch z hz).2]
            · rw [(prEvent_eq_zero_of_not_mem_support _) hz, zero_mul, zero_mul]]
      exact tsum_const_of_neverFails step hfail unit128
    rw [hboundEnd]
    refine add_le_add ?_ le_rfl
    calc ∑' z, Pr{let x ← step}[x = z] * value2 walk index z.2
        ≤ ∑' z, Pr{let x ← step}[x = z] *
            (watchValue target hits z.2.2.2 * (if Late2 walk state then 0 else 1)) := by
          refine tsum_le_of_support step _ _ fun z hz => ?_
          unfold value2
          rw [(hwatch z hz).1]
          refine mul_le_mul' le_rfl ?_
          by_cases hlate : Late2 walk state
          · rw [ite_eq_left (late2_step walk queried state z hz hlate), ite_eq_left hlate]
          · rw [ite_eq_right hlate]; split_ifs <;> simp
      _ = (∑' z, Pr{let x ← step}[x = z] * watchValue target hits z.2.2.2) *
            (if Late2 walk state then 0 else 1) := by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun z => by ring
      _ ≤ watchValue target hits state.2.2 * (if Late2 walk state then 0 else 1) := by
          refine mul_le_mul' ?_ le_rfl
          exact fused_step_le (leftAt walk) (rightAt walk) (innerAt (skAt walk, keyAt walk))
            ServedAgreement.startServingOn ServedAgreement.stopServingOn
            (watchValue target hits)
            (fun queried state => watchValue_step_le _ _ target hits queried state)
            (fun request state => watchValue_onCarrierTape target hits _
              (cacheOf_startServingOn (keyAt walk) request) state)
            (fun state => watchValue_onCarrierTape target hits _
              (cacheOf_stopServingOn (keyAt walk)) state) queried state
  · -- the cell is not filed yet: the value is zero, and a filing step pays at most a unit
    have hvalueStart : value2 walk index state = 0 := by
      unfold value2 watchAt
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hreached)]
      simp
    have hboundStart : bound2 walk index state = 0 := by
      unfold bound2; rw [ite_eq_right hreached]
    rw [hvalueStart, hboundStart, add_zero, zero_add]
    refine tsum_le_of_support step _ _ fun z hz => ?_
    by_cases hreachedZ : index < z.2.2.2.2.2.2.length
    swap
    · unfold value2 watchAt
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hreachedZ)]
      simp
    unfold bound2
    rw [ite_eq_left hreachedZ]
    rcases queried with world | request
    · obtain ⟨inner, hinner, hz2⟩ := adversary_step_shape walk world state z hz
      have hrightZ : z.2.2.2.2.2.2 = inner.2.2.2.2 := by rw [hz2]
      rcases world with coin | input
      · rw [hrightZ, tapeStep_inl _ _ coin state.2.2 inner hinner] at hreachedZ
        exact absurd hreachedZ hreached
      · rcases tapeStep_inr_cases (leftAt walk) (rightAt walk) input state.2.2 inner hinner with
          ⟨-, hst⟩ | ⟨-, -, hst⟩ | ⟨hfresh, -, hkeep, hst⟩ | ⟨-, -, -, hst⟩
        · rw [hrightZ, hst] at hreachedZ; exact absurd hreachedZ hreached
        · rw [hrightZ, hst] at hreachedZ; exact absurd hreachedZ hreached
        · -- the filing step itself
          have hindex : index = state.2.2.2.2.2.length := by
            rw [hrightZ, hst] at hreachedZ
            simp only [List.length_append, List.length_singleton] at hreachedZ
            omega
          have hgetZ : z.2.2.2.2.2.2[index]? = some (input, inner.1) := by
            rw [hrightZ, hst, hindex]
            simp
          have hcarrier : z.2.2.2 = inner.2 := by rw [hz2]
          unfold value2 watchAt
          rw [hgetZ]
          dsimp only
          rw [hcarrier]
          rcases filing_watch_le walk state.2.2 input hkeep.2 inner hinner with hle | hsigner
          · calc watchValue (targetOf walk.1.1.2.1 (keyAt walk) input) (HitsOf (keyAt walk) input)
                  inner.2 * (if Late2 walk z.2 then 0 else 1)
                ≤ watchValue (targetOf walk.1.1.2.1 (keyAt walk) input)
                    (HitsOf (keyAt walk) input) inner.2 * 1 := by
                  refine mul_le_mul' le_rfl ?_; split_ifs <;> simp
              _ ≤ unit128 := by rw [mul_one]; exact hle
          · rcases hinv.1 input hsigner with hpresent | hlate
            · exact absurd (by rw [← CacheView.cache_onQuery state.2.2.1 input]; exact hfresh)
                hpresent
            · rw [ite_eq_left (late2_step walk _ state z hz hlate), mul_zero]
              exact zero_le
        · rw [hrightZ, hst] at hreachedZ; exact absurd hreachedZ hreached
    · rw [signing_step_right walk hwalk hgood request state z hz] at hreachedZ
      exact absurd hreachedZ hreached

/-! ## Verification

The verifier's queries are recorded too, so a `PRF_msg` input at the real seed that it caches is
a seed guess. The state does not carry the verifier's record, so the stage tracks the guess
through the cache instead: a `PRF_msg` input cached now and not at the end of the phase
(`NewPrf`). -/

/-- **A `PRF_msg` input at the real seed cached since the phase ended.** -/
def NewPrf (walk : Walk) (phaseCache : QueryCache HashSpec)
    (state : SplitTapeState (CountedAt (keyAt walk))) : Prop :=
  ∃ y, RandomizerGate.PrfClass walk.1.1.2.1 y ∧ CacheView.cacheOf state.1 y ≠ none ∧
    phaseCache y = none

/-- `late` as far as verification has got. -/
def Late3 (walk : Walk) (phaseLate : Prop) (phaseCache : QueryCache HashSpec)
    (state : SplitTapeState (CountedAt (keyAt walk))) : Prop :=
  phaseLate ∨ NewPrf walk phaseCache state

/-- **The invariant of verification.** -/
def Inv3 (walk : Walk) (phaseLate : Prop) (phaseCache : QueryCache HashSpec)
    (state : SplitTapeState (CountedAt (keyAt walk))) : Prop :=
  Covered walk (CacheView.cacheOf state.1) (Late3 walk phaseLate phaseCache state) ∧
    RightClean walk state.2.2.2 ∧
    ∀ y answer, phaseCache y = some answer → CacheView.cacheOf state.1 y = some answer

/-- The cache only grows, one recorder step at a time. -/
theorem tapeStep_persists (walk : Walk) (queried : OracleWorld.Domain)
    (state : SplitTapeState (CountedAt (keyAt walk)))
    (step : OracleWorld.Range queried × SplitTapeState (CountedAt (keyAt walk)))
    (hstep : step ∈ support (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
      queried).run state))
    (input : Bytes) (answer : HashOutput)
    (hcached : CacheView.cacheOf state.1 input = some answer) :
    CacheView.cacheOf step.2.1 input = some answer := by
  rcases queried with coin | queriedInput
  · rw [tapeStep_inl _ _ coin state step hstep]; exact hcached
  · exact tapeStep_cache_persists _ _ queriedInput input answer state hcached step hstep

/-- **`late` as far as verification has got survives a recorder step.** -/
theorem late3_step (walk : Walk) (phaseLate : Prop) (phaseCache : QueryCache HashSpec)
    (queried : OracleWorld.Domain) (state : SplitTapeState (CountedAt (keyAt walk)))
    (step : OracleWorld.Range queried × SplitTapeState (CountedAt (keyAt walk)))
    (hstep : step ∈ support (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
      queried).run state))
    (hlate : Late3 walk phaseLate phaseCache state) :
    Late3 walk phaseLate phaseCache step.2 := by
  rcases hlate with hphase | ⟨y, hprf, hpresent, hfresh⟩
  · exact Or.inl hphase
  · refine Or.inr ⟨y, hprf, fun hnone => hpresent ?_, hfresh⟩
    cases hcached : CacheView.cacheOf state.1 y with
    | none => rfl
    | some value =>
      rw [tapeStep_persists walk queried state step hstep y value hcached] at hnone
      exact absurd hnone (by simp)

/-- **Verification keeps its invariant.** -/
theorem inv3_step (walk : Walk) (phaseLate : Prop) (phaseCache : QueryCache HashSpec)
    (queried : OracleWorld.Domain) (state : SplitTapeState (CountedAt (keyAt walk)))
    (hinv : Inv3 walk phaseLate phaseCache state)
    (step : OracleWorld.Range queried × SplitTapeState (CountedAt (keyAt walk)))
    (hstep : step ∈ support (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk))
      queried).run state)) :
    Inv3 walk phaseLate phaseCache step.2 := by
  classical
  have hlate := late3_step walk phaseLate phaseCache queried state step hstep
  have hpersist := tapeStep_persists walk queried state step hstep
  rcases queried with coin | input
  · have hsame := tapeStep_inl (leftAt walk) (rightAt walk) coin state step hstep
    rw [hsame]
    exact hinv
  · refine ⟨fun x hx => ?_, fun entry hentry => ?_,
      fun y answer hy => hpersist y answer (hinv.2.2 y answer hy)⟩
    · obtain ⟨answer, hcached, hhits⟩ := (signerRandomised_iff _ _ _ x).mp hx
      by_cases htarget : targetOf walk.1.1.2.1 (keyAt walk) x = input
      · by_cases hfreshInput : CacheView.cacheOf state.1 input = none
        · refine Or.inr (Or.inr ⟨input, htarget ▸ prfClass_targetOf _ _ x, ?_, ?_⟩)
          · rw [tapeStep_cache_self _ _ input state step hstep]; simp
          · cases hphase : phaseCache input with
            | none => rfl
            | some value =>
              rw [hinv.2.2 input value hphase] at hfreshInput
              exact absurd hfreshInput (by simp)
        · obtain ⟨old, hold⟩ := Option.ne_none_iff_exists'.mp hfreshInput
          have hpersistOld := hpersist input old hold
          rw [← htarget] at hpersistOld hold
          rw [hcached] at hpersistOld
          cases Option.some.inj hpersistOld
          rcases hinv.1 x ((signerRandomised_iff _ _ _ x).mpr ⟨answer, hold, hhits⟩) with
            hpresent | hlateBefore
          · refine Or.inl fun hnone => hpresent ?_
            cases hx' : CacheView.cacheOf state.1 x with
            | none => rfl
            | some v => rw [hpersist x v hx'] at hnone; exact absurd hnone (by simp)
          · exact Or.inr (hlate hlateBefore)
      · have hbefore : CacheView.cacheOf state.1 (targetOf walk.1.1.2.1 (keyAt walk) x) =
            some answer := by
          rw [← tapeStep_cache_ne _ _ input _ htarget state step hstep]
          exact hcached
        rcases hinv.1 x ((signerRandomised_iff _ _ _ x).mpr ⟨answer, hbefore, hhits⟩) with
          hpresent | hlateBefore
        · refine Or.inl fun hnone => hpresent ?_
          cases hx' : CacheView.cacheOf state.1 x with
          | none => rfl
          | some v => rw [hpersist x v hx'] at hnone; exact absurd hnone (by simp)
        · exact Or.inr (hlate hlateBefore)
    · rcases tapeStep_inr_cases (leftAt walk) (rightAt walk) input state step hstep with
        ⟨-, hst⟩ | ⟨-, -, hst⟩ | ⟨-, -, hkeep, hst⟩ | ⟨-, -, -, hst⟩
      · rw [hst] at hentry; exact hinv.2.1 entry hentry
      · rw [hst] at hentry; exact hinv.2.1 entry hentry
      · rw [hst] at hentry
        rcases List.mem_append.mp hentry with hold | hnew
        · exact hinv.2.1 entry hold
        · rw [List.mem_singleton] at hnew
          subst hnew
          exact hkeep.2
      · rw [hst] at hentry; exact hinv.2.1 entry hentry

open scoped Classical in
/-- **The value of verification.** -/
noncomputable def value3 (walk : Walk) (index : Nat) (phaseLate : Prop)
    (phaseCache : QueryCache HashSpec) (state : SplitTapeState (CountedAt (keyAt walk))) :
    ℝ≥0∞ :=
  watchAt walk index state * (if Late3 walk phaseLate phaseCache state then 0 else 1)

open scoped Classical in
/-- **The bound of verification.** -/
noncomputable def bound3 (walk : Walk) (index : Nat)
    (state : SplitTapeState (CountedAt (keyAt walk))) : ℝ≥0∞ :=
  if index < state.2.2.2.length then unit128 else 0

open scoped Classical in
/-- **Verification pays for its watched value as it is earned.** -/
theorem stage3_step (walk : Walk) (index : Nat) (phaseLate : Prop)
    (phaseCache : QueryCache HashSpec) (queried : OracleWorld.Domain)
    (state : SplitTapeState (CountedAt (keyAt walk)))
    (hinv : Inv3 walk phaseLate phaseCache state) :
    (∑' z, Pr{let x ← (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk)) queried).run
          state)}[x = z] *
        value3 walk index phaseLate phaseCache z.2) + bound3 walk index state ≤
      value3 walk index phaseLate phaseCache state +
        ∑' z, Pr{let x ← (((noticingSplitTapeRecorder (leftAt walk) (rightAt walk)) queried).run
          state)}[x = z] * bound3 walk index z.2 := by
  classical
  set step := ((noticingSplitTapeRecorder (leftAt walk) (rightAt walk)) queried).run state
    with hstepDef
  have hfail : prFail step = 0 :=
    (noticingSplitTapeRecorder_step (leftAt walk) (rightAt walk) queried state).1
  by_cases hreached : index < state.2.2.2.length
  · set entry := state.2.2.2[index] with hentry
    have hget : state.2.2.2[index]? = some entry := List.getElem?_eq_getElem hreached
    set target := targetOf walk.1.1.2.1 (keyAt walk) entry.1
    set hits := HitsOf (keyAt walk) entry.1
    have hwatch : ∀ z ∈ support step, watchAt walk index z.2 = watchValue target hits z.2 ∧
        bound3 walk index z.2 = unit128 := by
      intro z hz
      have hprefix := (noticingSplitTapeRecorder_step (leftAt walk) (rightAt walk) queried
        state).2 z hz
      have hgetZ : z.2.2.2.2[index]? = some entry := by
        obtain ⟨tail, htail⟩ := hprefix
        change (rightOf z.2)[index]? = some entry
        rw [← htail]
        exact (List.getElem?_append_left hreached).trans hget
      refine ⟨?_, ?_⟩
      · unfold watchAt
        rw [hgetZ]
      · unfold bound3
        rw [ite_eq_left (List.getElem?_eq_some_iff.mp hgetZ).1]
    have hvalueStart : value3 walk index phaseLate phaseCache state =
        watchValue target hits state *
          (if Late3 walk phaseLate phaseCache state then 0 else 1) := by
      unfold value3 watchAt
      rw [hget]
    have hboundStart : bound3 walk index state = unit128 := by
      unfold bound3; rw [ite_eq_left hreached]
    rw [hvalueStart, hboundStart]
    have hboundEnd : ∑' z, Pr{let x ← step}[x = z] * bound3 walk index z.2 = unit128 := by
      rw [show (∑' z, Pr{let x ← step}[x = z] * bound3 walk index z.2) =
          ∑' z, Pr{let x ← step}[x = z] * unit128 from tsum_congr fun z => by
            by_cases hz : z ∈ support step
            · rw [(hwatch z hz).2]
            · rw [(prEvent_eq_zero_of_not_mem_support _) hz, zero_mul, zero_mul]]
      exact tsum_const_of_neverFails step hfail unit128
    rw [hboundEnd]
    refine add_le_add ?_ le_rfl
    calc ∑' z, Pr{let x ← step}[x = z] * value3 walk index phaseLate phaseCache z.2
        ≤ ∑' z, Pr{let x ← step}[x = z] *
            (watchValue target hits z.2 *
              (if Late3 walk phaseLate phaseCache state then 0 else 1)) := by
          refine tsum_le_of_support step _ _ fun z hz => ?_
          unfold value3
          rw [(hwatch z hz).1]
          refine mul_le_mul' le_rfl ?_
          by_cases hlate : Late3 walk phaseLate phaseCache state
          · rw [ite_eq_left (late3_step walk phaseLate phaseCache queried state z hz hlate),
              ite_eq_left hlate]
          · rw [ite_eq_right hlate]; split_ifs <;> simp
      _ = (∑' z, Pr{let x ← step}[x = z] * watchValue target hits z.2) *
            (if Late3 walk phaseLate phaseCache state then 0 else 1) := by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun z => by ring
      _ ≤ watchValue target hits state *
            (if Late3 walk phaseLate phaseCache state then 0 else 1) :=
          mul_le_mul' (watchValue_step_le _ _ target hits queried state) le_rfl
  · have hvalueStart : value3 walk index phaseLate phaseCache state = 0 := by
      unfold value3 watchAt
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hreached)]
      simp
    have hboundStart : bound3 walk index state = 0 := by
      unfold bound3; rw [ite_eq_right hreached]
    rw [hvalueStart, hboundStart, add_zero, zero_add]
    refine tsum_le_of_support step _ _ fun z hz => ?_
    by_cases hreachedZ : index < z.2.2.2.2.length
    swap
    · unfold value3 watchAt
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hreachedZ)]
      simp
    unfold bound3
    rw [ite_eq_left hreachedZ]
    rcases queried with coin | input
    · rw [tapeStep_inl _ _ coin state z hz] at hreachedZ
      exact absurd hreachedZ hreached
    · rcases tapeStep_inr_cases (leftAt walk) (rightAt walk) input state z hz with
        ⟨-, hst⟩ | ⟨-, -, hst⟩ | ⟨hfresh, -, hkeep, hst⟩ | ⟨-, -, -, hst⟩
      · rw [hst] at hreachedZ; exact absurd hreachedZ hreached
      · rw [hst] at hreachedZ; exact absurd hreachedZ hreached
      · have hindex : index = state.2.2.2.length := by
          rw [hst] at hreachedZ
          simp only [List.length_append, List.length_singleton] at hreachedZ
          omega
        have hgetZ : z.2.2.2.2[index]? = some (input, z.1) := by
          rw [hst, hindex]
          simp
        unfold value3 watchAt
        rw [hgetZ]
        dsimp only
        rcases filing_watch_le walk state input hkeep.2 z hz with hle | hsigner
        · calc watchValue (targetOf walk.1.1.2.1 (keyAt walk) input) (HitsOf (keyAt walk) input)
                z.2 * (if Late3 walk phaseLate phaseCache z.2 then 0 else 1)
              ≤ watchValue (targetOf walk.1.1.2.1 (keyAt walk) input)
                  (HitsOf (keyAt walk) input) z.2 * 1 := by
                refine mul_le_mul' le_rfl ?_; split_ifs <;> simp
            _ ≤ unit128 := by rw [mul_one]; exact hle
        · rcases hinv.1 input hsigner with hpresent | hlate
          · exact absurd (by rw [← CacheView.cache_onQuery state.1 input]; exact hfresh)
              hpresent
          · rw [ite_eq_left (late3_step walk phaseLate phaseCache _ state z hz hlate), mul_zero]
            exact zero_le
      · rw [hst] at hreachedZ; exact absurd hreachedZ hreached

end SlhDsaSecurity.CarrierThin
