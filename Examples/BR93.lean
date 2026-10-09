/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.AsymmEncAlg.Defs
public import VCVio.CryptoFoundations.HardnessAssumptions.OneWay
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.Coercions.SubSpec
public import VCVio.OracleComp.QueryTracking.LoggingOracle
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.EvalDist.Monad.Measure
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
import VCVio.OracleComp.QueryTracking.RandomOracle.Programming
import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility

/-!
# Bellare-Rogaway 1993 Encryption

This file sets up the Bellare-Rogaway 1993 public-key encryption construction from:

- a trapdoor permutation `f(pk, ·)` over a randomness space `Rand`
- a hash/random oracle `H : Rand → M`
- an additive message space `M`

Encryption samples `r ← Rand` and returns `(f(pk, r), H(r) + m)`. Decryption inverts the
trapdoor permutation and unmasks by subtraction.

The security proof follows the standard three-step outline:

1. Real CPA game.
2. Replace the challenge hash query with a fresh uniform mask, up to the bad event that the
   adversary queries the hidden `r`.
3. Replace the masked challenge message with a uniform ciphertext component, yielding success
   probability `1/2`.

The bad event is then reduced to the repo's trapdoor-preimage experiment
(`tdpAdvantage`) by inspecting the adversary's random-oracle queries. The bad-event
reduction uses a shared transcript and measure-event inclusion. The up-to-bad game
hop couples the real game with the idealized one by programming the revealed mask into the
random-oracle cache at the hidden input: the two runs agree unless the idealized run queries it.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal OneWay

namespace BR93

variable {PK SK Rand M : Type}

/-- The concrete BR93 scheme instantiated with an explicit hash function `hash : Rand → M`. -/
@[simps!] def br93AsymmEnc [SampleableType Rand] [AddCommGroup M]
    (tdp : TrapdoorPermutation PK SK Rand) (hash : Rand → M) :
    AsymmEncAlg ProbComp (M := M) (PK := PK) (SK := SK) (C := Rand × M) where
  keygen := tdp.keygen
  encrypt pk msg := do
    let r ← $ᵗ Rand
    return (tdp.forward pk r, hash r + msg)
  decrypt sk c :=
    return (some (c.2 - hash (tdp.inverse sk c.1)))

namespace br93AsymmEnc

variable {tdp : TrapdoorPermutation PK SK Rand} {hash : Rand → M}

/-- Correctness of BR93 follows from correctness of the underlying trapdoor permutation. -/
theorem correct [SampleableType Rand] [DecidableEq M] [AddCommGroup M] (hcorrect : tdp.Correct) :
    (br93AsymmEnc (M := M) tdp hash).PerfectlyCorrect ProbCompRuntime.probComp := by
  intro msg
  let mx : ProbComp Bool := do
    let x ← tdp.keygen
    let c ← (do let r ← $ᵗ Rand; pure (tdp.forward x.1 r, hash r + msg))
    let msg' ← pure (some (c.2 - hash (tdp.inverse x.2 c.1)))
    pure (decide (msg' = some msg))
  rw [ProbCompRuntime.probComp_evalDist]
  have huniq : ∀ y ∈ support mx, y = true := by
    intro y hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨⟨pk, sk⟩, hpksk, hy⟩ := hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨c, hc, hy⟩ := hy
    rw [mem_support_bind_iff] at hc
    obtain ⟨r, _, hc⟩ := hc
    rw [mem_support_bind_iff] at hy
    obtain ⟨msg', hmsg', hy⟩ := hy
    simp only [support_pure, Set.mem_singleton_iff] at hc hmsg' hy
    obtain rfl := hc
    obtain rfl := hmsg'
    obtain rfl := hy
    simp [hcorrect pk sk hpksk r]
  rw [evalDist_apply_singleton]
  exact probOutput_eq_one_of_support_subset_singleton
    (NeverFail.probFailure_eq_zero (mx := mx)) huniq

/-! ## One-time IND-CPA in the random-oracle model -/

/-- The shared oracle interface for BR93 games: unrestricted uniform sampling plus a
lazy random oracle `Rand → M`. -/
abbrev RO_Spec (Rand M : Type) := unifSpec + (Rand →ₒ M)

/-- A one-time CPA adversary for BR93. Both phases share access to the same random oracle. -/
structure CPA_Adversary (PK Rand M : Type) where
  /-- State passed from the challenge phase to the guessing phase. -/
  State : Type
  /-- Given the public key, choose two challenge messages and a state. -/
  choose : PK → OracleComp (RO_Spec Rand M) (M × M × State)
  /-- Given the state and the challenge ciphertext, guess which message was encrypted. -/
  guess : State → Rand × M → OracleComp (RO_Spec Rand M) Bool

/-! ### Random-oracle transcript observations

Pure facts about query logs over `RO_Spec` and their hash-oracle part `QueryLog.snd`, needing no
structure on `Rand` or `M` beyond what each statement names. -/

private lemma wasQueried_snd [DecidableEq Rand] (log : QueryLog (RO_Spec Rand M)) (r : Rand) :
    log.snd.wasQueried r = log.wasQueried (Sum.inr r) := by
  induction log with
  | nil => rfl
  | cons e log ih =>
    rcases e with ⟨_ | r', u⟩
    · simpa [QueryLog.snd] using ih
    · obtain rfl | h := eq_or_ne r' r <;> simp_all [QueryLog.snd]

/-- The first logged hash query whose forward image is `y`, with the inverter's default on
failure. -/
private def transcriptPreimage [DecidableEq Rand] [Inhabited Rand]
    (pk : PK) (y : Rand) (log : QueryLog (Rand →ₒ M)) : Rand :=
  ((log.find? fun e => tdp.forward pk e.1 = y).map (·.1)).getD default

/-- A bad transcript yields a valid trapdoor preimage: if the hash oracle was queried at `r`, the
first logged query with the forward image of `r` is a preimage of it. -/
private lemma forward_transcriptPreimage_of_wasQueried [DecidableEq Rand] [Inhabited Rand]
    (pk : PK) (r : Rand) (log : QueryLog (Rand →ₒ M)) (hbad : log.wasQueried r = true) :
    tdp.forward pk (transcriptPreimage (tdp := tdp) pk (tdp.forward pk r) log) =
      tdp.forward pk r := by
  simp only [QueryLog.wasQueried_eq_decide_mem_map_fst, decide_eq_true_eq, List.mem_map] at hbad
  obtain ⟨e, he, rfl⟩ := hbad
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp <|
    (List.find?_isSome (p := fun e' => tdp.forward pk e'.1 = tdp.forward pk e.1)).mpr
      ⟨e, he, by simp⟩
  simpa [transcriptPreimage, hfound] using List.find?_some hfound

/-- Searching a full log for a hash query, as `inverter` does, is `transcriptPreimage` on its
hash-oracle part. -/
private lemma match_find?_eq_pure_transcriptPreimage [DecidableEq Rand] [Inhabited Rand]
    (pk : PK) (y : Rand) (log : QueryLog (RO_Spec Rand M)) :
    (match log.find? (fun entry => match entry.1 with
        | Sum.inl _ => false
        | Sum.inr r => tdp.forward pk r = y) with
      | some entry => match entry.1 with
        | Sum.inl _ => (pure default : ProbComp Rand)
        | Sum.inr r => pure r
      | none => pure default) = pure (transcriptPreimage (tdp := tdp) pk y log.snd) := by
  induction log with
  | nil => rfl
  | cons e log ih =>
    rcases e with ⟨_ | r, u⟩
    · simpa [QueryLog.snd] using ih
    · by_cases h : tdp.forward pk r = y <;> simp_all [QueryLog.snd, transcriptPreimage]

/-! ### The random-oracle world

The games below run in the random oracle model `(Rand →ₒ M).romImpl`, whose lazy random oracle
`Rand → M` needs equality on `Rand` and a canonical sampler for `M`. -/

variable [DecidableEq Rand] [SampleableType M]

private def runRightLog {α : Type} (mx : OracleComp (RO_Spec Rand M) α)
    (cache : (Rand →ₒ M).QueryCache) :
    ProbComp ((α × QueryLog (Rand →ₒ M)) × (Rand →ₒ M).QueryCache) :=
  (fun x => ((x.1.1, x.1.2.snd), x.2)) <$>
    (simulateQ (Rand →ₒ M).romImpl.withLogging mx).run.run cache

private lemma runRightLog_bind {α β : Type} (mx : OracleComp (RO_Spec Rand M) α)
    (f : α → OracleComp (RO_Spec Rand M) β) (cache : (Rand →ₒ M).QueryCache) :
    runRightLog (mx >>= f) cache = (do
      let x ← runRightLog mx cache
      let y ← runRightLog (f x.1.1) x.2
      pure ((y.1.1, x.1.2 ++ y.1.2), y.2)) := by
  simp only [runRightLog, QueryImpl.run_run_simulateQ_withLogging_bind, map_bind, map_pure,
    bind_map_left, QueryLog.snd, List.filterMap_append]

private lemma runRightLog_pure {α : Type} (a : α) (cache : (Rand →ₒ M).QueryCache) :
    runRightLog (pure a) cache = pure ((a, []), cache) := by
  simp [runRightLog, QueryLog.snd, StateT.run_pure]

private lemma runRightLog_lift {α : Type} (p : ProbComp α)
    (cache : (Rand →ₒ M).QueryCache) :
    runRightLog (liftM p) cache = p >>= fun a => pure ((a, []), cache) := by
  unfold runRightLog
  rw [map_eq_pure_bind]
  trans (simulateQ (Rand →ₒ M).romImpl.withLogging (liftM p)).run.run cache >>=
    fun x => pure ((x.1.1, []), x.2)
  · apply bind_congr_of_forall_mem_support
    intro x hx
    have hlog : x.1.2.snd = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro e he
      rw [← OracleComp.liftComp_eq_liftM] at hx
      obtain ⟨a, ha⟩ :=
        QueryImpl.exists_inl_of_mem_support_run_simulateQ_withLogging_liftComp_stateT _ p cache x
          hx e he
      obtain ⟨t, u⟩ := e
      obtain rfl : t = _ := ha
      rfl
    rw [hlog]
  · rw [QueryImpl.bind_run_run_simulateQ_withLogging (f := fun a s => pure ((a, []), s)),
      roSim.run_liftM, bind_map_left]

/-- Inversion reduction: run the BR93 adversary in the idealized challenge game, log its
random-oracle queries, and return the first query whose image under the trapdoor permutation
matches the challenge `y`. -/
def inverter [Inhabited Rand] [AddCommGroup M] (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adversary PK Rand M) : TDPAdversary PK Rand :=
  fun pk y => do
    let loggedRun :
        StateT ((Rand →ₒ M).QueryCache) ProbComp
          (Unit × QueryLog (RO_Spec Rand M)) :=
      (simulateQ (Rand →ₒ M).romImpl.withLogging <| (show OracleComp (RO_Spec Rand M) Unit from do
        let (m₁, m₂, st) ← adv.choose pk
        let b ← $ᵗ Bool
        let h ← $ᵗ M
        let c : Rand × M := (y, h + if b then m₁ else m₂)
        let _b' ← adv.guess st c
        return ())).run
    let (_result, log) ← loggedRun.run' ∅
    match log.find? (fun entry => match entry.1 with
      | Sum.inl _ => false
      | Sum.inr r => tdp.forward pk r = y) with
    | some entry =>
        match entry.1 with
        | Sum.inl _ => return default
        | Sum.inr r => return r
    | none => return default

/-- The logged challenge interaction, including the cache threaded from selection to guessing. -/
private def challengeTranscript [AddCommGroup M] (adv : CPA_Adversary PK Rand M)
    (pk : PK) (y : Rand) : ProbComp (QueryLog (Rand →ₒ M)) := do
  let choice ← runRightLog (adv.choose pk) ∅
  let b ← $ᵗ Bool
  let h ← $ᵗ M
  let guess ← runRightLog (adv.guess choice.1.1.2.2
    (y, h + if b then choice.1.1.1 else choice.1.1.2.1)) choice.2
  return choice.1.2 ++ guess.1.2

private lemma inverter_eq [Inhabited Rand] [AddCommGroup M] (adv : CPA_Adversary PK Rand M)
    (pk : PK) (y : Rand) :
    inverter tdp adv pk y = transcriptPreimage (tdp := tdp) pk y <$>
      challengeTranscript adv pk y := by
  have projected : inverter tdp adv pk y = (do
      let x ← runRightLog (show OracleComp (RO_Spec Rand M) Unit from do
        let (m₁, m₂, st) ← adv.choose pk
        let b ← $ᵗ Bool
        let h ← $ᵗ M
        let _ ← adv.guess st (y, h + if b then m₁ else m₂)
        return ()) ∅
      return transcriptPreimage (tdp := tdp) pk y x.1.2) := by
    simp only [inverter, runRightLog, StateT.run'_eq, bind_map_left]
    apply bind_congr
    intro x
    exact match_find?_eq_pure_transcriptPreimage pk y x.1.2
  rw [projected]
  simp only [challengeTranscript, runRightLog_bind, runRightLog_lift, runRightLog_pure,
    bind_assoc, pure_bind, List.nil_append, List.append_nil, map_bind, map_pure]

/-! ### Cache and transcript

A logged run caches the hidden input `r` exactly when its transcript queries `r`
(`roSim.isCached_of_mem_support_run_withLogging`), so the bad event can be read off either the
final cache or the transcript. -/

/-- The right-oracle projection of a logged run keeps the cache/transcript correspondence. -/
private lemma isCached_of_mem_support_runRightLog {α : Type}
    (oa : OracleComp (RO_Spec Rand M) α) (r : Rand) (s : (Rand →ₒ M).QueryCache) :
    ∀ z ∈ support (runRightLog oa s),
      z.2.isCached r = (s.isCached r || z.1.2.wasQueried r) := by
  intro z hz
  rw [runRightLog, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [roSim.isCached_of_mem_support_run_withLogging oa r s y hy, wasQueried_snd]

/-- A logged BR93 run whose transcript is discarded is the plain run. -/
private lemma bind_runRightLog_of_log_unused {α β : Type}
    (oa : OracleComp (RO_Spec Rand M) α) (s : (Rand →ₒ M).QueryCache)
    (f : α → (Rand →ₒ M).QueryCache → ProbComp β) :
    (runRightLog oa s >>= fun x => f x.1.1 x.2) =
      (simulateQ (Rand →ₒ M).romImpl oa).run s >>= fun x => f x.1 x.2 := by
  rw [runRightLog, bind_map_left]
  exact QueryImpl.bind_run_run_simulateQ_withLogging _ oa s f

/-! ### Games

The games sample the challenge randomness, and all but `game2` mask a message. -/

variable [SampleableType Rand]

/-- Game 2: after replacing the challenge hash with a uniform mask, translation by the
challenge message preserves uniformity, so the challenge ciphertext no longer depends on `b`. -/
def game2 (tdp : TrapdoorPermutation PK SK Rand) (adv : CPA_Adversary PK Rand M) : ProbComp Bool :=
  do
    let b ← ($ᵗ Bool)
    let b' ← (simulateQ (Rand →ₒ M).romImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
      let (pk, _sk) ← liftM tdp.keygen
      let (_m₁, _m₂, st) ← adv.choose pk
      let r ← $ᵗ Rand
      let h ← $ᵗ M
      let c : Rand × M := (tdp.forward pk r, h)
      adv.guess st c)).run' ∅
    return (b == b')

/-- In the all-random game, the challenge ciphertext is independent of the hidden bit, so the
adversary succeeds with probability exactly `1/2`. -/
theorem evalDist_game2_eq_half (adv : CPA_Adversary PK Rand M) :
    𝒟[game2 tdp adv] {true} = 1 / 2 := by
  let f : Bool → ProbComp Bool := fun _ =>
    (simulateQ (Rand →ₒ M).romImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
      let (pk, _sk) ← liftM tdp.keygen
      let (_m₁, _m₂, st) ← adv.choose pk
      let r ← $ᵗ Rand
      let h ← $ᵗ M
      let c : Rand × M := (tdp.forward pk r, h)
      adv.guess st c)).run' ∅
  change 𝒟[do let b ← $ᵗ Bool; let b' ← f b; return decide (b = b')] {true} = 1 / 2
  exact ProbComp.evalDist_decide_eq_uniformBool_half f (by rfl)

/-- The finite-frontend form of `evalDist_game2_eq_half`. -/
theorem game2_eq_half (adv : CPA_Adversary PK Rand M) :
    Pr[= true | game2 tdp adv] = 1 / 2 := by
  simpa only [evalDist_apply_singleton] using evalDist_game2_eq_half (tdp := tdp) adv

variable [AddCommGroup M]

/-- Real one-time CPA game in the random-oracle model. -/
def cpaGame (tdp : TrapdoorPermutation PK SK Rand) (adv : CPA_Adversary PK Rand M) :
    ProbComp Bool :=
  (simulateQ (Rand →ₒ M).romImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
    let b ← $ᵗ Bool
    let (pk, _sk) ← liftM tdp.keygen
    let (m₁, m₂, st) ← adv.choose pk
    let r ← $ᵗ Rand
    let h ← (Rand →ₒ M).query r
    let c : Rand × M := (tdp.forward pk r, h + if b then m₁ else m₂)
    let b' ← adv.guess st c
    return (b == b'))).run' ∅

/-- Game 1: replace the challenge hash value with a fresh uniform mask. The adversary still
interacts with the same lazy random oracle, so this only changes the game if it queries the
hidden challenge randomness `r`. -/
def game1 (tdp : TrapdoorPermutation PK SK Rand) (adv : CPA_Adversary PK Rand M) : ProbComp Bool :=
  (simulateQ (Rand →ₒ M).romImpl <| (show OracleComp (RO_Spec Rand M) Bool from do
    let b ← $ᵗ Bool
    let (pk, _sk) ← liftM tdp.keygen
    let (m₁, m₂, st) ← adv.choose pk
    let r ← $ᵗ Rand
    let h ← $ᵗ M
    let c : Rand × M := (tdp.forward pk r, h + if b then m₁ else m₂)
    let b' ← adv.guess st c
    return (b == b'))).run' ∅

/-- Bad event for the Game 0 → Game 1 hop: the adversary queries the random oracle at the
hidden challenge randomness `r`. -/
def badEventExperiment (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adversary PK Rand M) : ProbComp Bool := do
  let loggedRun :
      StateT ((Rand →ₒ M).QueryCache) ProbComp
        (Rand × QueryLog (RO_Spec Rand M)) :=
    (simulateQ (Rand →ₒ M).romImpl.withLogging <| (show OracleComp (RO_Spec Rand M) Rand from do
      let (pk, _sk) ← liftM tdp.keygen
      let (m₁, m₂, st) ← adv.choose pk
      let b ← $ᵗ Bool
      let r ← $ᵗ Rand
      let h ← $ᵗ M
      let c : Rand × M := (tdp.forward pk r, h + if b then m₁ else m₂)
      let _b' ← adv.guess st c
      return r)).run
  let (r, log) ← loggedRun.run' ∅
  return log.wasQueried (Sum.inr r)

/-- Probability of the bad event. -/
noncomputable def badEventProb (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adversary PK Rand M) : ℝ :=
  (𝒟[badEventExperiment tdp adv] {true}).toReal

private lemma badEventExperiment_eq (adv : CPA_Adversary PK Rand M) :
    badEventExperiment tdp adv = (do
      let (pk, _) ← tdp.keygen
      let choice ← runRightLog (adv.choose pk) ∅
      let b ← $ᵗ Bool
      let r ← $ᵗ Rand
      let h ← $ᵗ M
      let guess ← runRightLog (adv.guess choice.1.1.2.2
        (tdp.forward pk r, h + if b then choice.1.1.1 else choice.1.1.2.1)) choice.2
      return (choice.1.2 ++ guess.1.2).wasQueried r) := by
  have projected : badEventExperiment tdp adv = (do
      let x ← runRightLog (show OracleComp (RO_Spec Rand M) Rand from do
        let (pk, _) ← liftM tdp.keygen
        let (m₁, m₂, st) ← adv.choose pk
        let b ← $ᵗ Bool
        let r ← $ᵗ Rand
        let h ← $ᵗ M
        let _ ← adv.guess st (tdp.forward pk r, h + if b then m₁ else m₂)
        return r) ∅
      return x.1.2.wasQueried x.1.1) := by
    simp only [badEventExperiment, runRightLog, StateT.run'_eq, bind_map_left, wasQueried_snd]
  rw [projected]
  simp only [runRightLog_bind, runRightLog_lift, runRightLog_pure, bind_assoc,
    pure_bind, List.nil_append, List.append_nil]

/-- The idealized challenge game with its bad flag: the challenge mask is fresh, and the flag
records whether the final cache holds an answer at the hidden challenge input. -/
private def idealFlagged (tdp : TrapdoorPermutation PK SK Rand)
    (adv : CPA_Adversary PK Rand M) : ProbComp (Bool × Bool) := do
  let b ← $ᵗ Bool
  let ks ← tdp.keygen
  let choice ← (simulateQ (Rand →ₒ M).romImpl (adv.choose ks.1)).run ∅
  let r ← $ᵗ Rand
  let h ← $ᵗ M
  let z ← (simulateQ (Rand →ₒ M).romImpl (adv.guess choice.1.2.2
    (tdp.forward ks.1 r, h + if b then choice.1.1 else choice.1.2.1))).run choice.2
  return (b == z.1, z.2.isCached r)

/-- Game 1 is the success marginal of the flagged idealized game. -/
private lemma game1_eq_idealFlagged (adv : CPA_Adversary PK Rand M) :
    game1 tdp adv = Prod.fst <$> idealFlagged tdp adv := by
  rw [game1, idealFlagged]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, roSim.run_liftM, bind_map_left,
    simulateQ_pure]
  simp only [StateT.run_pure, map_eq_bind_pure_comp, Function.comp, bind_assoc, pure_bind]

/-- The bad-event experiment is the flag marginal of the flagged idealized game. -/
private lemma evalDist_badEventExperiment_eq_idealFlagged (adv : CPA_Adversary PK Rand M) :
    𝒟[badEventExperiment tdp adv] = 𝒟[Prod.snd <$> idealFlagged tdp adv] := by
  have hforget : badEventExperiment tdp adv = (do
      let ks ← tdp.keygen
      let choice ← (simulateQ (Rand →ₒ M).romImpl (adv.choose ks.1)).run ∅
      let b ← $ᵗ Bool
      let r ← $ᵗ Rand
      let h ← $ᵗ M
      let z ← (simulateQ (Rand →ₒ M).romImpl (adv.guess choice.1.2.2
        (tdp.forward ks.1 r, h + if b then choice.1.1 else choice.1.2.1))).run choice.2
      return z.2.isCached r) := by
    rw [badEventExperiment_eq]
    refine bind_congr fun ks => ?_
    obtain ⟨pk, sk⟩ := ks
    dsimp only
    rw [← bind_runRightLog_of_log_unused (adv.choose pk) ∅ (fun a c => do
      let b ← $ᵗ Bool
      let r ← $ᵗ Rand
      let h ← $ᵗ M
      let z ← (simulateQ (Rand →ₒ M).romImpl (adv.guess a.2.2
        (tdp.forward pk r, h + if b then a.1 else a.2.1))).run c
      return z.2.isCached r)]
    refine bind_congr_of_forall_mem_support _ fun choice hchoice => ?_
    refine bind_congr fun b => bind_congr fun r => bind_congr fun h => ?_
    rw [← bind_runRightLog_of_log_unused _ _ (fun _ c => pure (c.isCached r))]
    refine bind_congr_of_forall_mem_support _ fun guess hguess => ?_
    rw [isCached_of_mem_support_runRightLog _ r _ guess hguess,
      isCached_of_mem_support_runRightLog _ r _ choice hchoice, QueryLog.wasQueried_append,
      QueryCache.isCached_empty, Bool.false_or]
  rw [hforget, idealFlagged]
  simp only [map_bind, map_pure]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool) tdp.keygen]
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ks _ => ?_
  exact OracleComp.evalDist_bind_bind_swap _ _ _

/-- Off the bad flag, the flagged idealized game is dominated by the real game: when the
idealized run never queries the hidden input, programming the revealed mask there is invisible. -/
private lemma evalDist_idealFlagged_good_le_cpaGame (adv : CPA_Adversary PK Rand M)
    (E : Bool → Prop) :
    𝒟[idealFlagged tdp adv >>= fun z => pure (E z.1 ∧ z.2 = false)] {True} ≤
      𝒟[cpaGame tdp adv >>= fun y => pure (E y)] {True} := by
  rw [cpaGame, idealFlagged]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, roSim.run_liftM, bind_map_left,
    simulateQ_pure, bind_assoc, pure_bind]
  simp only [StateT.run_pure, pure_bind]
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton True)
    fun b _ => OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton True)
    fun ks _ => OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton True)
    fun choice _ => OracleComp.evalDist_bind_apply_mono_of_support _ _ _
      (measurableSet_singleton True) fun r _ => ?_
  simp only [roSim.simulateQ_liftM_spec_query, randomOracle.run_eq]
  cases hcr : choice.2 r with
  | some v =>
    -- The hidden input is already cached, so the idealized run is flagged bad.
    refine le_of_eq_of_le ?_ bot_le
    refine evalDist.apply_eq_zero_of_disjoint_support _ (measurableSet_singleton True) ?_
    intro p hp
    rw [mem_support_bind_iff] at hp
    obtain ⟨h, _, hp⟩ := hp
    rw [mem_support_bind_iff] at hp
    obtain ⟨z, hz, hp⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    have hcached := QueryCache.le_def.1 (roSim.le_of_mem_support_run _ choice.2 z hz) hcr
    simp [QueryCache.isCached, hcached]
  | none =>
    simp only [bind_assoc, pure_bind]
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton True)
      fun h _ => ?_
    simp only [QueryCache.isCached, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    exact roSim.prEvent_run_uncached_le_run_cacheQuery _ r h (fun b' => E (b == b')) choice.2 hcr

/-- Both one-sided up-to-bad bounds between the real game and Game 1, as event masses. -/
private lemma evalDist_cpaGame_game1_le_badEventExperiment (adv : CPA_Adversary PK Rand M) :
    𝒟[game1 tdp adv] {true} ≤ 𝒟[badEventExperiment tdp adv] {true} + 𝒟[cpaGame tdp adv] {true} ∧
      𝒟[cpaGame tdp adv] {true} ≤
        𝒟[badEventExperiment tdp adv] {true} + 𝒟[game1 tdp adv] {true} := by
  have h1 : 𝒟[game1 tdp adv] {true} = Pr{let z ← idealFlagged tdp adv}[z.1 = true] := by
    rw [← prEvent_eq_evalDist_singleton, game1_eq_idealFlagged]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  have hb :
      𝒟[badEventExperiment tdp adv] {true} = Pr{let z ← idealFlagged tdp adv}[z.2 = true] := by
    rw [evalDist_badEventExperiment_eq_idealFlagged, ← prEvent_eq_evalDist_singleton]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  rw [h1, hb, ← prEvent_eq_evalDist_singleton (cpaGame tdp adv) true]
  have hgood := evalDist_idealFlagged_good_le_cpaGame (tdp := tdp) adv
  refine ⟨prEvent_le_prEvent_add_of_prEvent_and_not_le _ _ (fun z : Bool × Bool => z.2 = true)
      (fun z => z.1 = true) (· = true) ?_,
    prEvent_le_prEvent_add_of_prEvent_not_and_not_le _ _ (fun z : Bool × Bool => z.2 = true)
      (fun z => z.1 = true) (· = true)
      ((OracleComp.prEvent_true_eq_one _).trans_le (OracleComp.prEvent_true_eq_one _).ge) ?_⟩
  · simpa only [Bool.not_eq_true] using hgood (· = true)
  · simpa only [Bool.not_eq_true] using hgood (· = false)

/-- Up-to-bad step: replacing the challenge hash query with a fresh uniform mask changes the
game by at most the bad-event probability. -/
theorem cpaGame_gap_le_badEvent (adv : CPA_Adversary PK Rand M) :
    |(Pr[= true | cpaGame tdp adv]).toReal -
      (Pr[= true | game1 tdp adv]).toReal| ≤
      badEventProb tdp adv := by
  obtain ⟨h₁, h₀⟩ := evalDist_cpaGame_game1_le_badEventExperiment (tdp := tdp) adv
  have hfin {α : Type} [MeasurableSpace α] (mx : ProbComp α) (s : Set α) : 𝒟[mx] s ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  rw [← evalDist_apply_singleton, ← evalDist_apply_singleton, badEventProb, abs_sub_le_iff,
    sub_le_iff_le_add, sub_le_iff_le_add, ← ENNReal.toReal_add (hfin _ _) (hfin _ _),
    ← ENNReal.toReal_add (hfin _ _) (hfin _ _)]
  exact ⟨ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _ _, hfin _ _⟩) h₀,
    ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _ _, hfin _ _⟩) h₁⟩

/-- Uniform masking step for any lawful measure semantics that interprets the challenge mask
uniformly. -/
theorem evalDist_game1_eq_game2 [MeasurableSpace M] [DiscreteMeasurableSpace M]
    [MeasurableSingletonClass M] [EvalDistSemantics ProbComp]
    [LawfulEvalDistSemantics ProbComp]
    (hM : 𝒟[($ᵗ M : ProbComp M)] = ProbabilityTheory.uniformOn Set.univ)
    (adv : CPA_Adversary PK Rand M) :
    𝒟[game1 tdp adv] = 𝒟[game2 tdp adv] := by
  rw [game1, game2]
  -- Push the random-oracle simulation through both games: lifted samples become plain
  -- `ProbComp` binds, the adversary's `choose`/`guess` thread the cache, and the trailing
  -- `pure` collapses, leaving identical computations save for the challenge mask.
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, roSim.run_liftM, bind_map_left,
    simulateQ_pure, bind_assoc]
  simp only [StateT.run_pure, map_eq_bind_pure_comp, Function.comp, bind_assoc, pure_bind]
  refine evalDist_bind_congr _ _ _ fun b => ?_
  refine evalDist_bind_congr _ _ _ fun ks => ?_
  refine evalDist_bind_congr _ _ _ fun mmst => ?_
  refine evalDist_bind_congr _ _ _ fun r => ?_
  exact evalDist_bind_bijective_of_uniform ($ᵗ M : ProbComp M) hM
    (fun x => x + if b = true then mmst.1.1 else mmst.1.2.1)
    (AddGroup.addRight_bijective (if b = true then mmst.1.1 else mmst.1.2.1))
    (fun x => (simulateQ (Rand →ₒ M).romImpl
      (adv.guess mmst.1.2.2 (tdp.forward ks.1 r, x))).run mmst.2 >>= fun p => pure (b == p.1))

/-- Finite-distribution form of the uniform masking step. -/
theorem game1_eq_game2 (adv : CPA_Adversary PK Rand M) :
    𝒮[game1 tdp adv] = 𝒮[game2 tdp adv] := by
  let : MeasurableSpace M := ⊤
  let : EvalDistSemantics ProbComp := instEvalDistSemanticsOfMonadLiftTSPMF
  have hM : 𝒟[($ᵗ M : ProbComp M)] = ProbabilityTheory.uniformOn Set.univ :=
    evalDist_uniformSample
  exact evalSPMF_eq_of_evalDist_eq _ _
    (evalDist_game1_eq_game2 hM adv)

/-- One shared challenge and transcript for the bad-event and inversion observations. -/
private def challengeTranscriptExperiment (adv : CPA_Adversary PK Rand M) :
    ProbComp (PK × Rand × QueryLog (Rand →ₒ M)) := do
  let (pk, _) ← tdp.keygen
  let r ← $ᵗ Rand
  let log ← challengeTranscript adv pk (tdp.forward pk r)
  return (pk, r, log)

private lemma tdpExperiment_eq_observation [Inhabited Rand] (adv : CPA_Adversary PK Rand M) :
    tdpExperiment tdp (inverter tdp adv) = (fun x : PK × Rand × QueryLog (Rand →ₒ M) =>
      decide (tdp.forward x.1 (transcriptPreimage (tdp := tdp) x.1
        (tdp.forward x.1 x.2.1) x.2.2) = tdp.forward x.1 x.2.1)) <$>
      challengeTranscriptExperiment (tdp := tdp) adv := by
  simp only [tdpExperiment, tdpRun, inverter_eq, challengeTranscriptExperiment, map_bind, map_pure,
    bind_map_left, bind_assoc, pure_bind]

/-- The bad-event experiment observes the shared challenge transcript under any lawful
measure semantics. Only independent challenge draws are reordered. -/
private theorem measure_badEventExperiment_eq_observation
    [EvalDistSemantics ProbComp] [LawfulEvalDistSemantics ProbComp]
    (adv : CPA_Adversary PK Rand M) :
    𝒟[badEventExperiment tdp adv] = 𝒟[(fun x : PK × Rand × QueryLog (Rand →ₒ M) =>
      x.2.2.wasQueried x.2.1) <$> challengeTranscriptExperiment (tdp := tdp) adv] := by
  let : MeasurableSpace (PK × SK) := ⊤
  let : MeasurableSpace Rand := ⊤
  let : MeasurableSpace
      (((M × M × adv.State) × QueryLog (Rand →ₒ M)) × (Rand →ₒ M).QueryCache) := ⊤
  rw [badEventExperiment_eq]
  simp only [challengeTranscriptExperiment, challengeTranscript, map_bind, map_pure,
    bind_assoc, pure_bind, evalDist_bind_of_discrete tdp.keygen]
  apply MeasureTheory.Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro pksk
  exact evalDist_bind_bind_bind_rotate _ _ _ _
    (measurable_from_prod_countable_left fun _ => .of_discrete)

/-- Bad BR93 challenge transcripts are a subevent of successful trapdoor inversion.
The proof uses the shared transcript's measure and pointwise event inclusion. -/
theorem measure_badEventExperiment_le_tdpExperiment [Inhabited Rand]
    [EvalDistSemantics ProbComp] [LawfulEvalDistSemantics ProbComp]
    (adv : CPA_Adversary PK Rand M) :
    𝒟[badEventExperiment tdp adv] {true} ≤ 𝒟[tdpExperiment tdp (inverter tdp adv)] {true} := by
  let : MeasurableSpace (PK × Rand × QueryLog (Rand →ₒ M)) := ⊤
  rw [measure_badEventExperiment_eq_observation, tdpExperiment_eq_observation,
    evalDist_map_apply_of_discrete _ _ (by measurability),
    evalDist_map_apply_of_discrete _ _ (by measurability)]
  apply MeasureTheory.measure_mono
  intro x hx
  change decide (_ = _) = true
  exact decide_eq_true (forward_transcriptPreimage_of_wasQueried (tdp := tdp) x.1 x.2.1 x.2.2 hx)

/-- The bad event is bounded by the trapdoor-preimage advantage of the inverter
constructed from the adversary's random-oracle transcript. -/
theorem badEventProb_le_tdpAdvantage [Inhabited Rand] (adv : CPA_Adversary PK Rand M) :
    badEventProb tdp adv ≤ (tdpAdvantage tdp (inverter tdp adv)).toReal := by
  rw [badEventProb, tdpAdvantage]
  exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
    (measure_badEventExperiment_le_tdpExperiment (tdp := tdp) adv)

/-- Main BR93 bound for this file's custom one-time ROM CPA game: the distinguishing
bias is bounded by the trapdoor-preimage advantage via the standard up-to-bad
reduction. -/
theorem indcpa_bound [Inhabited Rand] (adv : CPA_Adversary PK Rand M) :
    |(Pr[= true | cpaGame tdp adv]).toReal - 1 / 2| ≤
      (tdpAdvantage tdp (inverter tdp adv)).toReal := by
  have hg12 : Pr[= true | game1 tdp adv] = Pr[= true | game2 tdp adv] :=
    congr_fun (congr_arg _ (game1_eq_game2 adv)) true
  calc |(Pr[= true | cpaGame tdp adv]).toReal - 1 / 2|
      = |(Pr[= true | cpaGame tdp adv]).toReal -
          (Pr[= true | game1 tdp adv]).toReal| := by
        congr 1; rw [hg12, game2_eq_half adv]; norm_num
    _ ≤ badEventProb tdp adv := cpaGame_gap_le_badEvent adv
    _ ≤ (tdpAdvantage tdp (inverter tdp adv)).toReal :=
        badEventProb_le_tdpAdvantage adv

end br93AsymmEnc

end BR93
