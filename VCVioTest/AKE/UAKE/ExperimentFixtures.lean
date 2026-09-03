/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/

module

public import VCVio.CryptoFoundations.AKE.UAKE.Defs
public import VCVioTest.AKE.UAKE.TranscriptFixtures

/-!
# UAKE Security Experiment Canaries

Toy protocols and adversaries that exercise the producers behind the UAKE
security experiment: `Party.runHonest`, `Scheme.WellFormed`, `opImpl`,
`challengeSession`, `finalize`, `Exp`, and both advantage notions.

Two schemes are used. `toy2` sends two messages, with U speaking first and T
speaking last, so `isPingPong` runs at even parity. `toy3` sends three messages,
with T speaking first and last, so `isPingPong` runs at odd parity and `.openT`
records an opening message. Neither scheme authenticates T: T's replies are
independent of `tk`, so a forging adversary wins the experiment outright.

The transcripts these runs produce are exactly the literal fixtures in
`VCVioTest.AKE.UAKE.TranscriptFixtures`, which pins the hand-written timestamps
there to the output of `recordOne` / `recordOpt` under `opImpl`.
-/

@[expose] public section

open OracleSpec OracleComp

open scoped ENNReal

namespace VCVioTest.AKE.UAKE

open _root_.AKE.UAKE

/-! ## A two-message scheme: U speaks first, T speaks last -/

def toyU2 (m : Type → Type) [Monad m] : Party m Unit ℕ (Option Bool) where
  State := Bool
  init := fun _ => pure (.speakFirst false 1)
  step := fun st w =>
    if st then pure .reject
    else if w = 2 then pure (.complete true) else pure .reject
  output := fun st => if st then pure (some (some true)) else pure none

def toyT2 (m : Type → Type) [Monad m] : Party m ℕ ℕ (Option Bool) where
  State := Bool
  init := fun _ => pure (.waitForMsg false)
  step := fun st w =>
    if st then pure .reject
    else if w = 1 then pure (.acceptAndSend true 2 true) else pure .reject
  output := fun st => if st then pure (some (some true)) else pure none

def toy2 (m : Type → Type) [Monad m] : Scheme m Bool Unit ℕ ℕ where
  rounds := 2
  setup := pure ((), 0)
  U := toyU2 m
  T := toyT2 m

/-! ## A three-message scheme: T speaks first and last -/

def toyU3 (m : Type → Type) [Monad m] : Party m Unit ℕ (Option Bool) where
  State := ℕ
  init := fun _ => pure (.waitForMsg 0)
  step := fun st w =>
    if st = 0 then (if w = 1 then pure (.acceptAndSend 1 2 false) else pure .reject)
    else if st = 1 then (if w = 3 then pure (.complete 2) else pure .reject)
    else pure .reject
  output := fun st => if st = 2 then pure (some (some true)) else pure none

def toyT3 (m : Type → Type) [Monad m] : Party m ℕ ℕ (Option Bool) where
  State := Bool
  init := fun _ => pure (.speakFirst false 1)
  step := fun st w =>
    if st then pure .reject
    else if w = 2 then pure (.acceptAndSend true 3 true) else pure .reject
  output := fun st => if st then pure (some (some true)) else pure none

def toy3 (m : Type → Type) [Monad m] : Scheme m Bool Unit ℕ ℕ where
  rounds := 3
  setup := pure ((), 0)
  U := toyU3 m
  T := toyT3 m

/-! ## Honest runs and correctness -/

theorem toy2_runHonest :
    ((toy2 Id).U.runHonest (toy2 Id).T () 0 ((toy2 Id).rounds + 1) :
        Id (Option (Option Bool) × Option (Option Bool) × List ℕ)) =
      (some (some true), some (some true), [1, 2]) := rfl

theorem toy3_runHonest :
    ((toy3 Id).U.runHonest (toy3 Id).T () 0 ((toy3 Id).rounds + 1) :
        Id (Option (Option Bool) × Option (Option Bool) × List ℕ)) =
      (some (some true), some (some true), [1, 2, 3]) := rfl

theorem toy2_correctExp : (CorrectExp (toy2 Id) : Id Bool) = true := rfl

theorem toy3_correctExp : (CorrectExp (toy3 Id) : Id Bool) = true := rfl

theorem toy2_perfectlyCorrect :
    PerfectlyCorrect (toy2 ProbComp) ProbCompRuntime.probComp := by
  unfold PerfectlyCorrect
  rw [show ProbCompRuntime.probComp.evalDist (CorrectExp (toy2 ProbComp)) =
    liftM (CorrectExp (toy2 ProbComp)) from rfl,
    show CorrectExp (toy2 ProbComp) = pure true from rfl]
  simp

theorem toy3_perfectlyCorrect :
    PerfectlyCorrect (toy3 ProbComp) ProbCompRuntime.probComp := by
  unfold PerfectlyCorrect
  rw [show ProbCompRuntime.probComp.evalDist (CorrectExp (toy3 ProbComp)) =
    liftM (CorrectExp (toy3 ProbComp)) from rfl,
    show CorrectExp (toy3 ProbComp) = pure true from rfl]
  simp

/-! ## Well-formedness -/

theorem toyU2_outputsOnlyAtCompletion : (toyU2 ProbComp).OutputsOnlyAtCompletion := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ r hr out hout
    obtain rfl := eq_of_mem_support_pure hr
    obtain rfl := eq_of_mem_support_pure hout
    rfl
  · rintro st w st' hstep out hout
    simp only [toyU2] at hstep hout
    split_ifs at hstep <;>
      first
        | exact absurd (eq_of_mem_support_pure hstep) (by simp)
        | (obtain h := eq_of_mem_support_pure hstep
           injection h with h
           subst h
           obtain rfl := eq_of_mem_support_pure hout
           simp)
  · rintro st w st' w' done hstep out hout
    simp only [toyU2] at hstep
    split_ifs at hstep <;> exact absurd (eq_of_mem_support_pure hstep) (by simp)

theorem toyT2_outputsOnlyAtCompletion : (toyT2 ProbComp).OutputsOnlyAtCompletion := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ r hr out hout
    obtain rfl := eq_of_mem_support_pure hr
    obtain rfl := eq_of_mem_support_pure hout
    rfl
  · rintro st w st' hstep out hout
    simp only [toyT2] at hstep
    split_ifs at hstep <;> exact absurd (eq_of_mem_support_pure hstep) (by simp)
  · rintro st w st' w' done hstep out hout
    simp only [toyT2] at hstep hout
    split_ifs at hstep <;>
      first
        | exact absurd (eq_of_mem_support_pure hstep) (by simp)
        | (obtain h := eq_of_mem_support_pure hstep
           injection h with hst hw hdone
           subst hst
           subst hdone
           obtain rfl := eq_of_mem_support_pure hout
           simp)

theorem toy2_wellFormed : (toy2 ProbComp).WellFormed := by
  refine ⟨toyU2_outputsOnlyAtCompletion, toyT2_outputsOnlyAtCompletion, ?_⟩
  rintro uk tk - uOut tOut ms hms
  rw [show (toy2 ProbComp).U.runHonest (toy2 ProbComp).T uk tk ((toy2 ProbComp).rounds + 1) =
    pure (some (some true), some (some true), [1, 2]) from rfl] at hms
  obtain h := eq_of_mem_support_pure hms
  injection h with _ h
  injection h with _ h
  subst h
  rfl

theorem toyU3_outputsOnlyAtCompletion : (toyU3 ProbComp).OutputsOnlyAtCompletion := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ r hr out hout
    obtain rfl := eq_of_mem_support_pure hr
    obtain rfl := eq_of_mem_support_pure hout
    rfl
  · rintro st w st' hstep out hout
    simp only [toyU3] at hstep hout
    split_ifs at hstep <;>
      first
        | exact absurd (eq_of_mem_support_pure hstep) (by simp)
        | (obtain h := eq_of_mem_support_pure hstep
           injection h with h
           subst h
           obtain rfl := eq_of_mem_support_pure hout
           simp)
  · rintro st w st' w' done hstep out hout
    simp only [toyU3] at hstep hout
    split_ifs at hstep <;>
      first
        | exact absurd (eq_of_mem_support_pure hstep) (by simp)
        | (obtain h := eq_of_mem_support_pure hstep
           injection h with hst hw hdone
           subst hst
           subst hdone
           obtain rfl := eq_of_mem_support_pure hout
           simp)

theorem toyT3_outputsOnlyAtCompletion : (toyT3 ProbComp).OutputsOnlyAtCompletion := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ r hr out hout
    obtain rfl := eq_of_mem_support_pure hr
    obtain rfl := eq_of_mem_support_pure hout
    rfl
  · rintro st w st' hstep out hout
    simp only [toyT3] at hstep
    split_ifs at hstep <;> exact absurd (eq_of_mem_support_pure hstep) (by simp)
  · rintro st w st' w' done hstep out hout
    simp only [toyT3] at hstep hout
    split_ifs at hstep <;>
      first
        | exact absurd (eq_of_mem_support_pure hstep) (by simp)
        | (obtain h := eq_of_mem_support_pure hstep
           injection h with hst hw hdone
           subst hst
           subst hdone
           obtain rfl := eq_of_mem_support_pure hout
           simp)

theorem toy3_wellFormed : (toy3 ProbComp).WellFormed := by
  refine ⟨toyU3_outputsOnlyAtCompletion, toyT3_outputsOnlyAtCompletion, ?_⟩
  rintro uk tk - uOut tOut ms hms
  rw [show (toy3 ProbComp).U.runHonest (toy3 ProbComp).T uk tk ((toy3 ProbComp).rounds + 1) =
    pure (some (some true), some (some true), [1, 2, 3]) from rfl] at hms
  obtain h := eq_of_mem_support_pure hms
  injection h with _ h
  injection h with _ h
  subst h
  rfl

/-- A malformed U role: it hands out a key straight from its initial state. -/
def outputAtInitParty : Party ProbComp Unit ℕ (Option Bool) where
  State := Bool
  init := fun _ => pure (.speakFirst false 1)
  step := fun _ _ => pure .reject
  output := fun _ => pure (some (some true))

def outputAtInitScheme : Scheme ProbComp Bool Unit ℕ ℕ where
  rounds := 2
  setup := pure ((), 0)
  U := outputAtInitParty
  T := toyT2 ProbComp

theorem not_outputsOnlyAtCompletion_outputAtInitParty :
    ¬ outputAtInitParty.OutputsOnlyAtCompletion := fun h => by
  simpa using h.1 () (.speakFirst false 1) ((mem_support_pure_iff _ _).2 rfl)
    (some (some true)) ((mem_support_pure_iff _ _).2 rfl)

theorem not_wellFormed_outputAtInitScheme : ¬ outputAtInitScheme.WellFormed := fun h =>
  not_outputsOnlyAtCompletion_outputAtInitParty h.1

/-! ## Oracle probes against `opImpl` -/

abbrev toySpec : OracleSpec (Op ℕ) := oracleSpec Bool ℕ

/-- The environment `challengeSession` builds for `toy2`: U's opening is recorded at tick 0. -/
def toy2Env (m : Type → Type) [Monad m] : Env (toy2 m) := ⟨1, ⟨false, ⟨[(1, 0)]⟩⟩, false, []⟩

/-- The environment `challengeSession` builds for `toy3`: U waits, so nothing is recorded. -/
def toy3Env (m : Type → Type) [Monad m] : Env (toy3 m) := ⟨0, ⟨(0 : ℕ), ⟨[]⟩⟩, false, []⟩

def runToy2 {α : Type} (prog : OracleComp toySpec α) (env : Env (toy2 Id)) :
    α × Env (toy2 Id) :=
  (simulateQ (opImpl (toy2 Id) 0) prog).run env

def runToy3 {α : Type} (prog : OracleComp toySpec α) (env : Env (toy3 Id)) :
    α × Env (toy3 Id) :=
  (simulateQ (opImpl (toy3 Id) 0) prog).run env

def missingSessionProbe : OracleComp toySpec ((ℕ ⊕ Unit) × Option Bool) := do
  let stepped ← query (spec := toySpec) (.stepT 7 1)
  let revealed ← query (spec := toySpec) (.revealT 7)
  pure (stepped, revealed)

theorem missingSession_run :
    runToy2 missingSessionProbe (toy2Env Id) = ((.inr (), none), toy2Env Id) := rfl

def earlyRevealProbe : OracleComp toySpec (ℕ × Option Bool) := do
  let (sid, _) ← query (spec := toySpec) .openT
  let revealed ← query (spec := toySpec) (.revealT sid)
  pure (sid, revealed)

theorem earlyReveal_run :
    runToy2 earlyRevealProbe (toy2Env Id) =
      ((0, none), ⟨1, ⟨false, ⟨[(1, 0)]⟩⟩, false, [⟨false, ⟨[]⟩, none, false⟩]⟩) := rfl

def completedSessionProbe : OracleComp toySpec (ℕ ⊕ Unit) := do
  let (sid, _) ← query (spec := toySpec) .openT
  query (spec := toySpec) (.stepT sid 1)

theorem completedSession_run :
    runToy2 completedSessionProbe (toy2Env Id) =
      (.inl 2, ⟨3, ⟨false, ⟨[(1, 0)]⟩⟩, false, [⟨true, oracle2, some (some true), false⟩]⟩) := rfl

def postCompletionProbe : OracleComp toySpec (ℕ ⊕ Unit) := do
  let (sid, _) ← query (spec := toySpec) .openT
  let _ ← query (spec := toySpec) (.stepT sid 1)
  query (spec := toySpec) (.stepT sid 1)

theorem postCompletion_run :
    runToy2 postCompletionProbe (toy2Env Id) =
      (.inr (), (runToy2 completedSessionProbe (toy2Env Id)).2) := rfl

def revealAfterCompletionProbe : OracleComp toySpec (Option Bool) := do
  let (sid, _) ← query (spec := toySpec) .openT
  let _ ← query (spec := toySpec) (.stepT sid 1)
  query (spec := toySpec) (.revealT sid)

theorem revealAfterCompletion_run :
    runToy2 revealAfterCompletionProbe (toy2Env Id) =
      (some true, ⟨3, ⟨false, ⟨[(1, 0)]⟩⟩, false, [⟨true, oracle2, some (some true), true⟩]⟩) := rfl

def rejectedChallengeProbe : OracleComp toySpec (ℕ ⊕ Unit) :=
  query (spec := toySpec) (.stepChallenge 99)

theorem rejectedChallenge_run :
    runToy2 rejectedChallengeProbe (toy2Env Id) = (.inr (), toy2Env Id) := rfl

def relayProbe : OracleComp toySpec ((ℕ ⊕ Unit) × (ℕ ⊕ Unit)) := do
  let (sid, _) ← query (spec := toySpec) .openT
  let reply ← query (spec := toySpec) (.stepT sid 1)
  let closed ← query (spec := toySpec) (.stepChallenge 2)
  pure (reply, closed)

theorem relay_run :
    runToy2 relayProbe (toy2Env Id) =
      ((.inl 2, .inr ()),
        ⟨4, ⟨true, challenge2⟩, true, [⟨true, oracle2, some (some true), false⟩]⟩) := rfl

def relay3Probe : OracleComp toySpec (Option ℕ × (ℕ ⊕ Unit) × (ℕ ⊕ Unit) × (ℕ ⊕ Unit)) := do
  let (sid, opening) ← query (spec := toySpec) .openT
  let first ← query (spec := toySpec) (.stepChallenge 1)
  let reply ← query (spec := toySpec) (.stepT sid 2)
  let closed ← query (spec := toySpec) (.stepChallenge 3)
  pure (opening, first, reply, closed)

theorem relay3_run :
    runToy3 relay3Probe (toy3Env Id) =
      ((some 1, .inl 2, .inl 3, .inr ()),
        ⟨6, ⟨(2 : ℕ), challenge3⟩, true, [⟨true, oracle3, some (some true), false⟩]⟩) := rfl

def challengeStepProbe : OracleComp toySpec (ℕ ⊕ Unit) :=
  query (spec := toySpec) (.stepChallenge 1)

theorem challengeStep_live_run :
    runToy3 challengeStepProbe (toy3Env Id) =
      (.inl 2, ⟨2, ⟨(1 : ℕ), ⟨[(1, 0), (2, 1)]⟩⟩, false, []⟩) := rfl

theorem challengeStep_frozen_run :
    runToy3 challengeStepProbe { toy3Env Id with challengeDone := true } =
      (.inr (), { toy3Env Id with challengeDone := true }) := rfl

/-! ## Adversaries -/

/-- Forges T's reply to the challenge session without opening any T session. -/
def forgeAdv : Adversary (toy2 ProbComp) where
  State := Unit
  challenge := fun _uk _opening => do
    let _ ← query (spec := toySpec) (.stepChallenge 2)
    pure ()
  post := fun _ _ => pure true

/-- Relays the challenge session through a T session, without revealing it. The guess reads the
key it can recompute from the relayed transcript. -/
def relayAdv : Adversary (toy2 ProbComp) where
  State := Unit
  challenge := fun _uk _opening => do
    let (sid, _) ← query (spec := toySpec) .openT
    match ← query (spec := toySpec) (.stepT sid 1) with
    | .inl reply => let _ ← query (spec := toySpec) (.stepChallenge reply); pure ()
    | .inr _ => pure ()
  post := fun _ Kb => pure (decide (Kb ≠ some true))

/-- Relays the challenge session and reveals the relayed T session. -/
def relayRevealAdv : Adversary (toy2 ProbComp) where
  State := Unit
  challenge := fun _uk _opening => do
    let (sid, _) ← query (spec := toySpec) .openT
    match ← query (spec := toySpec) (.stepT sid 1) with
    | .inl reply =>
        let _ ← query (spec := toySpec) (.stepChallenge reply)
        let _ ← query (spec := toySpec) (.revealT sid)
        pure ()
    | .inr _ => pure ()
  post := fun _ Kb => pure (decide (Kb ≠ some true))

/-- Sends a message the challenge session rejects, so the challenge key stays ⊥. -/
def rejectAdv : Adversary (toy2 ProbComp) where
  State := Unit
  challenge := fun _uk _opening => do
    let _ ← query (spec := toySpec) (.stepChallenge 99)
    pure ()
  post := fun _ _ => pure true

/-- Relays the three-message scheme. -/
def relay3Adv : Adversary (toy3 ProbComp) where
  State := Unit
  challenge := fun _uk _opening => do
    let (sid, _) ← query (spec := toySpec) .openT
    let _ ← query (spec := toySpec) (.stepChallenge 1)
    match ← query (spec := toySpec) (.stepT sid 2) with
    | .inl reply => let _ ← query (spec := toySpec) (.stepChallenge reply); pure ()
    | .inr _ => pure ()
  post := fun _ _ => pure true

/-- Leaves the challenge session untouched during the challenge phase, then probes it once
`finalize` has frozen it. Its guess is the probe's observation. -/
def frozenProbeAdv : Adversary (toy3 ProbComp) where
  State := Unit
  challenge := fun _uk _opening => pure ()
  post := fun _ _ => do
    let probed ← query (spec := toySpec) (.stepChallenge 1)
    pure probed.isRight

/-! ## Challenge sessions -/

def forgeResult : ChallengeResult (toy2 ProbComp) := ⟨some true, ⟨[(1, 0), (2, 1)]⟩, []⟩

def relayResult : ChallengeResult (toy2 ProbComp) := ⟨some true, challenge2, [oracle2]⟩

def rejectResult : ChallengeResult (toy2 ProbComp) := ⟨none, ⟨[(1, 0)]⟩, []⟩

def relay3Result : ChallengeResult (toy3 ProbComp) := ⟨some true, challenge3, [oracle3]⟩

def frozenProbeResult : ChallengeResult (toy3 ProbComp) := ⟨none, ⟨[]⟩, []⟩

def relayState : Unit × Env (toy2 ProbComp) × ℕ :=
  ((), ⟨4, ⟨true, challenge2⟩, true, [⟨true, oracle2, some (some true), false⟩]⟩, 0)

def relayRevealState : Unit × Env (toy2 ProbComp) × ℕ :=
  ((), ⟨4, ⟨true, challenge2⟩, true, [⟨true, oracle2, some (some true), true⟩]⟩, 0)

def relay3State : Unit × Env (toy3 ProbComp) × ℕ :=
  ((), ⟨6, ⟨(2 : ℕ), challenge3⟩, true, [⟨true, oracle3, some (some true), false⟩]⟩, 0)

theorem challengeSession_forge :
    challengeSession ProbCompLift.id forgeAdv () 0 =
      pure (forgeResult, ((), ⟨2, ⟨true, ⟨[(1, 0), (2, 1)]⟩⟩, true, []⟩, 0)) := rfl

theorem challengeSession_relay :
    challengeSession ProbCompLift.id relayAdv () 0 = pure (relayResult, relayState) := rfl

theorem challengeSession_relayReveal :
    challengeSession ProbCompLift.id relayRevealAdv () 0 =
      pure (relayResult, relayRevealState) := rfl

theorem challengeSession_reject :
    challengeSession ProbCompLift.id rejectAdv () 0 =
      pure (rejectResult, ((), ⟨1, ⟨false, ⟨[(1, 0)]⟩⟩, false, []⟩, 0)) := rfl

theorem challengeSession_relay3 :
    challengeSession ProbCompLift.id relay3Adv () 0 = pure (relay3Result, relay3State) := rfl

theorem challengeSession_frozenProbe :
    challengeSession ProbCompLift.id frozenProbeAdv () 0 =
      pure (frozenProbeResult, ((), toy3Env ProbComp, 0)) := rfl

/-! ## Ping-pong classification of the produced transcripts -/

theorem forgeResult_K0 : forgeResult.K0 = some true := rfl

theorem rejectResult_K0 : rejectResult.K0 = none := rfl

theorem isPingPong_forgeResult : isPingPong forgeResult = false := by decide

theorem isPingPong_relayResult : isPingPong relayResult = true := by decide

theorem isPingPong_relay3Result : isPingPong relay3Result = true := by decide

theorem fullPingPong_relay : fullPingPong relayState.2.1.tSessions relayResult = false := by decide

theorem fullPingPong_relayReveal :
    fullPingPong relayRevealState.2.1.tSessions relayResult = true := by decide

/-! ## The experiment and its advantage branches -/

theorem probOutput_probComp_evalDist {α : Type} (oa : ProbComp α) (x : α) :
    Pr[= x | ProbCompRuntime.probComp.evalDist oa] = Pr[= x | oa] := rfl

theorem Exp_forge : Exp ProbCompLift.id forgeAdv = (do let _ ← ($ᵗ Bool); pure true) := rfl

theorem Exp_relay :
    Exp ProbCompLift.id relayAdv =
      (do
        let b ← ($ᵗ Bool)
        let k ← ($ᵗ Bool)
        pure (decide ((if b then some k else some true) ≠ some true) == b)) := rfl

theorem Exp_relayReveal :
    Exp ProbCompLift.id relayRevealAdv =
      (do let _ ← ($ᵗ Bool); let _ ← ($ᵗ Bool); ($ᵗ Bool)) := rfl

theorem Exp_reject :
    Exp ProbCompLift.id rejectAdv = (do let b ← ($ᵗ Bool); pure (true == b)) := rfl

theorem Exp_frozenProbe :
    Exp ProbCompLift.id frozenProbeAdv = (do let b ← ($ᵗ Bool); pure (true == b)) := rfl

theorem finalize_relay_real (K1 : Option Bool) :
    finalize ProbCompLift.id relayAdv relayState relayResult false K1 = pure true := rfl

theorem finalize_relay_random (k : Bool) :
    finalize ProbCompLift.id relayAdv relayState relayResult true (some k) = pure (!k) := by
  cases k <;> rfl

theorem finalize_relayReveal (b : Bool) (K1 : Option Bool) :
    finalize ProbCompLift.id relayRevealAdv relayRevealState relayResult b K1 = ($ᵗ Bool) := rfl

theorem finalize_frozenProbe (b : Bool) :
    finalize ProbCompLift.id frozenProbeAdv ((), toy3Env ProbComp, 0) frozenProbeResult b none =
      pure (true == b) := rfl

theorem probOutput_Exp_forge : Pr[= true | Exp ProbCompLift.id forgeAdv] = 1 := by
  rw [Exp_forge]
  simp

theorem probOutput_Exp_relay : Pr[= true | Exp ProbCompLift.id relayAdv] = 3 / 4 := by
  have harith : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ + 2⁻¹ = 3 / 4 := by
    have hc : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    rw [ENNReal.eq_div_iff (by norm_num) (by norm_num), mul_add,
      show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_mul_mul_comm, hc, one_mul, mul_assoc, hc, mul_one]
    norm_num
  rw [Exp_relay]
  simpa [probOutput_bind_eq_sum_fintype] using harith

theorem probOutput_Exp_relayReveal :
    Pr[= true | Exp ProbCompLift.id relayRevealAdv] = 1 / 2 := by
  rw [Exp_relayReveal]
  simp

theorem probOutput_Exp_reject : Pr[= true | Exp ProbCompLift.id rejectAdv] = 1 / 2 := by
  rw [Exp_reject]
  simp

theorem probOutput_Exp_frozenProbe :
    Pr[= true | Exp ProbCompLift.id frozenProbeAdv] = 1 / 2 := by
  rw [Exp_frozenProbe]
  simp

theorem advantage_forge : advantage ProbCompRuntime.probComp forgeAdv = 1 / 2 := by
  unfold advantage
  rw [show ProbCompRuntime.probComp.toProbCompLift = ProbCompLift.id from rfl,
    probOutput_probComp_evalDist, probOutput_Exp_forge]
  norm_num

theorem advantage_relay : advantage ProbCompRuntime.probComp relayAdv = 1 / 4 := by
  unfold advantage
  rw [show ProbCompRuntime.probComp.toProbCompLift = ProbCompLift.id from rfl,
    probOutput_probComp_evalDist, probOutput_Exp_relay]
  norm_num

theorem advantage_relayReveal : advantage ProbCompRuntime.probComp relayRevealAdv = 0 := by
  unfold advantage
  rw [show ProbCompRuntime.probComp.toProbCompLift = ProbCompLift.id from rfl,
    probOutput_probComp_evalDist, probOutput_Exp_relayReveal]
  norm_num

theorem advantage_reject : advantage ProbCompRuntime.probComp rejectAdv = 0 := by
  unfold advantage
  rw [show ProbCompRuntime.probComp.toProbCompLift = ProbCompLift.id from rfl,
    probOutput_probComp_evalDist, probOutput_Exp_reject]
  norm_num

theorem boolBiasAdvantage_relayReveal :
    boolBiasAdvantage ProbCompRuntime.probComp relayRevealAdv = 0 := by
  rw [boolBiasAdvantage_eq_two_mul_advantage, advantage_relayReveal, mul_zero]

theorem boolBiasAdvantage_forge :
    boolBiasAdvantage ProbCompRuntime.probComp forgeAdv = 1 := by
  rw [boolBiasAdvantage_eq_two_mul_advantage, advantage_forge]
  norm_num

end VCVioTest.AKE.UAKE
