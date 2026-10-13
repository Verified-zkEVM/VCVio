/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.ChainHybrid
import all HashSig.GXMSS.Security.Reductions.SourceGames
import all HashSig.GXMSS.Security.Reductions.GuessingGames
import all HashSig.GXMSS.Security.Reductions.CollisionReductions
import all HashSig.GXMSS.Security.Reductions.SplicedChain
import all HashSig.GXMSS.Security.Reductions.ChainHybrid

/-!
# Joint undetectability and preimage reductions

Joint SM-DT-UD and SM-DT-PRE experiments pay for the selected Game 4 histories, including
successful, unused and failed-consumed forged epochs. The final inequalities compare returned
winning measures without conditioning on termination.
-/

public section

namespace GXMSS.Reductions

open Encoding ENNReal OracleComp OracleSpec Security TweakableHash

variable {PP T X H M R E S : Type} {h w v n radix : ℕ}

private noncomputable def jointUDExplicitProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let guess ← $ᵗ (Guess h w v)
  let j ← $ᵗ (Fin (2 ^ w - 1))
  let starts ← GXMSS.sampleStarts H h v
  let answer ← SM_DT_UD_response world (chainUDProblem hash) pp
    (hash.chainTweak (guessedEpoch guess, guessedChain guess, j))
  if j.val < (guessedPosition guess).val then
    let spliceGuess : Guess h w v :=
      (guessedEpoch guess, guessedChain guess, j)
    let out ← runSpliced hash enc K adv pp spliceGuess answer starts
    return jointChainObservation hash enc K (guess, out)
  else return false

private noncomputable def jointUDFilteredProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let guess ← $ᵗ (Guess h w v)
  let j ← $ᵗ (Fin (2 ^ w - 1))
  let starts ← GXMSS.sampleStarts H h v
  let answer ← SM_DT_UD_response world (chainUDProblem hash) pp
    (hash.chainTweak (guessedEpoch guess, guessedChain guess, j))
  if j.val < (guessedPosition guess).val then
    let spliceGuess : Guess h w v :=
      (guessedEpoch guess, guessedChain guess, j)
    let out ← runFilteredSpliced hash enc K adv pp guess spliceGuess answer starts
    return out.elim false
      (fun result => jointChainObservation hash enc K (guess, result))
  else return false

/-- Filtering the one joint UD experiment preserves its returned true mass in either world. -/
private theorem jointUDExplicit_mass_eq_filtered
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    𝒟[jointUDExplicitProgram hash enc K adv world] {true} =
      𝒟[jointUDFilteredProgram hash enc K adv world] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  unfold jointUDExplicitProgram jointUDFilteredProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro guess
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro j
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro starts
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro answer
  by_cases hj : j.val < (guessedPosition guess).val
  · simp only [hj, ↓reduceIte]
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      runSpliced_selectedMass_eq_filtered hash enc K adv pp guess
        (guessedEpoch guess, guessedChain guess, j) answer starts
  · simp only [hj, ↓reduceIte]

/-- The authoritative real UD response is exactly one sampled positive chain step. -/
private theorem jointUD_real_response_eq_chain
    [SampleableType H]
    (hash : HashInstance PP T X H h w v)
    (pp : PP) (ep : Epoch h) (i : Fin v) (j : Fin (2 ^ w - 1)) :
    SM_DT_UD_response .real (chainUDProblem hash) pp
      (hash.chainTweak (ep, i, j)) =
    (fun x => hash.chain pp ep i j.val 1 x) <$> ($ᵗ H : ProbComp H) := by
  unfold SM_DT_UD_response chainUDProblem SM_DT_UD_Problem.standalone
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply bind_congr
  intro x
  congr 1
  have hstep := hash.chain_succ pp ep i j.val 0 x (by omega)
  simpa only [Nat.add_zero, zero_add, hash.chain_zero] using hstep.symm

/-- The authoritative ideal UD response samples the digest domain uniformly. -/
private theorem jointUD_ideal_response_eq_uniform
    [SampleableType H]
    (hash : HashInstance PP T X H h w v)
    (pp : PP) (ep : Epoch h) (i : Fin v) (j : Fin (2 ^ w - 1)) :
    SM_DT_UD_response .ideal (chainUDProblem hash) pp
      (hash.chainTweak (ep, i, j)) = ($ᵗ H : ProbComp H) := by
  rfl

private def jointUDChainCutProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let guess ← $ᵗ (Guess h w v)
  let j ← $ᵗ (Fin (2 ^ w - 1))
  let starts ← GXMSS.sampleStarts H h v
  let x ← ($ᵗ H : ProbComp H)
  let answer := match world with
    | .real => hash.chain pp (guessedEpoch guess) (guessedChain guess) j.val 1 x
    | .ideal => x
  if j.val < (guessedPosition guess).val then
    let spliceGuess : Guess h w v :=
      (guessedEpoch guess, guessedChain guess, j)
    let out ← runFilteredSpliced hash enc K adv pp guess spliceGuess answer starts
    return out.elim false
      (fun result => jointChainObservation hash enc K (guess, result))
  else return false

/-- The single authoritative UD challenge has the explicit chain-cut law in both worlds. -/
private theorem jointUDFiltered_eq_chainCut
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    jointUDFilteredProgram hash enc K adv world =
      jointUDChainCutProgram hash enc K adv world := by
  unfold jointUDFilteredProgram jointUDChainCutProgram
  apply bind_congr
  intro pp
  apply bind_congr
  intro guess
  apply bind_congr
  intro j
  apply bind_congr
  intro starts
  cases world with
  | real =>
    rw [jointUD_real_response_eq_chain hash pp (guessedEpoch guess)
      (guessedChain guess) j]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  | ideal =>
    rw [jointUD_ideal_response_eq_uniform hash pp (guessedEpoch guess)
      (guessedChain guess) j]

private theorem jointUDOracles_liftComp
    [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H h w v)
    (world : SM_DT_UD_World) (pp : PP) (oa : ProbComp S)
    (state : SM_DT_UD_State T) :
    (simulateQ (SM_DT_UD_oracles world (chainUDProblem hash) pp)
      (OracleComp.liftComp oa _)).run state =
        (fun x => (x, state)) <$> oa := by
  rw [SM_DT_UD_oracles, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp

private theorem jointUDOracles_challenge
    [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H h w v)
    (world : SM_DT_UD_World) (pp : PP) (t : T) :
    (simulateQ (SM_DT_UD_oracles world (chainUDProblem hash) pp)
      (liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
        collectionSpec (chainUDProblem hash).thColl)).query (.inr (.inl t))))).run
      (([], []) : SM_DT_UD_State T) =
      (fun answer => (some answer, ([t], []))) <$>
        SM_DT_UD_response world (chainUDProblem hash) pp t := by
  rw [SM_DT_UD_oracles, QueryImpl.simulateQ_add_query_right,
    QueryImpl.add_apply_inl]
  simp [SM_DT_UD_challengeOracle, TweakFresh, TweakReserved, chainUDProblem,
    SM_DT_UD_Problem.standalone, StateT.run_bind, map_eq_bind_pure_comp]

private theorem jointUDExperiment_eq_explicit
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    SM_DT_UD_Experiment world (jointUndetectabilityReduction hash enc K hv hw adv) =
      (letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
       letI : NeZero (2 ^ w - 1) :=
         ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
       jointUDExplicitProgram hash enc K adv world) := by
  unfold SM_DT_UD_Experiment jointUndetectabilityReduction jointUDExplicitProgram udPick
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    pure_bind, bind_assoc]
  simp only [jointUDOracles_liftComp, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  simp only [jointUDOracles_challenge, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl

/-- The authoritative one-target UD game's returned true mass is the explicit filtered chain
cut, with one pre-seed challenge and the original adaptive signing law. -/
private theorem jointUDExperiment_true_eq_chainCut
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    𝒟[SM_DT_UD_Experiment world
      (jointUndetectabilityReduction hash enc K hv hw adv)] {true} =
    𝒟[jointUDChainCutProgram hash enc K adv world] {true} := by
  rw [jointUDExperiment_eq_explicit hash enc K hv hw adv world]
  exact (jointUDExplicit_mass_eq_filtered hash enc K adv world).trans
    (congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
      (jointUDFiltered_eq_chainCut hash enc K adv world))

private def prePick [NeZero v] [NeZero (2 ^ w - 1)] [SampleableType H]
    (hash : HashInstance PP T X H h w v) :
    OracleComp (unifSpec + (SM_DT_PRE_challengeSpec T H +
      collectionSpec (chainPREProblem hash).thColl)) (SingleTargetState H h w v) := do
  let guess ← OracleComp.liftComp ($ᵗ (Guess h w v)) _
  let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
  let answer ← liftM ((unifSpec + (SM_DT_PRE_challengeSpec T H +
    collectionSpec (chainPREProblem hash).thColl)).query (.inr (.inl
      (hash.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess)))))
  return ⟨guess, answer, starts⟩

/-- Executable one-target preimage reduction; the designated chain cut supplies the preimage. -/
def preimageReduction [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (advGXMSS : SchemeAdversary PP H M R h v) : SM_DT_PRE_Adversary (chainPREProblem hash) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  exact {
  State := SingleTargetState H h w v
  choose := prePick hash
  invert state pp := do
    match state.answer with
    | none => return (0, state.starts 0 0)
    | some answer =>
      let out ← runSpliced hash enc K advGXMSS pp state.guess answer state.starts
      let fallback := (0, state.starts 0 0)
      let forgery := out.forgery
      let forgedEpoch := forgery.1
      let forgedPayload := forgery.2
      let forgedMessage := forgedPayload.1
      let forgedSignature := forgedPayload.2
      let guessedPosition := guessedPosition state.guess
      match out.history forgedEpoch with
      | some (msg, some signature) =>
        match enc.value pp msg signature.randomizer forgedEpoch,
          enc.value pp forgedMessage forgedSignature.randomizer forgedEpoch with
        | some honestWord, some forgedWord =>
          match findSmallerCoordinate honestWord forgedWord with
          | some i =>
            if _hguess : guessedEpoch state.guess = forgedEpoch ∧
                guessedChain state.guess = i ∧
                guessedPosition.val + 1 = (honestWord i).val then
              match hash.findChainCut pp forgedEpoch i (forgedWord i) (honestWord i)
                  (2 ^ w - 1) (signature.ots i) (forgedSignature.ots i) with
              | some (.inl preimage) => return (0, preimage)
              | _ => return fallback
            else return fallback
          | none => return fallback
        | _, _ => return fallback
      | _ => return fallback }

private def jointPreimageWitness
    [NeZero v]
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (guess : Guess h w v) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v) : H :=
  let fallback := starts 0 0
  if jointChainObservation hash enc K (guess, out) = false then fallback
  else
    let forgery := out.forgery
    let forgedEpoch := forgery.1
    let forgedMessage := forgery.2.1
    let forgedSignature := forgery.2.2
    match forgedEpochSource out with
    | .successful msg signature =>
      match enc.value out.pk.seed msg signature.randomizer forgedEpoch,
        enc.value out.pk.seed forgedMessage forgedSignature.randomizer forgedEpoch with
      | some honestWord, some forgedWord =>
        match findSmallerCoordinate honestWord forgedWord with
        | some i =>
          match hash.findChainCut out.pk.seed forgedEpoch i (forgedWord i) (honestWord i)
              (2 ^ w - 1) (signature.ots i) (forgedSignature.ots i) with
          | some (.inl preimage) => preimage
          | _ => fallback
        | none => fallback
      | _, _ => fallback
    | .unused | .failedConsumed _ =>
      match enc.value out.pk.seed forgedMessage forgedSignature.randomizer forgedEpoch with
      | none => fallback
      | some forgedWord =>
        match findNonMaximumCoordinate forgedWord with
        | none => fallback
        | some i =>
          hash.chain out.pk.seed forgedEpoch i (forgedWord i)
            (2 ^ w - 2 - (forgedWord i).val) (forgedSignature.ots i)

/-- Every selected returned spliced win yields an actual one-target PRE preimage, including
unused and failed-consumed histories. -/
private theorem jointPreimageWitness_sound
    [NeZero v] [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runSpliced hash enc K adv pp guess answer starts))
    (hwin : jointChainObservation hash enc K (guess, out) = true) :
    (HashInstance.thf hash).eval pp
      (hash.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (hash.digestInput (jointPreimageWitness hash enc K guess starts out)) =
      answer := by
  have hseed := (runSpliced_support_keys hash enc K adv pp guess answer starts out hout).1
  cases hs : forgedEpochSource out with
  | unused =>
    obtain ⟨word, i, hword, hi, heval⟩ :=
      joint_nonSuccess_selected_preimage_sound hash enc K adv pp guess answer starts
        out hout (Or.inl hs) hwin
    simpa [jointPreimageWitness, hwin, hs, hword, hi, hseed] using heval
  | failedConsumed msg =>
    obtain ⟨word, i, hword, hi, heval⟩ :=
      joint_nonSuccess_selected_preimage_sound hash enc K adv pp guess answer starts
        out hout (Or.inr ⟨msg, hs⟩) hwin
    simpa [jointPreimageWitness, hwin, hs, hword, hi, hseed] using heval
  | successful msg sig =>
    obtain ⟨honestWord, forgedWord, i, hhonest, hforged, hi,
        preimage, hfind, heval⟩ :=
      joint_successful_selected_preimage_sound hash enc K adv pp guess answer starts
        out hout msg sig hs hwin
    simpa [jointPreimageWitness, hwin, hs, hhonest, hforged, hi, hfind, hseed]
      using heval

/-- One PRE adversary uses the successful designated cut or, for an unused or failed-consumed
selected epoch, the forged predecessor to the challenged final chain point. It issues one target
before seed reveal and uses the unchanged retry law in `runSpliced`. -/
def jointPreimageReduction [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (advGXMSS : SchemeAdversary PP H M R h v) : SM_DT_PRE_Adversary (chainPREProblem hash) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  exact {
  State := SingleTargetState H h w v
  choose := prePick hash
  invert state pp := do
    match state.answer with
    | none => return (0, state.starts 0 0)
    | some answer =>
      let out ← runSpliced hash enc K advGXMSS pp state.guess answer state.starts
      return (0, jointPreimageWitness hash enc K state.guess state.starts out) }

/-- Selected returned mass under the real one-target PRE challenge response. This direct
program is normalized to the pinned challenge game by `jointPREExperiment_eq_explicit`. -/
noncomputable def jointPRESelectedProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let guess ← $ᵗ (Guess h w v)
  let starts ← GXMSS.sampleStarts H h v
  let hidden ← $ᵗ H
  let answer := hash.thf.eval pp
    (hash.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
    (hash.digestInput hidden)
  let out ← runSpliced hash enc K adv pp guess answer starts
  return jointChainObservation hash enc K (guess, out)

private def jointTerminalFilteredProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let guess ← $ᵗ (Guess h w v)
  let starts ← GXMSS.sampleStarts H h v
  let hidden ← $ᵗ H
  let answer := hash.thf.eval pp
    (hash.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
    (hash.digestInput hidden)
  let out ← runFilteredSpliced hash enc K adv pp guess guess answer starts
  return out.elim false
    (fun result => jointChainObservation hash enc K (guess, result))

/-- The actual one-target PRE selected event equals the filtered terminal hybrid mass. -/
private theorem jointPRESelected_mass_eq_terminalFiltered
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointPRESelectedProgram hash enc K adv] {true} =
      𝒟[jointTerminalFilteredProgram hash enc K adv] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  unfold jointPRESelectedProgram jointTerminalFilteredProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro guess
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro starts
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro hidden
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    runSpliced_selectedMass_eq_filtered hash enc K adv pp guess guess
      (hash.thf.eval pp
        (hash.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
        (hash.digestInput hidden)) starts

/-- The terminal PRE challenge response is the next positive hash step at the selected cut. -/
private theorem jointPRE_terminal_answer_eq_chain
    (hash : HashInstance PP T X H h w v)
    (pp : PP) (guess : Guess h w v) (hidden : H) :
    hash.thf.eval pp
      (hash.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (hash.digestInput hidden) =
    hash.chain pp (guessedEpoch guess) (guessedChain guess)
      (guessedPosition guess).val 1 hidden := by
  have hstep := hash.chain_succ pp (guessedEpoch guess) (guessedChain guess)
    (guessedPosition guess).val 0 hidden (by omega)
  simpa only [Nat.add_zero, zero_add, hash.chain_zero] using hstep.symm

private noncomputable def jointPREExplicitProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let guess ← $ᵗ (Guess h w v)
  let starts ← GXMSS.sampleStarts H h v
  let hidden ← $ᵗ H
  let answer := hash.thf.eval pp
    (hash.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
    (hash.digestInput hidden)
  let out ← runSpliced hash enc K adv pp guess answer starts
  return decide (hash.thf.eval pp
    (hash.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
    (hash.digestInput (jointPreimageWitness hash enc K guess starts out)) = answer)

private structure JointPRETrace (PP H M R : Type) (h w v : ℕ) where
  pp : PP
  guess : Guess h w v
  starts : Epoch h → Fin v → H
  answer : H
  out : Result PP H M R h v

private def jointPRECoupledProgram
    [SampleableType H] [SampleableType R]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp (JointPRETrace PP H M R h w v) := do
  let pp ← hash.thf.seedGen
  let guess ← $ᵗ (Guess h w v)
  let starts ← GXMSS.sampleStarts H h v
  let hidden ← $ᵗ H
  let answer := hash.thf.eval pp
    (hash.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
    (hash.digestInput hidden)
  let out ← runSpliced hash enc K adv pp guess answer starts
  return ⟨pp, guess, starts, answer, out⟩

private def jointPRESelectedObservation
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (z : JointPRETrace PP H M R h w v) : Bool :=
  jointChainObservation hash enc K (z.guess, z.out)

private def jointPREWinningObservation
    [NeZero v] [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (z : JointPRETrace PP H M R h w v) : Bool :=
  decide (hash.thf.eval z.pp
    (hash.chainTweak (guessedEpoch z.guess, guessedChain z.guess,
      guessedPosition z.guess))
    (hash.digestInput (jointPreimageWitness hash enc K z.guess z.starts z.out)) = z.answer)

private theorem jointPRESelectedProgram_eq_coupled
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    jointPRESelectedProgram hash enc K adv =
      jointPRESelectedObservation hash enc K <$> jointPRECoupledProgram hash enc K adv := by
  simp [jointPRESelectedProgram, jointPRECoupledProgram,
    jointPRESelectedObservation, map_eq_bind_pure_comp, bind_assoc]

private theorem jointPREExplicitProgram_eq_coupled
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    jointPREExplicitProgram hash enc K adv =
      jointPREWinningObservation hash enc K <$> jointPRECoupledProgram hash enc K adv := by
  simp [jointPREExplicitProgram, jointPRECoupledProgram,
    jointPREWinningObservation, map_eq_bind_pure_comp, bind_assoc]

private theorem jointPRECoupledProgram_support_run
    [SampleableType H] [SampleableType R]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (z : JointPRETrace PP H M R h w v)
    (hz : z ∈ support (jointPRECoupledProgram hash enc K adv)) :
    z.out ∈ support (runSpliced hash enc K adv z.pp z.guess z.answer z.starts) := by
  simp only [jointPRECoupledProgram, mem_support_bind_iff] at hz
  obtain ⟨pp, _, guess, _, starts, _, hidden, _, out, hout, hret⟩ := hz
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst z
  exact hout

private theorem jointPRESelectedObservation_implies_winning
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (z : JointPRETrace PP H M R h w v)
    (hz : z ∈ support (jointPRECoupledProgram hash enc K adv))
    (hselected : jointPRESelectedObservation hash enc K z = true) :
    jointPREWinningObservation hash enc K z = true := by
  have hrun := jointPRECoupledProgram_support_run hash enc K adv z hz
  have hsound := jointPreimageWitness_sound hash enc K adv z.pp z.guess z.answer
    z.starts z.out hrun hselected
  simpa only [jointPREWinningObservation, decide_eq_true_eq] using hsound

private theorem jointPREOracles_liftComp
    [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (oa : ProbComp S) (state : SM_DT_PRE_State T H) :
    (simulateQ (SM_DT_PRE_oracles (chainPREProblem hash) pp)
      (OracleComp.liftComp oa _)).run state =
        (fun x => (x, state)) <$> oa := by
  rw [SM_DT_PRE_oracles, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp

private theorem jointPREOracles_challenge
    [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (pp : PP) (t : T) :
    (simulateQ (SM_DT_PRE_oracles (chainPREProblem hash) pp)
      (liftM ((unifSpec + (SM_DT_PRE_challengeSpec T H +
        collectionSpec (chainPREProblem hash).thColl)).query (.inr (.inl t))))).run
      (([], []) : SM_DT_PRE_State T H) =
      (fun hidden => (some (hash.thf.eval pp t (hash.digestInput hidden)),
        ([(t, hidden)], []))) <$> ($ᵗ H) := by
  rw [SM_DT_PRE_oracles, QueryImpl.simulateQ_add_query_right,
    QueryImpl.add_apply_inl]
  simp [SM_DT_PRE_challengeOracle, TweakFresh, TweakReserved, chainPREProblem,
    SM_DT_PRE_Problem.standalone, StateT.run_bind, map_eq_bind_pure_comp]

private theorem jointPREExperiment_eq_explicit
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    SM_DT_PRE_Experiment (jointPreimageReduction hash enc K hv hw adv) =
      jointPREExplicitProgram hash enc K adv := by
  unfold SM_DT_PRE_Experiment jointPreimageReduction jointPREExplicitProgram prePick
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    pure_bind, bind_assoc]
  simp only [jointPREOracles_liftComp, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  simp only [jointPREOracles_challenge, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl

/-- The selected one-target event is bounded by the actual PRE experiment, with its
unconditioned returned measure and the unchanged optional signing interaction. -/
theorem jointPRESelectedMass_le_preimageAdvantage
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointPRESelectedProgram hash enc K adv] {true} ≤
      SM_DT_PRE_Advantage (jointPreimageReduction hash enc K hv hw adv) := by
  rw [jointPRESelectedProgram_eq_coupled]
  change _ ≤ 𝒟[SM_DT_PRE_Experiment
    (jointPreimageReduction hash enc K hv hw adv)] {true}
  rw [jointPREExperiment_eq_explicit hash enc K hv hw adv,
    jointPREExplicitProgram_eq_coupled]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (jointPRECoupledProgram hash enc K adv)
    (fun z => pure (jointPRESelectedObservation hash enc K z))
    (fun z => pure (jointPREWinningObservation hash enc K z))
    (measurableSet_singleton true)
  intro z hz
  by_cases hsel : jointPRESelectedObservation hash enc K z = true
  · rw [jointPRESelectedObservation_implies_winning hash enc K adv z hz hsel]
    simp [hsel]
  · have hfalse : jointPRESelectedObservation hash enc K z = false := by
      cases h : jointPRESelectedObservation hash enc K z <;> simp_all
    simp [hfalse]

private theorem bind_true_mass_telescope {α : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (draw : ProbComp α)
    (source ideal terminal real : α → ProbComp Bool) (n : ℕ)
    (h : ∀ a,
      𝒟[source a] {true} + (n : ℝ≥0∞) * 𝒟[ideal a] {true} =
        𝒟[terminal a] {true} + (n : ℝ≥0∞) * 𝒟[real a] {true}) :
    𝒟[draw >>= source] {true} + (n : ℝ≥0∞) * 𝒟[draw >>= ideal] {true} =
      𝒟[draw >>= terminal] {true} + (n : ℝ≥0∞) * 𝒟[draw >>= real] {true} := by
  simp only [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (measurableSet_singleton true)
      Measurable.of_discrete.aemeasurable]
  rw [← MeasureTheory.lintegral_const_mul _ (Measurable.of_discrete :
      Measurable fun a : α => 𝒟[ideal a] {true}),
    ← MeasureTheory.lintegral_add_left (Measurable.of_discrete :
      Measurable fun a : α => 𝒟[source a] {true})]
  rw [← MeasureTheory.lintegral_const_mul _ (Measurable.of_discrete :
      Measurable fun a : α => 𝒟[real a] {true}),
    ← MeasureTheory.lintegral_add_left (Measurable.of_discrete :
      Measurable fun a : α => 𝒟[terminal a] {true})]
  exact MeasureTheory.lintegral_congr fun a => h a

private theorem joint_fixed_selector_returned_measure_telescope
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v) :
    let n := 2 ^ w - 1
    let ep := guessedEpoch guess
    let i := guessedChain guess
    let g := (guessedPosition guess).val
    let cut : ℕ → Guess h w v := fun j => (ep, i, Fin.ofNat n j)
    let event : Option (Result PP H M R h v) → Bool := fun out => out.elim false
      (fun result => jointChainObservation hash enc K (guess, result))
    let source : ProbComp Bool := do
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let out ← runFilteredSpliced hash enc K adv pp guess (cut 0)
        (hash.chain pp ep i 0 1 x) starts
      return event out
    let terminal : ProbComp Bool := do
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let out ← runFilteredSpliced hash enc K adv pp guess guess
        (hash.chain pp ep i g 1 x) starts
      return event out
    let selected : SM_DT_UD_World → ProbComp Bool := fun world => do
      let j ← ($ᵗ (Fin n) : ProbComp (Fin n))
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let answer := match world with
        | .real => hash.chain pp ep i j.val 1 x
        | .ideal => x
      if j.val < g then
        let out ← runFilteredSpliced hash enc K adv pp guess (cut j.val) answer starts
        return event out
      else return false
    𝒟[source] {true} + (n : ℝ≥0∞) * 𝒟[selected .ideal] {true} =
      𝒟[terminal] {true} + (n : ℝ≥0∞) * 𝒟[selected .real] {true} := by
  let n := 2 ^ w - 1
  let ep := guessedEpoch guess
  let i := guessedChain guess
  let g := (guessedPosition guess).val
  let cut : ℕ → Guess h w v := fun j => (ep, i, Fin.ofNat n j)
  let event : Option (Result PP H M R h v) → Bool := fun out => out.elim false
    (fun result => jointChainObservation hash enc K (guess, result))
  let real : ℕ → ℝ≥0∞ := fun j => 𝒟[do
    let starts ← GXMSS.sampleStarts H h v
    let x ← ($ᵗ H : ProbComp H)
    let out ← runFilteredSpliced hash enc K adv pp guess (cut j)
      (hash.chain pp ep i j 1 x) starts
    return event out] {true}
  let ideal : ℕ → ℝ≥0∞ := fun j => 𝒟[do
    let starts ← GXMSS.sampleStarts H h v
    let x ← ($ᵗ H : ProbComp H)
    let out ← runFilteredSpliced hash enc K adv pp guess (cut j) x starts
    return event out] {true}
  have htelescope : real 0 + ∑ j ∈ Finset.range g, ideal j =
      real g + ∑ j ∈ Finset.range g, real j := by
    simpa only [real, ideal, n, ep, i, g, cut, event] using
      fixed_selector_filtered_hybrid_telescope hash enc K adv pp guess
  have hg : g ≤ n := by
    have := (guessedPosition guess).isLt
    omega
  have hcutg : cut g = guess := by
    rcases guess with ⟨epoch, chain, position⟩
    change (epoch, chain, Fin.ofNat n position.val) = (epoch, chain, position)
    simp only [Prod.mk.injEq, true_and]
    apply Fin.ext
    change position.val % (2 ^ w - 1) = position.val
    exact Nat.mod_eq_of_lt position.isLt
  have hideal :
      𝒟[do
        let j ← ($ᵗ (Fin n) : ProbComp (Fin n))
        let starts ← GXMSS.sampleStarts H h v
        let x ← ($ᵗ H : ProbComp H)
        if j.val < g then
          let out ← runFilteredSpliced hash enc K adv pp guess (cut j.val) x starts
          return event out
        else return false] {true} =
        (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range g, ideal j := by
    apply uniform_fin_prefix_true_mass_of_pointwise n g hg _ ideal
    intro j
    by_cases hj : j.val < g
    · simp only [hj, ↓reduceIte, ideal]
    · simp only [hj, ↓reduceIte]
      simp only [OracleComp.evalDist_bind_const, evalDist_pure]
      simp
  have hreal :
      𝒟[do
        let j ← ($ᵗ (Fin n) : ProbComp (Fin n))
        let starts ← GXMSS.sampleStarts H h v
        let x ← ($ᵗ H : ProbComp H)
        if j.val < g then
          let out ← runFilteredSpliced hash enc K adv pp guess (cut j.val)
            (hash.chain pp ep i j.val 1 x) starts
          return event out
        else return false] {true} =
        (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range g, real j := by
    apply uniform_fin_prefix_true_mass_of_pointwise n g hg _ real
    intro j
    by_cases hj : j.val < g
    · simp only [hj, ↓reduceIte, real]
    · simp only [hj, ↓reduceIte]
      simp only [OracleComp.evalDist_bind_const, evalDist_pure]
      simp
  change real 0 + (n : ℝ≥0∞) * _ = _ + (n : ℝ≥0∞) * _
  rw [hideal, hreal]
  convert finite_chain_hybrid_mean_telescope real ideal n g htelescope using 1
  simp only [real, ep, i, g, event, hcutg]

/-- The one joint returned-measure identity across the entire seed, selector, start and cut
sampling law. All four terms retain returned false and unreturned mass. -/
private theorem joint_outer_returned_measure_telescope
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointZeroRealProgram hash enc K adv] {true} +
      (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        𝒟[jointUDChainCutProgram hash enc K adv .ideal] {true} =
    𝒟[jointTerminalFilteredProgram hash enc K adv] {true} +
      (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        𝒟[jointUDChainCutProgram hash enc K adv .real] {true} := by
  let : MeasurableSpace PP := ⊤
  rw [jointZeroRealProgram_eq_normalized hash enc K adv]
  unfold jointZeroRealNormalized jointTerminalFilteredProgram jointUDChainCutProgram
  let sourcePP (pp : PP) : ProbComp Bool := do
    let guess ← $ᵗ (Guess h w v)
    let starts ← GXMSS.sampleStarts H h v
    let x ← ($ᵗ H : ProbComp H)
    let zero : Guess h w v :=
      (guessedEpoch guess, guessedChain guess,
        ⟨0, Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))⟩)
    let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x
    let out ← runFilteredSpliced hash enc K adv pp guess zero answer starts
    return out.elim false
      (fun result => jointChainObservation hash enc K (guess, result))
  let selectedPP (world : SM_DT_UD_World) (pp : PP) : ProbComp Bool := do
    let guess ← $ᵗ (Guess h w v)
    let j ← $ᵗ (Fin (2 ^ w - 1))
    let starts ← GXMSS.sampleStarts H h v
    let x ← ($ᵗ H : ProbComp H)
    let answer := match world with
      | .real => hash.chain pp (guessedEpoch guess) (guessedChain guess) j.val 1 x
      | .ideal => x
    if j.val < (guessedPosition guess).val then
      let spliceGuess : Guess h w v :=
        (guessedEpoch guess, guessedChain guess, j)
      let out ← runFilteredSpliced hash enc K adv pp guess spliceGuess answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (guess, result))
    else return false
  let terminalPP (pp : PP) : ProbComp Bool := do
    let guess ← $ᵗ (Guess h w v)
    let starts ← GXMSS.sampleStarts H h v
    let hidden ← $ᵗ H
    let answer := hash.thf.eval pp
      (hash.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (hash.digestInput hidden)
    let out ← runFilteredSpliced hash enc K adv pp guess guess answer starts
    return out.elim false
      (fun result => jointChainObservation hash enc K (guess, result))
  change 𝒟[hash.thf.seedGen >>= sourcePP] {true} +
    (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
      𝒟[hash.thf.seedGen >>= selectedPP .ideal] {true} =
    𝒟[hash.thf.seedGen >>= terminalPP] {true} +
      (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        𝒟[hash.thf.seedGen >>= selectedPP .real] {true}
  apply bind_true_mass_telescope hash.thf.seedGen sourcePP (selectedPP .ideal)
    terminalPP (selectedPP .real) (2 ^ w - 1)
  intro pp
  apply bind_true_mass_telescope
    ($ᵗ (Guess h w v) : ProbComp (Guess h w v)) _ _ _ _ (2 ^ w - 1)
  intro guess
  have hfin (j : Fin (2 ^ w - 1)) : Fin.ofNat (2 ^ w - 1) j.val = j := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt j.isLt
  have hzero : Fin.ofNat (2 ^ w - 1) 0 =
      (⟨0, Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))⟩ : Fin (2 ^ w - 1)) := by
    apply Fin.ext
    simp [Fin.ofNat]
  simpa only [jointPRE_terminal_answer_eq_chain hash pp guess, hfin, hzero] using
    joint_fixed_selector_returned_measure_telescope hash enc K adv pp guess

/-- The joint finite-index returned-measure bridge. The theorem below proves this proposition
from the zero-real source law, filtered UD worlds, terminal PRE selected mass, and the finite
hybrid telescope. -/
@[expose] def JointChainHybridReturnedMeasureBridge
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) : Prop :=
  jointChainAdvantage hash enc K hv hw adv ≤
    (↑(2 ^ w - 1) : ℝ≥0∞) *
      SM_DT_UD_Advantage (jointUndetectabilityReduction hash enc K hv hw adv) +
      𝒟[jointPRESelectedProgram hash enc K adv] {true}

/-- The native returned-mass telescope charges all selected Game 4 histories to one joint UD
distance and the exact selected mass of the one joint PRE experiment. -/
theorem jointChainAdvantage_le_jointUD_add_jointPRESelected
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    jointChainAdvantage hash enc K hv hw adv ≤
      (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (jointUndetectabilityReduction hash enc K hv hw adv) +
        𝒟[jointPRESelectedProgram hash enc K adv] {true} := by
  let n := 2 ^ w - 1
  let ud := jointUndetectabilityReduction hash enc K hv hw adv
  have hreal :
      𝒟[SM_DT_UD_Experiment .real ud] {true} =
        𝒟[jointUDChainCutProgram hash enc K adv .real] {true} :=
    jointUDExperiment_true_eq_chainCut hash enc K hv hw adv .real
  have hideal :
      𝒟[SM_DT_UD_Experiment .ideal ud] {true} =
        𝒟[jointUDChainCutProgram hash enc K adv .ideal] {true} :=
    jointUDExperiment_true_eq_chainCut hash enc K hv hw adv .ideal
  have hdist :
      𝒟[jointUDChainCutProgram hash enc K adv .real] {true} ≤
        𝒟[jointUDChainCutProgram hash enc K adv .ideal] {true} +
          SM_DT_UD_Advantage ud := by
    have h := MeasureTheory.Measure.apply_true_le_add_boolDist
      𝒟[SM_DT_UD_Experiment .real ud] 𝒟[SM_DT_UD_Experiment .ideal ud]
    rw [hreal, hideal] at h
    simpa only [SM_DT_UD_Advantage] using h
  have hfinite : (n : ℝ≥0∞) *
      𝒟[jointUDChainCutProgram hash enc K adv .ideal] {true} ≠ ∞ := by
    have hle : (n : ℝ≥0∞) *
        𝒟[jointUDChainCutProgram hash enc K adv .ideal] {true} ≤ n := by
      calc
        _ ≤ (n : ℝ≥0∞) * 1 := by
          gcongr
          exact evalDist_apply_le_one (jointUDChainCutProgram hash enc K adv .ideal) {true}
        _ = n := mul_one _
    exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) hle
  have hselected := finite_hybrid_boolDist_bound
    (𝒟[jointZeroRealProgram hash enc K adv] {true})
    (𝒟[jointTerminalFilteredProgram hash enc K adv] {true})
    (𝒟[jointUDChainCutProgram hash enc K adv .real] {true})
    (𝒟[jointUDChainCutProgram hash enc K adv .ideal] {true})
    (SM_DT_UD_Advantage ud) n hfinite
    (joint_outer_returned_measure_telescope hash enc K adv) hdist
  calc
    jointChainAdvantage hash enc K hv hw adv =
        𝒟[jointZeroRealProgram hash enc K adv] {true} :=
      jointChainAdvantage_eq_zeroReal hash enc K hv hw adv
    _ ≤ 𝒟[jointTerminalFilteredProgram hash enc K adv] {true} +
          (n : ℝ≥0∞) * SM_DT_UD_Advantage ud := hselected
    _ = 𝒟[jointPRESelectedProgram hash enc K adv] {true} +
          (n : ℝ≥0∞) * SM_DT_UD_Advantage ud := by
      rw [jointPRESelected_mass_eq_terminalFiltered hash enc K adv]
    _ = _ := by
      ac_rfl

/-- The previously stated hybrid bridge follows from the native returned-mass equality. -/
theorem jointChainHybridReturnedMeasureBridge
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    JointChainHybridReturnedMeasureBridge hash enc K hv hw adv := by
  unfold JointChainHybridReturnedMeasureBridge
  have hcoeff : (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) = (2 ^ w - 1 : ℝ≥0∞) := by
    simp only [ENNReal.natCast_sub, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  simpa only [hcoeff] using
    jointChainAdvantage_le_jointUD_add_jointPRESelected hash enc K hv hw adv

/-- One joint UD charge and one joint PRE charge pay every selected returned Game 4 history,
including successful, unused and failed-consumed epochs. -/
theorem jointChainAdvantage_le_jointUD_add_jointPRE
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    jointChainAdvantage hash enc K hv hw adv ≤
      (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (jointUndetectabilityReduction hash enc K hv hw adv) +
        SM_DT_PRE_Advantage (jointPreimageReduction hash enc K hv hw adv) := by
  calc
    jointChainAdvantage hash enc K hv hw adv ≤
        (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (jointUndetectabilityReduction hash enc K hv hw adv) +
          𝒟[jointPRESelectedProgram hash enc K adv] {true} :=
      jointChainAdvantage_le_jointUD_add_jointPRESelected hash enc K hv hw adv
    _ ≤ _ := by
      gcongr
      exact jointPRESelectedMass_le_preimageAdvantage hash enc K hv hw adv

end GXMSS.Reductions
