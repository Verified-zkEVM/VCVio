/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.ChainSource
import all HashSig.GXMSS.Security.Interval.Reductions.ChainSource
import HashSig.GXMSS.Security.Interval.Reductions.ChainPrograms
import HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import HashSig.GXMSS.Security.Interval.Reductions.FilteredView
import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import VCVio.OracleComp.EvalDist.Sum

/-!
# Native selected interval chain hybrids

The named original-domain reductions retain actual public-seed and challenge sampling. A single
source resampling and filtered finite telescope relates returned source mass to the terminal PRE
event and the two UD worlds without normalizing failed or missing outcomes.
-/

public section
namespace GXMSS.Interval.Reductions.Chain
open IncomparableEncoding ENNReal OracleComp OracleSpec TweakableHash
  GXMSS.Reductions GXMSS.Interval.Reductions GXMSS.IntervalMerkle SyncSignatureUnforgeability
variable {PP T X H M R : Type} {h w v : ℕ}

/-- Final-chain predecessor algebra, independent of roots, paths, encodings and histories. -/
private theorem chainFinalPredecessor_sound
    (hash : HashInstance PP T X H h w v) (pp : PP) (epoch : Epoch h) (chain : Fin v)
    (digit : Fin (2 ^ w)) (position : Fin (2 ^ w - 1)) (ots answer : H)
    (hsmall : digit.val < 2 ^ w - 1) (hfinal : position.val + 1 = 2 ^ w - 1)
    (hendpoint : hash.chain pp epoch chain digit (2 ^ w - 1 - digit.val) ots = answer) :
    hash.thf.eval pp (hash.chainTweak (epoch, chain, position))
      (hash.digestInput (hash.chain pp epoch chain digit (2 ^ w - 2 - digit.val) ots)) =
      answer := by
  have hlen : digit.val + (2 ^ w - 2 - digit.val) + 1 ≤ 2 ^ w - 1 := by omega
  have hstep := hash.chain_succ pp epoch chain digit (2 ^ w - 2 - digit.val) ots hlen
  have hcount : 2 ^ w - 2 - digit.val + 1 = 2 ^ w - 1 - digit.val := by omega
  rw [hcount] at hstep
  have hposition : (⟨digit.val + (2 ^ w - 2 - digit.val), by omega⟩ :
      Fin (2 ^ w - 1)) = position := by
    apply Fin.ext
    change digit.val + (2 ^ w - 2 - digit.val) = position.val
    omega
  rw [hposition] at hstep
  exact hstep.symm.trans hendpoint

/-- A strict earlier digit supplies the predecessor at a designated honest cut, using only
chain recurrence and the concrete cut equality. -/
private theorem chainCutPredecessor_sound [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (pp : PP) (epoch : Epoch h) (chain : Fin v)
    (forgedDigit honestDigit : Fin (2 ^ w)) (position : Fin (2 ^ w - 1))
    (honestOTS forgedOTS : H) (hsmaller : forgedDigit.val < honestDigit.val)
    (hposition : position.val + 1 = honestDigit.val)
    (hcut : hash.chain pp epoch chain forgedDigit
      (honestDigit.val - forgedDigit.val) forgedOTS = honestOTS) :
    ∃ preimage : H,
      hash.findChainCut pp epoch chain forgedDigit honestDigit (2 ^ w - 1)
        honestOTS forgedOTS = some (.inl preimage) ∧
      hash.thf.eval pp (hash.chainTweak (epoch, chain, position))
        (hash.digestInput preimage) = honestOTS := by
  let preimage := hash.chain pp epoch chain forgedDigit
    (honestDigit.val - forgedDigit.val - 1) forgedOTS
  have hfind : hash.findChainCut pp epoch chain forgedDigit honestDigit (2 ^ w - 1)
      honestOTS forgedOTS = some (.inl preimage) := by
    simp [HashInstance.findChainCut_eq, preimage, hcut]
  have hlen : forgedDigit.val + (honestDigit.val - forgedDigit.val - 1) + 1 ≤
      2 ^ w - 1 := by
    have := honestDigit.isLt
    omega
  have hstep := hash.chain_succ pp epoch chain forgedDigit
    (honestDigit.val - forgedDigit.val - 1) forgedOTS hlen
  have hcount : honestDigit.val - forgedDigit.val - 1 + 1 =
      honestDigit.val - forgedDigit.val := by omega
  rw [hcount] at hstep
  have hpos : (⟨forgedDigit.val + (honestDigit.val - forgedDigit.val - 1), by omega⟩ :
      Fin (2 ^ w - 1)) = position := by
    apply Fin.ext
    change forgedDigit.val + (honestDigit.val - forgedDigit.val - 1) = position.val
    omega
  rw [hpos] at hstep
  exact ⟨preimage, hfind, hstep.symm.trans hcut⟩

private noncomputable def chainUDExplicitProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let guess := activeGuess I selector
    let response ← SM_DT_UD_response world (chainUDProblem P) pp
      (P.chainTweak (guessedEpoch guess, guessedChain guess, hybrid))
    if hybrid.val < (guessedPosition guess).val then
      let splice : Guess h w v := (guessedEpoch guess, guessedChain guess, hybrid)
      let out ← runContextSpliced P enc K (intervalChainContext P I fillers)
        A pp splice response starts
      pure (intervalSelectedChainObservation P enc K I fillers guess out)
    else pure false

private noncomputable def chainUDFilteredProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let guess := activeGuess I selector
    let response ← SM_DT_UD_response world (chainUDProblem P) pp
      (P.chainTweak (guessedEpoch guess, guessedChain guess, hybrid))
    if hybrid.val < (guessedPosition guess).val then
      let splice : Guess h w v := (guessedEpoch guess, guessedChain guess, hybrid)
      let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
        A pp guess splice response starts
      pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))
    else pure false

private noncomputable def chainUDChainCutProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let guess := activeGuess I selector
    let x ← ($ᵗ H : ProbComp H)
    let response := match world with
      | .real => P.chain pp (guessedEpoch guess) (guessedChain guess) hybrid.val 1 x
      | .ideal => x
    if hybrid.val < (guessedPosition guess).val then
      let splice : Guess h w v := (guessedEpoch guess, guessedChain guess, hybrid)
      let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
        A pp guess splice response starts
      pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))
    else pure false

private theorem chainUDOracles_liftComp
    [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v)
    (world : SM_DT_UD_World) (pp : PP) {S : Type} (oa : ProbComp S)
    (state : SM_DT_UD_State T) :
    (simulateQ (SM_DT_UD_oracles world (chainUDProblem P) pp)
      (OracleComp.liftComp oa _)).run state =
        (fun x => (x, state)) <$> oa := by
  rw [SM_DT_UD_oracles, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp

private theorem chainUDOracles_challenge
    [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v)
    (world : SM_DT_UD_World) (pp : PP) (t : T) :
    (simulateQ (SM_DT_UD_oracles world (chainUDProblem P) pp)
      (liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
        collectionSpec (chainUDProblem P).thColl)).query (.inr (.inl t))))).run
      (([], []) : SM_DT_UD_State T) =
      (fun answer => (some answer, ([t], []))) <$>
        SM_DT_UD_response world (chainUDProblem P) pp t := by
  rw [SM_DT_UD_oracles, QueryImpl.simulateQ_add_query_right,
    QueryImpl.add_apply_inl]
  simp [SM_DT_UD_challengeOracle, TweakFresh, TweakReserved, chainUDProblem,
    SM_DT_UD_Problem.standalone, StateT.run_bind, map_eq_bind_pure_comp]

private theorem chainUDExperiment_eq_explicit
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    SM_DT_UD_Experiment world (chainUndetectabilityReduction P enc K I hv hw A) =
      (letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
       letI : NeZero (2 ^ w - 1) := ⟨by
         have := Nat.one_lt_two_pow (by omega : w ≠ 0)
         omega⟩
       chainUDExplicitProgram P enc K I A world) := by
  unfold SM_DT_UD_Experiment chainUndetectabilityReduction chainUDExplicitProgram chainUDPick
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    pure_bind, bind_assoc]
  simp only [chainUDOracles_liftComp, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  simp only [chainUDOracles_challenge, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl

private theorem chainUDExplicit_mass_eq_filtered
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) :
    𝒟[chainUDExplicitProgram P enc K I A world] {true} =
      𝒟[chainUDFilteredProgram P enc K I A world] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  unfold chainUDExplicitProgram chainUDFilteredProgram
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro pp _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro selector _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro hybrid _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro starts _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro fillers _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro response _
  let guess := activeGuess I selector
  by_cases hj : hybrid.val < (guessedPosition guess).val
  · simp only [show activeGuess I selector = guess from rfl, hj, ↓reduceIte]
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      intervalSelectedSplice_mass_eq_filtered P enc K I A pp fillers guess
        (guessedEpoch guess, guessedChain guess, hybrid) response starts
  · simp only [show activeGuess I selector = guess from rfl, hj, ↓reduceIte]

private theorem chainUDFiltered_mass_eq_chainCut
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) :
    𝒟[chainUDFilteredProgram P enc K I A world] {true} =
      𝒟[chainUDChainCutProgram P enc K I A world] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  unfold chainUDFilteredProgram chainUDChainCutProgram
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro pp _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro selector _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro hybrid _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro starts _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro fillers _
  let guess := activeGuess I selector
  let continuation : H → ProbComp Bool := fun response =>
    if hybrid.val < (guessedPosition guess).val then do
      let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
        A pp guess (guessedEpoch guess, guessedChain guess, hybrid) response starts
      pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))
    else pure false
  cases world with
  | real =>
    exact congrArg (fun d : MeasureTheory.Measure Bool => d {true})
      (chainUD_real_response_bind_chain P pp (guessedEpoch guess) (guessedChain guess)
        hybrid continuation)
  | ideal => rfl

private theorem chainUDExperiment_true_eq_chainCut
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    𝒟[SM_DT_UD_Experiment world (chainUndetectabilityReduction P enc K I hv hw A)] {true} =
      𝒟[chainUDChainCutProgram P enc K I A world] {true} := by
  rw [chainUDExperiment_eq_explicit]
  exact (chainUDExplicit_mass_eq_filtered P enc K I A world).trans
    (chainUDFiltered_mass_eq_chainCut P enc K I A world)

private theorem intervalFinalPreimage_sound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (fillers : Fillers I H)
    (guess : Guess h w v) (response : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts))
    (hwin : intervalSelectedChainObservation P enc K I fillers guess out = true)
    (word : Codeword v (2 ^ w)) (i : Fin v)
    (hword : let pk := out.pk
      let (epoch, message, signature) := out.forgery
      enc.value pk.seed message signature.randomizer epoch = some word)
    (hi : findNonMaximumCoordinate word = some i)
    (hepoch : let (epoch, _, _) := out.forgery; guessedEpoch guess = epoch)
    (hchain : guessedChain guess = i)
    (hfinal : (guessedPosition guess).val + 1 = 2 ^ w - 1) :
    let (epoch, _, signature) := out.forgery
    TweakableHash.eval P.thf pp (P.chainTweak
      (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (P.digestInput (P.chain pp epoch i (word i)
        (2 ^ w - 2 - (word i).val) (signature.ots i))) = response := by
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history⟩
  dsimp only at hepoch
  let out : Result PP H M R h v := ⟨pk, sk, (epoch, message, signature), history⟩
  obtain ⟨hseed, hendpoints⟩ := runContextSpliced_support_keys P enc K
    (intervalChainContext P I fillers) A pp guess response starts out hout
  have hrem := hwin
  simp only [intervalSelectedChainObservation, Bool.and_eq_true] at hrem
  have hendpoint := intervalChainRemainder_endpoint_eq_forged P enc K I fillers out word
    hword hrem.1 i
  dsimp only [out] at hendpoint
  rw [hseed] at hendpoint
  have hselected : sk.endpoints epoch i = response := by
    rw [hendpoints, ← hepoch, ← hchain]
    exact splicedEndpoints_guess_final P pp guess response starts hfinal
  rw [hselected] at hendpoint
  have hsmall := findNonMaximumCoordinate_sound word hi
  have heval := chainFinalPredecessor_sound P pp epoch i (word i)
    (guessedPosition guess) (signature.ots i) response hsmall hfinal hendpoint.symm
  simpa only [hepoch, hchain] using heval

private theorem extractChainPreimageWithFallback_sound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (fillers : Fillers I H)
    (guess : Guess h w v) (response : H) (starts : Epoch h → Fin v → H) (fallback : H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts))
    (hwin : intervalSelectedChainObservation P enc K I fillers guess out = true) :
    TweakableHash.eval P.thf pp (P.chainTweak
      (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (P.digestInput (
        extractChainPreimageWithFallback P enc K I fillers guess fallback out)) = response := by
  obtain ⟨hseed, _⟩ := runContextSpliced_support_keys P enc K (intervalChainContext P I fillers)
    A pp guess response starts out hout
  have hrem := hwin
  simp only [intervalSelectedChainObservation, Bool.and_eq_true] at hrem
  rcases hrem with ⟨hrem, hsel⟩
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history⟩
  unfold intervalSelectedCut at hsel
  dsimp only at hsel
  rw [hseed] at hsel
  cases hentry : history epoch with
  | none =>
      cases hword : enc.value pp message signature.randomizer epoch with
      | none => simp [hentry, hword] at hsel
      | some word =>
        cases hi : findNonMaximumCoordinate word with
        | none => simp [hentry, hword, hi] at hsel
        | some i =>
          have hs : guessedEpoch guess = epoch ∧ guessedChain guess = i ∧
              (guessedPosition guess).val + 1 = 2 ^ w - 1 := by
            simpa [hentry, hword, hi] using hsel
          rcases hs with ⟨hepoch, hchain, hfinal⟩
          have heval := intervalFinalPreimage_sound P enc K I A pp fillers guess response starts
            (⟨pk, sk, (epoch, message, signature), history⟩ : Result PP H M R h v) hout hwin
            word i (by dsimp only; rw [hseed]; exact hword) hi hepoch hchain hfinal
          simp only [extractChainPreimageWithFallback, hwin, Bool.true_eq_false,
            ite_false, hentry]
          rw [hseed, hword]
          simp only [hi]
          exact heval
  | some entry =>
    rcases entry with ⟨first, answer⟩
    cases answer with
    | none =>
        cases hword : enc.value pp message signature.randomizer epoch with
        | none => simp [hentry, hword] at hsel
        | some word =>
          cases hi : findNonMaximumCoordinate word with
          | none => simp [hentry, hword, hi] at hsel
          | some i =>
            have hs : guessedEpoch guess = epoch ∧ guessedChain guess = i ∧
                (guessedPosition guess).val + 1 = 2 ^ w - 1 := by
              simpa [hentry, hword, hi] using hsel
            rcases hs with ⟨hepoch, hchain, hfinal⟩
            have heval := intervalFinalPreimage_sound P enc K I A pp fillers guess response starts
              (⟨pk, sk, (epoch, message, signature), history⟩ : Result PP H M R h v) hout hwin
              word i (by dsimp only; rw [hseed]; exact hword) hi hepoch hchain hfinal
            simp only [extractChainPreimageWithFallback, hwin, Bool.true_eq_false,
            ite_false, hentry]
            rw [hseed, hword]
            simp only [hi]
            exact heval
    | some honest =>
      cases hhonest : enc.value pp first honest.randomizer epoch with
      | none => simp [hentry, hhonest] at hsel
      | some honestWord =>
        cases hforged : enc.value pp message signature.randomizer epoch with
        | none => simp [hentry, hhonest, hforged] at hsel
        | some forgedWord =>
          cases hi : (Fin.find? fun j => decide (forgedWord j < honestWord j)) with
          | none => simp [hentry, hhonest, hforged, hi] at hsel
          | some i =>
            have hs : guessedEpoch guess = epoch ∧ guessedChain guess = i ∧
                (guessedPosition guess).val + 1 = (honestWord i).val := by
              simpa [hentry, hhonest, hforged, hi] using hsel
            rcases hs with ⟨hepoch, hchain, hposition⟩
            obtain ⟨wr, hsig, hwr⟩ := runContextSpliced_successful_record_signature P enc K
              (intervalChainContext P I fillers) A pp guess response starts
              (⟨pk, sk, (epoch, message, signature), history⟩ : Result PP H M R h v)
              hout epoch first honest hentry
            have hr : honest.randomizer = wr.2 := by rw [hsig]; rfl
            have hwordEq : wr.1 = honestWord := by
              have hh := hhonest
              rw [hr, hwr] at hh
              exact Option.some.inj hh
            have hsigAnswer : honest.ots i = response := by
              rw [hsig, ← hchain]
              apply contextSplicedSignatureOfWord_guess_succ P (intervalChainContext P I fillers)
                pp guess response starts (splicedEndpoints P pp guess response starts) epoch wr
                hepoch.symm
              rw [hwordEq, hchain]
              exact hposition.symm
            simp only [intervalChainRemainderObservation, Bool.and_eq_true] at hrem
            rcases hrem with ⟨_, hcut⟩
            simp only [designatedCutHolds, forgedEpochSource, hentry] at hcut
            rw [hseed] at hcut
            simp only [hhonest, hforged, hi] at hcut
            have hcutEq := of_decide_eq_true hcut
            have hsmaller := of_decide_eq_true (Fin.eq_true_of_find?_eq_some hi)
            obtain ⟨preimage, hfind, heval⟩ := chainCutPredecessor_sound P pp epoch i
              (forgedWord i) (honestWord i) (guessedPosition guess) (honest.ots i) (signature.ots i)
              hsmaller hposition hcutEq
            have heval' : TweakableHash.eval P.thf pp (P.chainTweak
                (guessedEpoch guess, guessedChain guess, guessedPosition guess))
                (P.digestInput preimage) = response := by
              simpa only [hepoch, hchain, hsigAnswer] using heval
            simp only [extractChainPreimageWithFallback, hwin, Bool.true_eq_false,
            ite_false, hentry]
            rw [hseed, hhonest, hforged]
            simp only [hi, hfind]
            exact heval'

private theorem extractChainPreimage_sound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (fillers : Fillers I H)
    (guess : Guess h w v) (response : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts))
    (hwin : intervalSelectedChainObservation P enc K I fillers guess out = true) :
    TweakableHash.eval P.thf pp (P.chainTweak
      (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (P.digestInput (extractChainPreimage P enc K I fillers guess starts out)) = response := by
  exact extractChainPreimageWithFallback_sound P enc K I A pp fillers guess response starts
    (starts (guessedEpoch guess) (guessedChain guess)) out hout hwin

private noncomputable def chainPRESelectedProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let hidden ← ($ᵗ H : ProbComp H)
    let guess := activeGuess I selector
    let tweak := P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess)
    let response := TweakableHash.eval P.thf pp tweak (P.digestInput hidden)
    let out ← runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts
    pure (intervalSelectedChainObservation P enc K I fillers guess out)

private noncomputable def chainPREFilteredProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let hidden ← ($ᵗ H : ProbComp H)
    let guess := activeGuess I selector
    let tweak := P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess)
    let response := TweakableHash.eval P.thf pp tweak (P.digestInput hidden)
    let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
      A pp guess guess response starts
    pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))

private noncomputable def chainTerminalBackProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let hidden ← ($ᵗ H : ProbComp H)
    let guess := activeGuess I selector
    let response := P.chain pp (guessedEpoch guess) (guessedChain guess)
      (guessedPosition guess).val 1 hidden
    let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
      A pp guess guess response starts
    pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))

private noncomputable def chainPREExplicitProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let hidden ← ($ᵗ H : ProbComp H)
    let guess := activeGuess I selector
    let tweak := P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess)
    let response := TweakableHash.eval P.thf pp tweak (P.digestInput hidden)
    let out ← runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts
    let preimage := extractChainPreimage P enc K I fillers guess starts out
    pure (decide (TweakableHash.eval P.thf pp tweak
      (P.digestInput preimage) = response))

private theorem chainPREOracles_liftComp
    [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (pp : PP) {S : Type}
    (oa : ProbComp S) (state : SM_DT_PRE_State T H) :
    (simulateQ (SM_DT_PRE_oracles (chainPREProblem P) pp)
      (OracleComp.liftComp oa _)).run state = (fun x => (x, state)) <$> oa := by
  rw [SM_DT_PRE_oracles, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp

private theorem chainPREOracles_challenge
    [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (pp : PP) (t : T) :
    (simulateQ (SM_DT_PRE_oracles (chainPREProblem P) pp)
      (liftM ((unifSpec + (SM_DT_PRE_challengeSpec T H +
        collectionSpec (chainPREProblem P).thColl)).query (.inr (.inl t))))).run
      (([], []) : SM_DT_PRE_State T H) =
      (fun hidden => (some (TweakableHash.eval P.thf pp t (P.digestInput hidden)),
        ([(t, hidden)], []))) <$> ($ᵗ H) := by
  rw [SM_DT_PRE_oracles, QueryImpl.simulateQ_add_query_right, QueryImpl.add_apply_inl]
  simp [SM_DT_PRE_challengeOracle, TweakFresh, TweakReserved, chainPREProblem,
    SM_DT_PRE_Problem.standalone, StateT.run_bind, map_eq_bind_pure_comp]

private theorem chainPREExperiment_eq_explicit
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    SM_DT_PRE_Experiment (selectedChainPreimageReduction P enc K I hv hw A) =
      chainPREExplicitProgram P enc K I A := by
  unfold SM_DT_PRE_Experiment selectedChainPreimageReduction chainPREExplicitProgram chainPREPick
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    pure_bind, bind_assoc]
  simp only [chainPREOracles_liftComp, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  simp only [chainPREOracles_challenge, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl

/-- The terminal selected experiment has one active target and one fixed private filler table.
Hidden inputs are uniform on the original digest subspace. -/
noncomputable def selectedPreimageExperiment
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  exact chainPRESelectedProgram P enc K I A

/-- The terminal selected mass is charged to the actual original-domain one-target PRE adversary.
The witness proof uses only chain recurrence, the concrete designated cut and native history. -/
theorem selectedPreimageMass_le_advantage
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    𝒟[selectedPreimageExperiment P enc K I hv hw A] {true} ≤
      SM_DT_PRE_Advantage (selectedChainPreimageReduction P enc K I hv hw A) := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  change 𝒟[chainPRESelectedProgram P enc K I A] {true} ≤ _
  unfold SM_DT_PRE_Advantage
  rw [chainPREExperiment_eq_explicit P enc K I hv hw A]
  unfold chainPRESelectedProgram chainPREExplicitProgram
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro pp _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro selector _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro starts _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro fillers _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro hidden _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro out hout
  let guess := activeGuess I selector
  by_cases hselected : intervalSelectedChainObservation P enc K I fillers guess out = true
  · have heval := extractChainPreimage_sound P enc K I A pp fillers guess
      (TweakableHash.eval P.thf pp
        (P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
          (P.digestInput hidden))
      starts out hout hselected
    have hwin := heval
    simp only [show activeGuess I selector = guess from rfl, hselected, hwin,
      decide_true, evalDist_pure,
      MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton true)]
    simp
  · have hfalse := Bool.eq_false_iff.mpr hselected
    simp [show activeGuess I selector = guess from rfl, hfalse]

private noncomputable def jointZeroRealProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let (pp, guess, fillers) ← jointOuterDraw P I
  let starts ← GXMSS.sampleStarts H h v
  let x ← ($ᵗ H : ProbComp H)
  let zero : Guess h w v := (guessedEpoch guess, guessedChain guess, Fin.ofNat (2 ^ w - 1) 0)
  let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers) A pp guess
    zero (P.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x) starts
  pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))

private noncomputable def jointTerminalProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let (pp, guess, fillers) ← jointOuterDraw P I
  let starts ← GXMSS.sampleStarts H h v
  let x ← ($ᵗ H : ProbComp H)
  let response := P.chain pp (guessedEpoch guess) (guessedChain guess)
    (guessedPosition guess).val 1 x
  let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
    A pp guess guess response starts
  pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))

private noncomputable def jointUDFrontProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) : ProbComp Bool := do
  let (pp, guess, fillers) ← jointOuterDraw P I
  let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
  let starts ← GXMSS.sampleStarts H h v
  let x ← ($ᵗ H : ProbComp H)
  let response := match world with
    | .real => P.chain pp (guessedEpoch guess) (guessedChain guess) hybrid.val 1 x
    | .ideal => x
  if hybrid.val < (guessedPosition guess).val then
    let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers) A pp guess
      (guessedEpoch guess, guessedChain guess, Fin.ofNat (2 ^ w - 1) hybrid.val) response starts
    pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))
  else pure false

private theorem joint_native_returned_mass_telescope
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[jointZeroRealProgram P enc K I A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) * 𝒟[jointUDFrontProgram P enc K I A .ideal] {true} =
      𝒟[jointTerminalProgram P enc K I A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) * 𝒟[jointUDFrontProgram P enc K I A .real] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  let : MeasurableSpace (PP × Guess h w v × Fillers I H) := ⊤
  unfold jointZeroRealProgram jointTerminalProgram jointUDFrontProgram
  have integrate_telescope {α : Type} [MeasurableSpace α]
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
  apply integrate_telescope (jointOuterDraw P I)
  intro z
  rcases z with ⟨pp, guess, fillers⟩
  exact context_fixed_selector_returned_measure_telescope P enc K
    (intervalChainContext P I fillers) A pp guess
    (intervalSelectedChainObservation P enc K I fillers guess)

private theorem chainUDChainCut_mass_eq_front
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) :
    𝒟[chainUDChainCutProgram P enc K I A world] {true} =
      𝒟[jointUDFrontProgram P enc K I A world] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  unfold chainUDChainCutProgram jointUDFrontProgram jointOuterDraw
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro pp _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro selector _
  let guess := activeGuess I selector
  let F : Fin (2 ^ w - 1) → (Epoch h → Fin v → H) → Fillers I H → ProbComp Bool :=
    fun hybrid starts fillers => do
      let x ← ($ᵗ H : ProbComp H)
      let response := match world with
        | .real => P.chain pp (guessedEpoch guess) (guessedChain guess) hybrid.val 1 x
        | .ideal => x
      if hybrid.val < (guessedPosition guess).val then
        let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
          A pp guess (guessedEpoch guess, guessedChain guess, hybrid) response starts
        pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))
      else pure false
  have hswap : 𝒟[do
      let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
      let starts ← GXMSS.sampleStarts H h v
      let fillers ← sampleFillers I H
      F hybrid starts fillers] =
      𝒟[do
        let fillers ← sampleFillers I H
        let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
        let starts ← GXMSS.sampleStarts H h v
        F hybrid starts fillers] := by
    calc
      _ = 𝒟[do
        let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
        let fillers ← sampleFillers I H
        let starts ← GXMSS.sampleStarts H h v
        F hybrid starts fillers] := by
          apply evalDist_bind_congr_of_support
          intro hybrid _
          exact evalDist_bind_bind_swap _ _ (fun starts fillers => F hybrid starts fillers)
      _ = _ := evalDist_bind_bind_swap _ _
        (fun hybrid fillers => GXMSS.sampleStarts H h v >>= fun starts => F hybrid starts fillers)
  have hfin (j : Fin (2 ^ w - 1)) : Fin.ofNat (2 ^ w - 1) j.val = j := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt j.isLt
  simpa only [F, guess, hfin] using congrArg (fun d : MeasureTheory.Measure Bool => d {true}) hswap

private theorem chainPRESelected_mass_eq_filtered
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[chainPRESelectedProgram P enc K I A] {true} =
      𝒟[chainPREFilteredProgram P enc K I A] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  unfold chainPRESelectedProgram chainPREFilteredProgram
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro pp _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro selector _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro starts _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro fillers _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro hidden _
  let guess := activeGuess I selector
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    intervalSelectedSplice_mass_eq_filtered P enc K I A pp fillers guess guess
      (TweakableHash.eval P.thf pp
        (P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
          (P.digestInput hidden))
        starts

private theorem chainPREFiltered_mass_eq_terminalBack
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[chainPREFilteredProgram P enc K I A] {true} =
      𝒟[chainTerminalBackProgram P enc K I A] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  unfold chainPREFilteredProgram chainTerminalBackProgram
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro pp _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro selector _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro starts _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro fillers _
  let guess := activeGuess I selector
  let continuation : H → ProbComp Bool := fun response => do
    let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
      A pp guess guess response starts
    pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))
  have hprojection := chainUD_real_response_bind_chain P pp (guessedEpoch guess)
    (guessedChain guess) (guessedPosition guess) continuation
  simpa only [SM_DT_UD_response, chainUDProblem, SM_DT_UD_Problem.standalone,
    id_eq, continuation, guess, bind_assoc, pure_bind] using
    congrArg (fun d : MeasureTheory.Measure Bool => d {true}) hprojection

private theorem chainTerminalBack_mass_eq_front
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[chainTerminalBackProgram P enc K I A] {true} =
      𝒟[jointTerminalProgram P enc K I A] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  unfold chainTerminalBackProgram jointTerminalProgram jointOuterDraw
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro pp _
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro selector _
  exact congrArg (fun d : MeasureTheory.Measure Bool => d {true})
    (evalDist_bind_bind_swap (GXMSS.sampleStarts H h v) (sampleFillers I H) _)

/-- The filtered first-cut experiment samples an independent real challenge input, one active
selector and a fixed filler table. The observation retains returned false and unreturned mass. -/
private noncomputable def zeroRealFilteredExperiment
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  exact jointZeroRealProgram P enc K I A

/-- Exact native additive form of the signed joint chain telescope, before absolute values.
The same one-target original-domain UD adversary appears in both worlds and the terminal term is the
actual original-domain PRE selected experiment; all cuts retain the same sampled filler table. -/
private theorem selectedChain_native_telescope
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    𝒟[zeroRealFilteredExperiment P enc K I hv hw A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          𝒟[SM_DT_UD_Experiment .ideal (chainUndetectabilityReduction P enc K I hv hw A)] {true} =
      𝒟[selectedPreimageExperiment P enc K I hv hw A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          𝒟[SM_DT_UD_Experiment .real (chainUndetectabilityReduction P enc K I hv hw A)]
            {true} := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  change 𝒟[jointZeroRealProgram P enc K I A] {true} + _ =
    𝒟[chainPRESelectedProgram P enc K I A] {true} + _
  rw [chainUDExperiment_true_eq_chainCut, chainUDExperiment_true_eq_chainCut,
    chainUDChainCut_mass_eq_front, chainUDChainCut_mass_eq_front,
    chainPRESelected_mass_eq_filtered, chainPREFiltered_mass_eq_terminalBack,
    chainTerminalBack_mass_eq_front]
  exact joint_native_returned_mass_telescope P enc K I A

private theorem fixedSelectedSource_mass_eq_zeroReal
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (fillers : Fillers I H) :
    𝒟[fixedSelectedSourceProgram P enc K I A pp guess fillers] {true} =
      𝒟[do
        let starts ← GXMSS.sampleStarts H h v
        let x ← ($ᵗ H : ProbComp H)
        let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers) A pp guess
          (guessedEpoch guess, guessedChain guess, Fin.ofNat (2 ^ w - 1) 0)
          (P.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x) starts
        pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))]
        {true} := by
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  have hn : 0 < 2 ^ w - 1 := Nat.pos_of_ne_zero (NeZero.ne _)
  let zero : Guess h w v := (guessedEpoch guess, guessedChain guess, ⟨0, hn⟩)
  let source : ProbComp Bool := do
    let starts ← GXMSS.sampleStarts H h v
    let response := P.chain pp (guessedEpoch guess) (guessedChain guess) 0
      ((guessedPosition guess).val + 1) (starts (guessedEpoch guess) (guessedChain guess))
    let out ← runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts
    pure (intervalSelectedChainObservation P enc K I fillers guess out)
  have hsource : fixedSelectedSourceProgram P enc K I A pp guess fillers = source := by
    unfold fixedSelectedSourceProgram source
    apply bind_congr
    intro starts
    dsimp only
    rw [runContextSpliced_honest_interval]
    simp only [bind_assoc]
    apply bind_congr
    rintro ⟨publicKey, forgery, history⟩
    rfl
  have hpoint (starts : Epoch h → Fin v → H) :
      𝒟[do
        let response := P.chain pp (guessedEpoch guess) (guessedChain guess) 0
          ((guessedPosition guess).val + 1) (starts (guessedEpoch guess) (guessedChain guess))
        let out ← runContextSpliced P enc K (intervalChainContext P I fillers)
          A pp guess response starts
        pure (intervalSelectedChainObservation P enc K I fillers guess out)] {true} =
      𝒟[do
        let response := P.chain pp (guessedEpoch guess) (guessedChain guess) 0 1
          (starts (guessedEpoch guess) (guessedChain guess))
        let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
          A pp guess zero response starts
        pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))]
        {true} := by
    have hfilter := intervalSelectedSplice_mass_eq_filtered P enc K I A pp fillers guess guess
      (P.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1) (starts (guessedEpoch guess) (guessedChain guess))) starts
    have hcut := runContextFilteredSpliced_honest_from_zero P enc K
      (intervalChainContext P I fillers) A pp guess starts hn
    rw [← hcut] at hfilter
    simpa only [zero, map_eq_bind_pure_comp, Function.comp_def] using hfilter
  have hzero : (guessedPosition zero).val = 0 := rfl
  have hresample := intervalSelectedSplice_zero_real_resampling P enc K I A pp fillers
    guess zero hzero hn rfl rfl
  have hmass : 𝒟[source] {true} =
      𝒟[do
        let starts ← GXMSS.sampleStarts H h v
        let response := P.chain pp (guessedEpoch guess) (guessedChain guess) 0 1
          (starts (guessedEpoch guess) (guessedChain guess))
        let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
          A pp guess zero response starts
        pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))]
        {true} := by
    unfold source
    apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
    intro starts _
    exact hpoint starts
  rw [hsource, hmass]
  have hswap := OracleComp.evalDist_bind_bind_swap ($ᵗ H : ProbComp H) (GXMSS.sampleStarts H h v)
    (fun x starts => do
      let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
        A pp guess zero (P.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x) starts
      pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess)))
  have hzeroFin : (⟨0, hn⟩ : Fin (2 ^ w - 1)) = Fin.ofNat (2 ^ w - 1) 0 := by
    apply Fin.ext
    simp
  exact hresample.trans (by
    simpa only [zero, guessedEpoch, guessedChain, hzeroFin] using
      congrArg (fun d : MeasureTheory.Measure Bool => d {true}) hswap)

private theorem selectedSource_mass_eq_zeroReal
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    𝒟[selectedSourceExperiment P enc K I hv hw A] {true} =
      𝒟[zeroRealFilteredExperiment P enc K I hv hw A] {true} := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  let : MeasurableSpace (PP × Guess h w v × Fillers I H) := ⊤
  unfold selectedSourceExperiment zeroRealFilteredExperiment jointZeroRealProgram
  apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
  intro z _
  rcases z with ⟨pp, guess, fillers⟩
  exact fixedSelectedSource_mass_eq_zeroReal P enc K I A pp guess fillers

/-- Native signed chain identity for the actual selected interval source event. The exact
real-minus-ideal UD contribution is retained before taking any absolute value. -/
theorem selectedSource_native_telescope
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    𝒟[selectedSourceExperiment P enc K I hv hw A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          𝒟[SM_DT_UD_Experiment .ideal (chainUndetectabilityReduction P enc K I hv hw A)] {true} =
      𝒟[selectedPreimageExperiment P enc K I hv hw A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          𝒟[SM_DT_UD_Experiment .real (chainUndetectabilityReduction P enc K I hv hw A)]
            {true} := by
  rw [selectedSource_mass_eq_zeroReal]
  exact selectedChain_native_telescope P enc K I hv hw A

/-- One-target chain PRE with fixed `starts 0 0` fallback. The selected-coordinate
public strategy remains separate; unselected fallback outputs can accidentally win. -/
noncomputable def chainPreimageReduction
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    SM_DT_PRE_Adversary (chainPREProblem P) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  exact {
    State := ChainPREState H h w v I
    choose := chainPREPick P I
    invert state pp := do
      let guess := activeGuess I state.selector
      let starts := state.starts
      let fallback := starts 0 0
      match state.answer with
      | none => return (0, fallback)
      | some response =>
        let out ← runContextSpliced P enc K (intervalChainContext P I state.fillers)
          A pp guess response state.starts
        let preimage := extractChainPreimageWithFallback P enc K I state.fillers guess fallback out
        return (0, preimage) }

private noncomputable def fixedFallbackPREExplicitProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let hidden ← ($ᵗ H : ProbComp H)
    let guess := activeGuess I selector
    let tweak := P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess)
    let response := TweakableHash.eval P.thf pp tweak (P.digestInput hidden)
    let out ← runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts
    let fallback := starts 0 0
    let preimage :=
      extractChainPreimageWithFallback P enc K I fillers guess fallback out
    pure (decide (TweakableHash.eval P.thf pp tweak
      (P.digestInput preimage) = response))

private theorem fixedFallbackPREExperiment_eq_explicit
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    SM_DT_PRE_Experiment (chainPreimageReduction P enc K I hv hw A) =
      fixedFallbackPREExplicitProgram P enc K I A := by
  unfold SM_DT_PRE_Experiment chainPreimageReduction
    fixedFallbackPREExplicitProgram chainPREPick
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    pure_bind, bind_assoc]
  simp only [chainPREOracles_liftComp, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  simp only [chainPREOracles_challenge, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl

end GXMSS.Interval.Reductions.Chain
