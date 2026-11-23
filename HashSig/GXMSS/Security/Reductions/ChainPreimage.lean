/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
import all HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Security.Auxiliary.ChainSplicing
import all HashSig.GXMSS.Security.Auxiliary.ChainSplicing
public import HashSig.GXMSS.Security.Auxiliary.ChainSourceMass
import all HashSig.GXMSS.Security.Auxiliary.ChainSourceMass
public import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
public import HashSig.GXMSS.Security.Auxiliary.ChainTelescope
import all HashSig.GXMSS.Security.Auxiliary.ChainTelescope
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
import all HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Auxiliary.Encoding
import all HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
public import HashSig.GXMSS.Security.Reductions.EncodingCollision
import all HashSig.GXMSS.Security.Reductions.EncodingCollision
public import HashSig.GXMSS.Security.Reductions.Problems
import all HashSig.GXMSS.Security.Reductions.Problems
public import HashSig.GXMSS.Security.Reductions.TargetCollision
import all HashSig.GXMSS.Security.Reductions.TargetCollision
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.EvalDist.Sum
public import HashSig.GXMSS.Security.Reductions.ChainUndetectability
import all HashSig.GXMSS.Security.Reductions.ChainUndetectability

/-!
# Original-domain chain preimage reduction

Selected chain witnesses and the named one-target preimage experiments preserve fallback
outcomes and all source-history classes. Whole coupled experiments justify the advantage bound.
-/

public section

namespace GXMSS.Reductions

open Encoding ENNReal OracleComp OracleSpec GXMSS.Security TweakableHash

variable {PP T X H M R E S : Type} {h w v n radix : ℕ}

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
    simp [HashInstance.findChainCut, preimage, hcut]
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

/-- A non-maximum forged digit yields a preimage of a spliced final response whenever Game 1
equates the forged chain endpoint with that response. This is the deterministic PRE witness;
the distributional relation to the PRE experiment is separate. -/
private theorem spliced_final_nonSuccess_preimage_sound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (pp : PP) (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (out : Result PP H M R h v)
    (word : Codeword v (2 ^ w)) (i : Fin v)
    (hseed : out.pk.seed = pp)
    (hendpoints : out.sk.endpoints = splicedEndpoints hash pp guess answer starts)
    (hword : enc.value out.pk.seed out.forgery.2.1
      out.forgery.2.2.randomizer out.forgery.1 = some word)
    (hone : gameOneObservation hash enc K out = true)
    (hi : findNonMaximumCoordinate word = some i)
    (hepoch : guessedEpoch guess = out.forgery.1)
    (hchain : guessedChain guess = i)
    (hfinal : (guessedPosition guess).val + 1 = 2 ^ w - 1) :
    (HashInstance.thf hash).eval pp (hash.chainTweak
      (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (hash.digestInput (hash.chain pp out.forgery.1 i (word i)
        (2 ^ w - 2 - (word i).val) (out.forgery.2.2.ots i))) = answer := by
  have hsmall := findNonMaximumCoordinate_sound word hi
  have hendpoint := gameOneObservation_endpoint_eq_forged hash enc K out word hword hone i
  rw [hseed] at hendpoint
  have hselected : out.sk.endpoints out.forgery.1 i = answer := by
    rw [hendpoints, ← hepoch, ← hchain]
    exact splicedEndpoints_guess_final hash pp guess answer starts hfinal
  rw [hselected] at hendpoint
  have heval := chainFinalPredecessor_sound hash pp out.forgery.1 i (word i)
    (guessedPosition guess) (out.forgery.2.2.ots i) answer hsmall hfinal hendpoint.symm
  simpa only [hepoch, hchain] using heval
/-- In a returned spliced execution, the enlarged selector's unused or failed-consumed branch
produces the concrete final-step PRE witness from the forged OTS suffix. -/
private theorem joint_nonSuccess_selected_preimage_sound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runSpliced hash enc K adv pp guess answer starts))
    (hsource : forgedEpochSource out = .unused ∨
      ∃ msg, forgedEpochSource out = .failedConsumed msg)
    (hwin : jointChainObservation hash enc K (guess, out) = true) :
    ∃ word : Codeword v (2 ^ w), ∃ i : Fin v,
      enc.value pp out.forgery.2.1 out.forgery.2.2.randomizer out.forgery.1 =
        some word ∧
      findNonMaximumCoordinate word = some i ∧
      (HashInstance.thf hash).eval pp (hash.chainTweak
        (guessedEpoch guess, guessedChain guess, guessedPosition guess))
        (hash.digestInput (hash.chain pp out.forgery.1 i (word i)
          (2 ^ w - 2 - (word i).val) (out.forgery.2.2.ots i))) = answer := by
  obtain ⟨hseed, hendpoints⟩ := runSpliced_support_keys hash enc K adv pp guess
    answer starts out hout
  have hfilter := hwin
  rcases hsource with hs | ⟨msg, hs⟩
  · simp only [jointChainObservation, hs, Bool.and_eq_true] at hfilter
    have hfour := hfilter.1
    have hselected := hfilter.2
    rw [hseed] at hselected
    cases hword : enc.value pp out.forgery.2.1 out.forgery.2.2.randomizer
        out.forgery.1 with
    | none => simp [hword] at hselected
    | some word =>
      cases hi : findNonMaximumCoordinate word with
      | none => simp [hword, hi] at hselected
      | some i =>
        simp only [hword, hi] at hselected
        have hguess : guessedEpoch guess = out.forgery.1 ∧
            guessedChain guess = i ∧
            (guessedPosition guess).val + 1 = 2 ^ w - 1 := by
          exact of_decide_eq_true hselected
        have hone : gameOneObservation hash enc K out = true := by
          have hfour' := hfour
          simp only [gameFourObservation, Bool.and_eq_true] at hfour'
          have hthree := hfour'.1
          simp only [gameThreeObservation, Bool.and_eq_true] at hthree
          have htwo := hthree.1
          simp only [gameTwoObservation, Bool.and_eq_true] at htwo
          exact htwo.1
        refine ⟨word, i, rfl, hi, ?_⟩
        exact spliced_final_nonSuccess_preimage_sound hash enc K pp guess answer
          starts out word i hseed hendpoints (by rw [hseed]; exact hword)
          hone hi hguess.1 hguess.2.1 hguess.2.2
  · simp only [jointChainObservation, hs, Bool.and_eq_true] at hfilter
    have hfour := hfilter.1
    have hselected := hfilter.2
    rw [hseed] at hselected
    cases hword : enc.value pp out.forgery.2.1 out.forgery.2.2.randomizer
        out.forgery.1 with
    | none => simp [hword] at hselected
    | some word =>
      cases hi : findNonMaximumCoordinate word with
      | none => simp [hword, hi] at hselected
      | some i =>
        simp only [hword, hi] at hselected
        have hguess : guessedEpoch guess = out.forgery.1 ∧
            guessedChain guess = i ∧
            (guessedPosition guess).val + 1 = 2 ^ w - 1 := by
          exact of_decide_eq_true hselected
        have hone : gameOneObservation hash enc K out = true := by
          have hfour' := hfour
          simp only [gameFourObservation, Bool.and_eq_true] at hfour'
          have hthree := hfour'.1
          simp only [gameThreeObservation, Bool.and_eq_true] at hthree
          have htwo := hthree.1
          simp only [gameTwoObservation, Bool.and_eq_true] at htwo
          exact htwo.1
        refine ⟨word, i, rfl, hi, ?_⟩
        exact spliced_final_nonSuccess_preimage_sound hash enc K pp guess answer
          starts out word i hseed hendpoints (by rw [hseed]; exact hword)
          hone hi hguess.1 hguess.2.1 hguess.2.2
/-- The successful selected branch uses the existing designated cut. Its extracted predecessor
hashes to the PRE challenge response supplied at the guessed tweak. -/
private theorem joint_successful_selected_preimage_sound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runSpliced hash enc K adv pp guess answer starts))
    (msg : M) (sig : GXMSS.Signature R H h v)
    (hsource : forgedEpochSource out = .successful msg sig)
    (hwin : jointChainObservation hash enc K (guess, out) = true) :
    ∃ honestWord forgedWord : Codeword v (2 ^ w), ∃ i : Fin v,
      enc.value pp msg sig.randomizer out.forgery.1 = some honestWord ∧
      enc.value pp out.forgery.2.1 out.forgery.2.2.randomizer out.forgery.1 =
        some forgedWord ∧
      findSmallerCoordinate honestWord forgedWord = some i ∧
      ∃ preimage : H,
        hash.findChainCut pp out.forgery.1 i (forgedWord i) (honestWord i)
          (2 ^ w - 1) (sig.ots i) (out.forgery.2.2.ots i) = some (.inl preimage) ∧
        (HashInstance.thf hash).eval pp (hash.chainTweak
          (guessedEpoch guess, guessedChain guess, guessedPosition guess))
          (hash.digestInput preimage) = answer := by
  obtain ⟨hseed, _⟩ := runSpliced_support_keys hash enc K adv pp guess answer
    starts out hout
  obtain ⟨honestWord, forgedWord, i, hfour, hhonest, hforged, hi,
      hepoch, hchain, hposition⟩ :=
    jointChainObservation_successful_cut hash enc K guess out msg sig hsource hwin
  have hrecord := history_of_successful_source out msg sig hsource
  obtain ⟨wr, hsig, hwr⟩ := runSpliced_successful_record_signature hash enc K
    adv pp guess answer starts out hout out.forgery.1 msg sig hrecord
  have hhonest' : enc.value pp msg wr.2 out.forgery.1 = some honestWord := by
    rw [hseed] at hhonest
    simpa [hsig, splicedSignatureOfWord] using hhonest
  have hwordEq : wr.1 = honestWord := Option.some.inj (hwr.symm.trans hhonest')
  have hsigAnswer : sig.ots i = answer := by
    rw [hsig, ← hchain]
    apply splicedSignatureOfWord_guess_succ hash pp guess answer starts
      (splicedEndpoints hash pp guess answer starts) out.forgery.1 wr hepoch.symm
    rw [hwordEq, hchain]
    exact hposition.symm
  have hfour' := hfour
  simp only [gameFourObservation, Bool.and_eq_true] at hfour'
  have hcut := hfour'.2
  simp only [designatedCutHolds, hsource, hhonest, hforged, hi] at hcut
  have hcutEq := of_decide_eq_true hcut
  rw [hseed, hsigAnswer] at hcutEq
  let preimage : H := hash.chain pp out.forgery.1 i (forgedWord i)
    ((honestWord i).val - (forgedWord i).val - 1) (out.forgery.2.2.ots i)
  have hfind : hash.findChainCut pp out.forgery.1 i (forgedWord i)
      (honestWord i) (2 ^ w - 1) (sig.ots i) (out.forgery.2.2.ots i) =
        some (.inl preimage) := by
    simp [HashInstance.findChainCut, preimage, hcutEq, hsigAnswer]
  have hsmaller := findSmallerCoordinate_sound honestWord forgedWord hi
  have hlen : (forgedWord i).val +
      ((honestWord i).val - (forgedWord i).val - 1) + 1 ≤ 2 ^ w - 1 := by
    have := (honestWord i).isLt
    omega
  have hstep := hash.chain_succ pp out.forgery.1 i (forgedWord i)
    ((honestWord i).val - (forgedWord i).val - 1) (out.forgery.2.2.ots i) hlen
  have hcount : (honestWord i).val - (forgedWord i).val - 1 + 1 =
      (honestWord i).val - (forgedWord i).val := by omega
  rw [hcount] at hstep
  have hpos : (⟨(forgedWord i).val +
      ((honestWord i).val - (forgedWord i).val - 1), by omega⟩ :
      Fin (2 ^ w - 1)) = guessedPosition guess := by
    apply Fin.ext
    change (forgedWord i).val +
      ((honestWord i).val - (forgedWord i).val - 1) = (guessedPosition guess).val
    omega
  rw [hpos] at hstep
  have heval : (HashInstance.thf hash).eval pp (hash.chainTweak
      (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (hash.digestInput preimage) = answer := by
    have := hstep.symm.trans hcutEq
    simpa only [preimage, hepoch, hchain] using this
  refine ⟨honestWord, forgedWord, i, ?_, ?_, hi, preimage, hfind, heval⟩
  · rw [hseed] at hhonest
    exact hhonest
  · rw [hseed] at hforged
    exact hforged

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

end GXMSS.Reductions
