/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.EncodingSimulation
public import HashSig.GXMSS.Security.Interval.Reductions.FilteredView
public import HashSig.GXMSS.Security.Interval.Reductions.SourcePartition
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
import all HashSig.GXMSS.Security.Interval.Reductions.EncodingSimulation
import all HashSig.GXMSS.Security.Interval.Reductions.FilteredView
import HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import HashSig.GXMSS.Security.Auxiliary.ChainSelection

/-!
# Original-domain interval chain reduction programs

One retained start and filler table determines each adaptive splice. Active selectors and
challenge responses are captured by the named UD and selected PRE adversaries.
-/

public section
namespace GXMSS.Reductions
open IncomparableEncoding OracleComp OracleSpec TweakableHash
variable {PP T X H M R : Type} {h w v : ℕ}

/-- One-target chain undetectability problem on the original digest input domain. -/
@[expose] noncomputable def chainUDProblem [SampleableType H]
    (hash : HashInstance PP T X H h w v) :=
  SM_DT_UD_Problem.standalone hash.thf hash.digestInput (HashInstance.digestInput hash).injective
    ($ᵗ H) ($ᵗ H) 1

/-- One-target chain preimage problem on the original digest input domain. -/
@[expose] def chainPREProblem (hash : HashInstance PP T X H h w v) :=
  SM_DT_PRE_Problem.standalone hash.thf hash.digestInput (HashInstance.digestInput hash).injective 1

/-- Exact source-history classification at the forged epoch. -/
private inductive ForgedEpochSource (M S : Type)
  | unused
  | successful (message : M) (signature : S)
  | failedConsumed (message : M)

/-- Classify `none`, `some (msg, some signature)`, and `some (msg, none)` without merging cases. -/
private def forgedEpochSource (out : Result PP H M R h v) :
    ForgedEpochSource M (GXMSS.Signature R H h v) :=
  let forgery := out.forgery
  match out.history forgery.1 with
  | none => .unused
  | some (msg, some signature) => .successful msg signature
  | some (msg, none) => .failedConsumed msg

/-- Equation (4)'s designated-cut equality, when both encodings and the smaller coordinate exist. -/
private def designatedCutHolds [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (out : Result PP H M R h v) : Bool :=
  let publicKey := out.pk
  let forgery := out.forgery
  let forgedEpoch := forgery.1
  let forgedPayload := forgery.2
  let forgedMessage := forgedPayload.1
  let forgedSignature := forgedPayload.2
  match forgedEpochSource out with
  | .successful msg sig =>
      match enc.value publicKey.seed msg sig.randomizer forgedEpoch,
        enc.value publicKey.seed forgedMessage forgedSignature.randomizer forgedEpoch with
      | some honestWord, some forgedWord =>
          match (Fin.find? fun j => decide (forgedWord j < honestWord j)) with
          | none => false
          | some i => decide (hash.chain publicKey.seed forgedEpoch i (forgedWord i)
              ((honestWord i).val - (forgedWord i).val) (forgedSignature.ots i) = sig.ots i)
      | _, _ => false
  | _ => true

end GXMSS.Reductions

namespace GXMSS.Interval.Reductions
open OracleComp OracleSpec IncomparableEncoding GXMSS.Reductions GXMSS.IntervalMerkle
    SyncSignatureUnforgeability
variable {PP T X H M R : Type} {h w v : ℕ}

private noncomputable def intervalChainRemainderObservation
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (fillers : Fillers I H) (out : Result PP H M R h v) : Bool :=
  let pk := out.pk
  let (epoch, message, signature) := out.forgery
  let history := out.history
  let view : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v) := (pk, out.forgery, history)
  let sk := out.sk
  let endpoints := sk.endpoints
  -- The matching gate observes seed/endpoints only; its start field is irrelevant.
  let observedKey : GXMSS.Interval.SecretKey PP H h v I :=
    ⟨⟨pk.seed, endpoints, endpoints⟩, fillers⟩
  GXMSS.Interval.Unforgeability.activeMatchingEvent P enc K I observedKey view &&
    !intervalEncodingCollision enc I view &&
    (match history epoch with
    | some (first, some honest) => decide ((first, honest.randomizer) ≠
        (message, signature.randomizer) ∨ honest.ots = signature.ots)
    | _ => true) && designatedCutHolds P enc out

private theorem intervalChainRemainder_endpoint_eq_forged
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (fillers : Fillers I H) (out : Result PP H M R h v) (word : Codeword v (2 ^ w))
    (hword : let pk := out.pk
      let (epoch, message, signature) := out.forgery
      enc.value pk.seed message signature.randomizer epoch = some word)
    (hrem : intervalChainRemainderObservation P enc K I fillers out = true) (i : Fin v) :
    let sk := out.sk
    let pk := out.pk
    let (epoch, _, signature) := out.forgery
    sk.endpoints epoch i = P.chain pk.seed epoch i (word i)
      (2 ^ w - 1 - (word i).val) (signature.ots i) := by
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history⟩
  dsimp only at hword
  simp only [intervalChainRemainderObservation, Bool.and_eq_true] at hrem
  rcases hrem with ⟨⟨⟨hactive, _⟩, _⟩, _⟩
  simp only [GXMSS.Interval.Unforgeability.activeMatchingEvent, hword, Bool.and_eq_true] at hactive
  exact congrFun (congrArg Prod.fst (of_decide_eq_true hactive.2).2) i

private noncomputable def intervalSelectedCut
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (selector : Guess h w v) (out : Result PP H M R h v) : Bool :=
  let pk := out.pk
  let (epoch, message, signature) := out.forgery
  match out.history epoch with
  | some (first, some honest) =>
    match enc.value pk.seed first honest.randomizer epoch,
        enc.value pk.seed message signature.randomizer epoch with
    | some honestWord, some forgedWord =>
      match (Fin.find? fun j => decide (forgedWord j < honestWord j)) with
      | none => false
      | some i => decide (guessedEpoch selector = epoch ∧ guessedChain selector = i ∧
          (guessedPosition selector).val + 1 = (honestWord i).val)
    | _, _ => false
  | _ =>
    match enc.value pk.seed message signature.randomizer epoch with
    | none => false
    | some word =>
      match findNonMaximumCoordinate word with
      | none => false
      | some i => decide (guessedEpoch selector = epoch ∧ guessedChain selector = i ∧
          (guessedPosition selector).val + 1 = 2 ^ w - 1)

private theorem intervalSelectedCut_not_bad
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (selector : Guess h w v) (out : Result PP H M R h v)
    (hsel : intervalSelectedCut enc selector out = true) :
    let pk := out.pk
    badSelectedHistory enc pk.seed selector out.history = false := by
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history⟩
  cases hentry : history epoch with
  | none =>
    cases hword : enc.value pk.seed message signature.randomizer epoch with
    | none => simp [intervalSelectedCut, hentry, hword] at hsel
    | some word =>
      cases hi : findNonMaximumCoordinate word with
      | none => simp [intervalSelectedCut, hentry, hword, hi] at hsel
      | some i =>
        have hs : guessedEpoch selector = epoch ∧ guessedChain selector = i ∧
            (guessedPosition selector).val + 1 = 2 ^ w - 1 := by
          simpa [intervalSelectedCut, hentry, hword, hi] using hsel
        simp [badSelectedHistory, hs.1, hentry]
  | some entry =>
    rcases entry with ⟨first, answer⟩
    cases answer with
    | none =>
      cases hword : enc.value pk.seed message signature.randomizer epoch with
      | none => simp [intervalSelectedCut, hentry, hword] at hsel
      | some word =>
        cases hi : findNonMaximumCoordinate word with
        | none => simp [intervalSelectedCut, hentry, hword, hi] at hsel
        | some i =>
          have hs : guessedEpoch selector = epoch ∧ guessedChain selector = i ∧
              (guessedPosition selector).val + 1 = 2 ^ w - 1 := by
            simpa [intervalSelectedCut, hentry, hword, hi] using hsel
          simp [badSelectedHistory, hs.1, hentry]
    | some honest =>
      cases hhonest : enc.value pk.seed first honest.randomizer epoch with
      | none => simp [intervalSelectedCut, hentry, hhonest] at hsel
      | some honestWord =>
        cases hforged : enc.value pk.seed message signature.randomizer epoch with
        | none => simp [intervalSelectedCut, hentry, hhonest, hforged] at hsel
        | some forgedWord =>
          cases hi : (Fin.find? fun j => decide (forgedWord j < honestWord j)) with
          | none => simp [intervalSelectedCut, hentry, hhonest, hforged, hi] at hsel
          | some i =>
            have hs : guessedEpoch selector = epoch ∧ guessedChain selector = i ∧
                (guessedPosition selector).val + 1 = (honestWord i).val := by
              simpa [intervalSelectedCut, hentry, hhonest, hforged, hi] using hsel
            have hn : ¬ (honestWord (guessedChain selector)).val <
                (guessedPosition selector).val + 1 := by
              rcases hs with ⟨_, hchain, hposition⟩
              rw [hchain, hposition]
              omega
            simp [badSelectedHistory, hs.1, hentry, hhonest, hn]

private noncomputable def intervalSelectedChainObservation
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (fillers : Fillers I H) (selector : Guess h w v) (out : Result PP H M R h v) : Bool :=
  intervalChainRemainderObservation P enc K I fillers out && intervalSelectedCut enc selector out

private theorem intervalSelectedChainObservation_not_bad
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (fillers : Fillers I H) (selector : Guess h w v) (out : Result PP H M R h v)
    (hwin : intervalSelectedChainObservation P enc K I fillers selector out = true) :
    let pk := out.pk
    badSelectedHistory enc pk.seed selector out.history = false := by
  simp only [intervalSelectedChainObservation, Bool.and_eq_true] at hwin
  exact intervalSelectedCut_not_bad enc selector out hwin.2

end GXMSS.Interval.Reductions

namespace GXMSS.Interval.Reductions.Chain
open OracleComp OracleSpec TweakableHash IncomparableEncoding GXMSS.IntervalMerkle
    GXMSS.Reductions GXMSS.Interval.Reductions SyncSignatureUnforgeability
variable {PP T X H M R : Type} {h w v : ℕ}

private abbrev ActiveSelector (I : Interval h) (w v : ℕ) :=
  Fin (I.last.val - I.first.val + 1) × Fin v × Fin (2 ^ w - 1)

private def activeGuess (I : Interval h) (selector : ActiveSelector I w v) : Guess h w v :=
  let (offset, chain, position) := selector
  (⟨I.first.val + offset.val, by
    have ho := I.ordered
    have hl := I.last.isLt
    have hx := offset.isLt
    simp only [Fin.le_iff_val_le_val] at ho
    omega⟩, chain, position)

private theorem activeGuess_isActive (I : Interval h) (selector : ActiveSelector I w v) :
    Epoch.IsActive I (guessedEpoch (activeGuess I selector)) := by
  rcases selector with ⟨offset, chain, position⟩
  have ho := I.ordered
  have hx := offset.isLt
  simp only [Epoch.IsActive, activeGuess, guessedEpoch, Fin.le_iff_val_le_val] at *
  omega

private theorem activeSelector_card (I : Interval h) :
    Fintype.card (ActiveSelector I w v) =
      (I.last.val - I.first.val + 1) * v * (2 ^ w - 1) := by
  simp [ActiveSelector, Nat.mul_assoc]

private structure ChainUDState (H : Type) (h w v : ℕ) (I : Interval h) where
  selector : ActiveSelector I w v
  hybrid : Fin (2 ^ w - 1)
  answer : Option H
  starts : Epoch h → Fin v → H
  fillers : Fillers I H

private structure ChainPREState (H : Type) (h w v : ℕ) (I : Interval h) where
  selector : ActiveSelector I w v
  answer : Option H
  starts : Epoch h → Fin v → H
  fillers : Fillers I H

private noncomputable def chainUDPick
    [SampleableType H] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v) (I : Interval h) :
    OracleComp (unifSpec + (SM_DT_UD_challengeSpec T H +
      collectionSpec (chainUDProblem P).thColl)) (ChainUDState H h w v I) := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let selector ← OracleComp.liftComp ($ᵗ (ActiveSelector I w v)) _
    let hybrid ← OracleComp.liftComp ($ᵗ (Fin (2 ^ w - 1))) _
    let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
    let fillers ← OracleComp.liftComp (sampleFillers I H) _
    let guess := activeGuess I selector
    let answer ← liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
      collectionSpec (chainUDProblem P).thColl)).query (.inr (.inl
        (P.chainTweak (guessedEpoch guess, guessedChain guess, hybrid)))))
    return ⟨selector, hybrid, answer, starts, fillers⟩

/-- Original-domain interval UD retains the selector, hybrid cut, starts and complete filler table
before the sole challenge; the adaptive view uses that same table. -/
noncomputable def chainUndetectabilityReduction
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    SM_DT_UD_Adversary (chainUDProblem P) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  exact {
    State := ChainUDState H h w v I
    pick := chainUDPick P I
    distinguish state pp := do
      let guess := activeGuess I state.selector
      let hybrid := state.hybrid
      if hybrid.val < (guessedPosition guess).val then
        match state.answer with
        | none => return false
        | some response =>
          let splice : Guess h w v :=
            (guessedEpoch guess, guessedChain guess, state.hybrid)
          let out ← runContextSpliced P enc K (intervalChainContext P I state.fillers)
            A pp splice response state.starts
          return intervalSelectedChainObservation P enc K I state.fillers guess out
      else return false }

private theorem chainUD_real_response_bind_chain
    [SampleableType H] {α : Type} [MeasurableSpace α]
    (P : HashInstance PP T X H h w v) (pp : PP)
    (epoch : Epoch h) (chain : Fin v) (position : Fin (2 ^ w - 1))
    (f : H → ProbComp α) :
    𝒟[SM_DT_UD_response .real (chainUDProblem P) pp
      (P.chainTweak (epoch, chain, position)) >>= f] =
    𝒟[do let x ← ($ᵗ H : ProbComp H); f (P.chain pp epoch chain position.val 1 x)] := by
  unfold SM_DT_UD_response chainUDProblem SM_DT_UD_Problem.standalone
  simp only [bind_assoc, pure_bind]
  have hstep (x : H) : TweakableHash.eval P.thf pp (P.chainTweak (epoch, chain, position))
      (P.digestInput x) = P.chain pp epoch chain position.val 1 x := by
    have hs := P.chain_succ pp epoch chain position.val 0 x (by omega)
    simpa only [Nat.add_zero, zero_add, P.chain_zero] using hs.symm
  simp_rw [hstep]

private theorem chainUD_ideal_response [SampleableType H]
    (P : HashInstance PP T X H h w v) (pp : PP) (tweak : T) :
    SM_DT_UD_response .ideal (chainUDProblem P) pp tweak =
      ($ᵗ H : ProbComp H) := rfl

private noncomputable def extractChainPreimageWithFallback
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (fillers : Fillers I H) (guess : Guess h w v) (fallback : H)
    (out : Result PP H M R h v) : H :=
  let pk := out.pk
  if intervalSelectedChainObservation P enc K I fillers guess out = false then fallback
  else
    let (epoch, message, signature) := out.forgery
    match out.history epoch with
    | some (first, some honest) =>
      match enc.value pk.seed first honest.randomizer epoch,
          enc.value pk.seed message signature.randomizer epoch with
      | some honestWord, some forgedWord =>
        match (Fin.find? fun j => decide (forgedWord j < honestWord j)) with
        | none => fallback
        | some i =>
          match P.findChainCut pk.seed epoch i (forgedWord i) (honestWord i)
              (2 ^ w - 1) (honest.ots i) (signature.ots i) with
          | some (.inl preimage) => preimage
          | _ => fallback
      | _, _ => fallback
    | _ =>
      match enc.value pk.seed message signature.randomizer epoch with
      | none => fallback
      | some word =>
        match findNonMaximumCoordinate word with
        | none => fallback
        | some i => P.chain pk.seed epoch i (word i)
            (2 ^ w - 2 - (word i).val) (signature.ots i)

private noncomputable def extractChainPreimage
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (fillers : Fillers I H) (guess : Guess h w v) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v) : H :=
  extractChainPreimageWithFallback P enc K I fillers guess
    (starts (guessedEpoch guess) (guessedChain guess)) out

private noncomputable def chainPREPick
    [SampleableType H] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v) (I : Interval h) :
    OracleComp (unifSpec + (SM_DT_PRE_challengeSpec T H +
      collectionSpec (chainPREProblem P).thColl)) (ChainPREState H h w v I) := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let selector ← OracleComp.liftComp ($ᵗ (ActiveSelector I w v)) _
    let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
    let fillers ← OracleComp.liftComp (sampleFillers I H) _
    let guess := activeGuess I selector
    let answer ← liftM ((unifSpec + (SM_DT_PRE_challengeSpec T H +
      collectionSpec (chainPREProblem P).thColl)).query (.inr (.inl
        (P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess)))))
    return ⟨selector, answer, starts, fillers⟩

/-- Interval PRE on the original digest input domain with a selected-coordinate fallback.
Every simulated view and chain cut uses one retained filler table. -/
noncomputable def selectedChainPreimageReduction
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
      let fallback := state.starts (guessedEpoch guess) (guessedChain guess)
      match state.answer with
      | none => return (0, fallback)
      | some response =>
        let out ← runContextSpliced P enc K (intervalChainContext P I state.fillers)
          A pp guess response state.starts
        let preimage := extractChainPreimage P enc K I state.fillers guess state.starts out
        return (0, preimage) }

end GXMSS.Interval.Reductions.Chain
