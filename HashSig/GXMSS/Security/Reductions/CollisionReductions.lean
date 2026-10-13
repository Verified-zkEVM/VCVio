/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.GuessingGames
import all HashSig.GXMSS.Security.Reductions.SourceGames
import all HashSig.GXMSS.Security.Reductions.GuessingGames

/-!
# Target collision reductions

The Merkle and chain reductions use the authoritative reject-on-arrival SM-DT-TCR game.
The encoding reduction records exactly `qs` signing queries, makes no post-forgery query,
and charges only differences backed by a successful source record.
-/

public section

namespace GXMSS.Reductions

open Encoding ENNReal OracleComp OracleSpec Security TweakableHash

variable {PP T X H M R E S : Type} {h w v n radix : ℕ}

/-- Chain value at `position`, with the guessed predecessor replaced when the guess is positive. -/
def replacedChainValue (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (replacement : H) (starts : Epoch h → Fin v → H)
    (ep : Epoch h) (i : Fin v) (position : ℕ) : H :=
  if _htarget : ep = guessedEpoch guess ∧ i = guessedChain guess then
    if position < (guessedPosition guess).val then
      hash.chain pp ep i 0 position (starts ep i)
    else
      hash.chain pp ep i (guessedPosition guess).val
        (position - (guessedPosition guess).val) replacement
  else hash.chain pp ep i 0 position (starts ep i)

/-- Below the guessed predecessor, Game 6 retains the honest chain. -/
theorem replacedChainValue_below (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (replacement : H) (starts : Epoch h → Fin v → H)
    (position : ℕ) (hposition :
      let coordinate := guess.2
      let guessedPosition := coordinate.2
      position < guessedPosition.val) :
    let guessedEpoch := guess.1
    let coordinate := guess.2
    let guessedChain := coordinate.1
    replacedChainValue hash pp guess replacement starts guessedEpoch guessedChain position =
      hash.chain pp guessedEpoch guessedChain 0 position (starts guessedEpoch guessedChain) := by
  dsimp at hposition ⊢
  simp [replacedChainValue, guessedEpoch, guessedChain, guessedPosition, hposition]

/-- At the guessed predecessor, Game 6 returns exactly the sampled replacement. -/
theorem replacedChainValue_equal (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (replacement : H) (starts : Epoch h → Fin v → H) :
    let guessedEpoch := guess.1
    let coordinate := guess.2
    let guessedChain := coordinate.1
    let guessedPosition := coordinate.2
    replacedChainValue hash pp guess replacement starts guessedEpoch guessedChain
        guessedPosition.val = replacement := by
  dsimp
  simp [replacedChainValue, guessedEpoch, guessedChain, guessedPosition]

/-- Above the guessed predecessor, Game 6 continues the chain from the replacement. -/
theorem replacedChainValue_above (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (replacement : H) (starts : Epoch h → Fin v → H)
    (position : ℕ) (hposition :
      let coordinate := guess.2
      let guessedPosition := coordinate.2
      guessedPosition.val ≤ position) :
    let guessedEpoch := guess.1
    let coordinate := guess.2
    let guessedChain := coordinate.1
    let guessedPosition := coordinate.2
    replacedChainValue hash pp guess replacement starts guessedEpoch guessedChain position =
      hash.chain pp guessedEpoch guessedChain guessedPosition.val
        (position - guessedPosition.val) replacement := by
  dsimp at hposition ⊢
  simp [replacedChainValue, guessedEpoch, guessedChain, guessedPosition,
    Nat.not_lt.mpr hposition]

/-- The equality case is the zero-step instance of the above-replacement formula. -/
theorem replacedChainValue_zeroStep (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (replacement : H) (starts : Epoch h → Fin v → H) :
    let guessedEpoch := guess.1
    let coordinate := guess.2
    let guessedChain := coordinate.1
    let guessedPosition := coordinate.2
    hash.chain pp guessedEpoch guessedChain guessedPosition.val 0 replacement =
      replacedChainValue hash pp guess replacement starts guessedEpoch guessedChain
        guessedPosition.val := by
  dsimp
  simp [replacedChainValue, guessedEpoch, guessedChain, guessedPosition]

/-- Endpoints of the chain family whose guessed predecessor is uniformly replaced. -/
def replacedEndpoints (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (replacement : H) (starts : Epoch h → Fin v → H) :
    Epoch h → Fin v → H :=
  fun ep i => replacedChainValue hash pp guess replacement starts ep i (2 ^ w - 1)

/-- Sign from the modified chain family, retaining the canonical path of its modified endpoints. -/
def replacedSignatureOfWord (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (replacement : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H) (ep : Epoch h) (wr : Codeword v (2 ^ w) × R) :
    GXMSS.Signature R H h v :=
  ⟨wr.2, fun i => replacedChainValue hash pp guess replacement starts ep i (wr.1 i),
    hash.authPath pp endpoints ep⟩

/-- A signature at the honest digit `x = g + 1` descends from the replacement at `g`. -/
theorem replacedSignatureOfWord_guess_succ (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (replacement : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H) (word : Codeword v (2 ^ w)) (randomizer : R)
    (hword :
      let coordinate := guess.2
      let guessedChain := coordinate.1
      let guessedPosition := coordinate.2
      (word guessedChain).val = guessedPosition.val + 1) :
    let guessedEpoch := guess.1
    let coordinate := guess.2
    let guessedChain := coordinate.1
    let guessedPosition := coordinate.2
    (replacedSignatureOfWord hash pp guess replacement starts endpoints guessedEpoch
      (word, randomizer)).ots guessedChain =
      hash.chain pp guessedEpoch guessedChain guessedPosition.val 1 replacement := by
  dsimp at hword ⊢
  simp [replacedSignatureOfWord, replacedChainValue, guessedEpoch, guessedChain,
    guessedPosition, hword]

/-- The guessed endpoint used by the Game 6 public root descends from the same replacement. -/
theorem replacedEndpoints_guess (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (replacement : H) (starts : Epoch h → Fin v → H) :
    let guessedEpoch := guess.1
    let coordinate := guess.2
    let guessedChain := coordinate.1
    let guessedPosition := coordinate.2
    replacedEndpoints hash pp guess replacement starts guessedEpoch guessedChain =
      hash.chain pp guessedEpoch guessedChain guessedPosition.val
        (2 ^ w - 1 - guessedPosition.val) replacement := by
  dsimp
  apply replacedChainValue_above
  omega

private def replacedSign [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (pp : PP)
    (guess : Guess h w v) (replacement : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H) (ep : Epoch h) (msg : M) :
    ProbComp (Option (GXMSS.Signature R H h v)) :=
  Option.map (replacedSignatureOfWord hash pp guess replacement starts endpoints ep) <$>
    enc.retry ($ᵗ R) pp msg ep K

private def replacedSigningOracle [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (pp : PP)
    (guess : Guess h w v) (replacement : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H) :
    QueryImpl (SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) := fun q history =>
  match history q.1 with
  | some _ => pure (none, history)
  | none => do
      let answer ← replacedSign hash enc K pp guess replacement starts endpoints q.1 q.2
      return (answer, Function.update history q.1 (some (q.2, answer)))

/-- Game 6 installs the sampled predecessor before constructing endpoints, the Merkle root, and
all signing replies. The guess type contains exactly the positive paper positions, whose sampling
instances are derived from explicit GXMSS positivity. -/
def gameSix [SampleableType H] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w) (adv : SchemeAdversary PP H M R h v) :
    ProbComp (Guess h w v × H × Result PP H M R h v) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) :=
    ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  exact do
    let guess ← $ᵗ (Guess h w v)
    let replacement ← $ᵗ H
    let pp ← (HashInstance.thf hash).seedGen
    let starts ← GXMSS.sampleStarts H h v
    let endpoints := replacedEndpoints hash pp guess replacement starts
    let pk : GXMSS.PublicKey PP H := ⟨hash.merkleRoot pp endpoints, pp⟩
    let sk : GXMSS.SecretKey PP H h v := ⟨pp, starts, endpoints⟩
    let impl : QueryImpl
        (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
          (GXMSS.Signature R H h v))
        (StateT (SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v)) ProbComp) :=
      (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (StateT (SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v)) ProbComp) +
        replacedSigningOracle hash enc K pp guess replacement starts endpoints
    let (forgery, history) ←
      (simulateQ impl (adv.forge pk)).run SyncSignatureUnforgeability.emptyHistory
    return (guess, replacement, ⟨pk, sk, forgery, history⟩)

/-- Game 6 exposes the same win observation and the replacement value for the PRE extractor. -/
def gameSixObservation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Guess h w v × H × Result PP H M R h v) : Bool :=
  let guess := out.1
  let remaining := out.2
  let result := remaining.2
  gameFiveObservation hash enc K (guess, result)

/-! ## Authoritative reduction problems -/

/-- Reject-on-arrival Merkle target-collision game with capacity for honest target registration. -/
@[expose] def merkleTCRProblem (hash : HashInstance PP T X H h w v) :=
  SM_DT_TCR_Problem.standalone hash.thf (2 * (2 ^ h) * v * (2 ^ w))

/-- Reject-on-arrival chain target-collision game with honest chain capacity. -/
@[expose] def chainTCRProblem (hash : HashInstance PP T X H h w v) :=
  SM_DT_TCR_Problem.standalone hash.thf ((2 ^ h) * v * (2 ^ w))

/-- Encoding target-collision game with `qs` signing records and retry bound `K`. -/
@[expose] def encodingTCRProblem [SampleableType R] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ) :=
  Encoding.TargetCollisionResistance.Problem.mk enc
    (HashInstance.thf hash).seedGen ($ᵗ R) qs K

/-- One-target chain undetectability game for the hash instance. -/
@[expose] noncomputable def chainUDProblem [SampleableType H]
    (hash : HashInstance PP T X H h w v) :=
  SM_DT_UD_Problem.standalone hash.thf hash.digestInput (HashInstance.digestInput hash).injective
    ($ᵗ H) ($ᵗ H) 1

/-- One-target chain preimage game for the hash instance. -/
@[expose] def chainPREProblem (hash : HashInstance PP T X H h w v) :=
  SM_DT_PRE_Problem.standalone hash.thf hash.digestInput (HashInstance.digestInput hash).injective 1

/-- Local registration state used while choosing honest SM-DT-TCR targets. -/
abbrev TCRSetupM (hash : HashInstance PP T X H h w v) (targets : ℕ) :=
  StateT (List (T × X)) (OracleComp (unifSpec + (SM_DT_TCR_challengeSpec T X H +
    collectionSpec (SM_DT_TCR_Problem.standalone hash.thf targets).thColl)))

/-- Key material obtained by registering every honest target before the public seed is revealed. -/
structure TCRKeyState (PP T X H : Type) (h v : ℕ) where
  /-- Sampled honest OTS start values. -/
  starts : Fin (2 ^ h) → Fin v → H
  /-- Honest OTS endpoints derived from the starts. -/
  endpoints : Fin (2 ^ h) → Fin v → H
  /-- Merkle root of the honest endpoints. -/
  root : H
  /-- Accepted target registrations in their submission order. -/
  targets : List (T × X)
  /-- Value returned after a target registration is rejected. -/
  fallback : H

/-- Submit one target and append it locally exactly when the authoritative oracle accepts it. -/
def tcrEval (hash : HashInstance PP T X H h w v) (targets : ℕ)
    (tweak : T) (input : X) (fallback : H) : TCRSetupM hash targets H := do
  let answer ← liftM ((unifSpec + (SM_DT_TCR_challengeSpec T X H +
    collectionSpec (SM_DT_TCR_Problem.standalone hash.thf targets).thColl)).query
      (.inr (.inl (tweak, input))))
  match answer with
  | none => return fallback
  | some value =>
      let registered ← get
      set (registered ++ [(tweak, input)])
      return value

/-- Register one complete honest chain, in positive paper-step order. -/
def tcrFullChain (hash : HashInstance PP T X H h w v) (targets : ℕ)
    (ep : Epoch h) (i : Fin v) (start fallback : H) :
    (s : ℕ) → s ≤ 2 ^ w - 1 → TCRSetupM hash targets H
  | 0, _ => pure start
  | s + 1, hs => do
      let previous ← tcrFullChain hash targets ep i start fallback s (by omega)
      tcrEval hash targets (hash.chainTweak (ep, i, ⟨s, by omega⟩))
        (hash.digestInput previous) fallback

/-- Register every positive step of every honest chain, in epoch-major order. -/
def tcrEndpoints (hash : HashInstance PP T X H h w v) (targets : ℕ)
    (starts : Epoch h → Fin v → H) (fallback : H) :
    TCRSetupM hash targets (Epoch h → Fin v → H) :=
  Fin.mOfFn (2 ^ h) fun ep => Fin.mOfFn v fun i =>
    tcrFullChain hash targets ep i (starts ep i) fallback (2 ^ w - 1) (by omega)

/-- Register every hashed leaf and internal node of the honest Merkle tree. -/
def tcrMerkleRoot (hash : HashInstance PP T X H h w v) (targets : ℕ)
    (endpoints : Epoch h → Fin v → H) (fallback : H) : TCRSetupM hash targets H :=
  PerfectMerkleTree.merkleRootM
    (fun t => if ht : t < 2 ^ h then
      let ep : Epoch h := ⟨t, ht⟩
      tcrEval hash targets (hash.treeTweak (0, ep)) (hash.vectorInput (endpoints ep)) fallback
    else pure fallback)
    (fun z t left right => if hz : z < h + 1 then
      if ht : t < 2 ^ h then
        tcrEval hash targets (hash.treeTweak (⟨z, hz⟩, ⟨t, ht⟩))
          (hash.pairInput (left, right)) fallback
      else pure fallback
    else pure fallback) h 0

/-- Register all honest chain and Merkle targets before revealing the public seed. -/
def tcrKeySetup [SampleableType H]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) :
    OracleComp (unifSpec + (SM_DT_TCR_challengeSpec T X H +
      collectionSpec (SM_DT_TCR_Problem.standalone hash.thf targets).thColl))
      (TCRKeyState PP T X H h v) := do
  let fallback ← OracleComp.liftComp ($ᵗ H) _
  let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
  let ((endpoints, root), registered) ← (do
    let endpoints ← tcrEndpoints hash targets starts fallback
    let root ← tcrMerkleRoot hash targets endpoints fallback
    return (endpoints, root)).run []
  return ⟨starts, endpoints, root, registered, fallback⟩

/-- Register all honest chain targets for either chain-collision reduction. -/
def tcrChainSetup [SampleableType H]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) :
    OracleComp (unifSpec + (SM_DT_TCR_challengeSpec T X H +
      collectionSpec (SM_DT_TCR_Problem.standalone hash.thf targets).thColl))
      (TCRKeyState PP T X H h v) := do
  let fallback ← OracleComp.liftComp ($ᵗ H) _
  let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
  let (endpoints, registered) ← (tcrEndpoints hash targets starts fallback).run []
  return ⟨starts, endpoints, fallback, registered, fallback⟩

/-- The first challenge-history index of a registered tweak/input target. -/
def registeredIndex [DecidableEq T] [DecidableEq X]
    (targets : List (T × X)) (tweak : T) (input : X) : ℕ :=
  targets.findIdx (fun target => target = (tweak, input))

/-- Membership makes the selected registered index strictly smaller than the history length. -/
theorem registeredIndex_lt_length_of_mem [DecidableEq T] [DecidableEq X]
    (targets : List (T × X)) (tweak : T) (input : X)
    (hmem : (tweak, input) ∈ targets) :
    registeredIndex targets tweak input < targets.length := by
  exact List.findIdx_lt_length_of_exists ⟨(tweak, input), hmem, by simp⟩

/-- Looking up a selected registered index returns that exact target. -/
theorem registeredIndex_lookup_of_mem [DecidableEq T] [DecidableEq X]
    (targets : List (T × X)) (tweak : T) (input : X)
    (hmem : (tweak, input) ∈ targets) :
    targets[registeredIndex targets tweak input]? = some (tweak, input) := by
  have hlt := registeredIndex_lt_length_of_mem targets tweak input hmem
  rw [List.getElem?_eq_getElem hlt]
  congr
  exact of_decide_eq_true (List.findIdx_getElem (w := hlt))

/-- A registered target is within every capacity that bounds the complete target history. -/
theorem registeredIndex_lt_capacity_of_mem [DecidableEq T] [DecidableEq X]
    (targets : List (T × X)) (tweak : T) (input : X) (capacity : ℕ)
    (hmem : (tweak, input) ∈ targets) (hlen : targets.length ≤ capacity) :
    registeredIndex targets tweak input < capacity :=
  (registeredIndex_lt_length_of_mem targets tweak input hmem).trans_le hlen

private def fallbackTarget (hash : HashInstance PP T X H h w v)
    (state : TCRKeyState PP T X H h v) : X :=
  hash.vectorInput (state.endpoints 0)

/-- Executable Merkle target-collision reduction. Its candidate is extracted from the forged
leaf. -/
def merkleTargetCollisionReduction [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (_hv : 0 < v)
    (advGXMSS : SchemeAdversary PP H M R h v) : SM_DT_TCR_Adversary (merkleTCRProblem hash) := by
  letI : NeZero v := ⟨Nat.ne_of_gt _hv⟩
  exact {
  State := TCRKeyState PP T X H h v
  choose := tcrKeySetup hash _
  forge state pp := do
    let pk : GXMSS.PublicKey PP H := ⟨state.root, pp⟩
    let sk : GXMSS.SecretKey PP H h v := ⟨pp, state.starts, state.endpoints⟩
    let out ← runWithKeys hash enc K advGXMSS pk sk
    let forgery := out.forgery
    let forgedEpoch := forgery.1
    let forgedPayload := forgery.2
    let forgedSignature := forgedPayload.2
    match forgedLeaf? hash enc out with
    | none => return (0, fallbackTarget hash state)
    | some forgedLeaf =>
      match hash.findMerkleCollision pp forgedEpoch (state.endpoints forgedEpoch)
          forgedLeaf (hash.authPath pp state.endpoints forgedEpoch) forgedSignature.path with
      | none => return (0, fallbackTarget hash state)
      | some collision =>
          return (registeredIndex state.targets collision.tweak collision.first, collision.second) }

/-- Executable first-chain target-collision reduction, distinct at the declaration level. -/
def firstChainTargetCollisionReduction [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (advGXMSS : SchemeAdversary PP H M R h v) : SM_DT_TCR_Adversary (chainTCRProblem hash) where
  State := TCRKeyState PP T X H h v
  choose := tcrChainSetup hash _
  forge state pp := do
    let sk : GXMSS.SecretKey PP H h v := ⟨pp, state.starts, state.endpoints⟩
    let pk : GXMSS.PublicKey PP H := ⟨hash.merkleRoot pp state.endpoints, pp⟩
    let out ← runWithKeys hash enc K advGXMSS pk sk
    let fallback := (0, hash.digestInput state.fallback)
    let forgery := out.forgery
    let forgedEpoch := forgery.1
    let forgedPayload := forgery.2
    let forgedMessage := forgedPayload.1
    let forgedSignature := forgedPayload.2
    match out.history forgedEpoch with
    | some (msg, some signature) =>
      match enc.value pp msg signature.randomizer forgedEpoch,
        enc.value pp forgedMessage forgedSignature.randomizer forgedEpoch with
      | some honestWord, some forgedWord =>
        if hword : honestWord = forgedWord then
          match Security.findUnequalCoordinate signature.ots forgedSignature.ots with
          | none => return fallback
          | some i =>
            match hash.findChainCollision pp forgedEpoch i (honestWord i)
                (2 ^ w - 1 - (honestWord i).val) (signature.ots i)
                (forgedSignature.ots i) with
            | none => return fallback
            | some d =>
              let tweak := hash.chainTweak (forgedEpoch, i,
                ⟨(honestWord i).val + d.val, by omega⟩)
              let first := hash.digestInput
                (hash.chain pp forgedEpoch i (honestWord i) d (signature.ots i))
              let second := hash.digestInput
                (hash.chain pp forgedEpoch i (honestWord i) d (forgedSignature.ots i))
              return (registeredIndex state.targets tweak first, second)
        else return fallback
      | _, _ => return fallback
    | _ => return fallback

/-- Executable second-chain target-collision reduction, kept separate from the first chain. -/
def secondChainTargetCollisionReduction [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (advGXMSS : SchemeAdversary PP H M R h v) : SM_DT_TCR_Adversary (chainTCRProblem hash) where
  State := TCRKeyState PP T X H h v
  choose := tcrChainSetup hash _
  forge state pp := do
    let sk : GXMSS.SecretKey PP H h v := ⟨pp, state.starts, state.endpoints⟩
    let pk : GXMSS.PublicKey PP H := ⟨hash.merkleRoot pp state.endpoints, pp⟩
    let out ← runWithKeys hash enc K advGXMSS pk sk
    let fallback := (0, hash.digestInput state.fallback)
    let forgery := out.forgery
    let forgedEpoch := forgery.1
    let forgedPayload := forgery.2
    let forgedMessage := forgedPayload.1
    let forgedSignature := forgedPayload.2
    match out.history forgedEpoch with
    | some (msg, some signature) =>
      match enc.value pp msg signature.randomizer forgedEpoch,
        enc.value pp forgedMessage forgedSignature.randomizer forgedEpoch with
      | some honestWord, some forgedWord =>
        match findSmallerCoordinate honestWord forgedWord with
        | none => return fallback
        | some i =>
          match hash.findChainCut pp forgedEpoch i (forgedWord i) (honestWord i)
              (2 ^ w - 1) (signature.ots i) (forgedSignature.ots i) with
          | some (.inr d) =>
            let advanced := hash.chain pp forgedEpoch i (forgedWord i)
              ((honestWord i).val - (forgedWord i).val) (forgedSignature.ots i)
            let tweak := hash.chainTweak (forgedEpoch, i,
              ⟨(honestWord i).val + d.val, by omega⟩)
            let first := hash.digestInput
              (hash.chain pp forgedEpoch i (honestWord i) d (signature.ots i))
            let second := hash.digestInput
              (hash.chain pp forgedEpoch i (honestWord i) d advanced)
            return (registeredIndex state.targets tweak first, second)
          | _ => return fallback
      | _, _ => return fallback
    | _ => return fallback

private def encodingSigningOracle
    (hash : HashInstance PP T X H h w v)
    (sk : GXMSS.SecretKey PP H h v) :
    QueryImpl (SyncSignatureUnforgeability.signingSpec (Epoch h) M (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M (GXMSS.Signature R H h v))
        (OracleComp (unifSpec + Encoding.TargetCollisionResistance.challengeSpec
          M R (Epoch h) v (2 ^ w)))) := fun q history =>
  match history q.1 with
  | some _ => pure (none, history)
  | none => do
      let answer ← liftM ((unifSpec + Encoding.TargetCollisionResistance.challengeSpec
        M R (Epoch h) v (2 ^ w)).query (.inr (q.2, q.1)))
      let signature := answer.map (GXMSS.signatureOfWord hash sk q.1)
      return (signature, Function.update history q.1 (some (q.2, signature)))

private theorem encodingSigningOracle_used
    (hash : HashInstance PP T X H h w v)
    (sk : GXMSS.SecretKey PP H h v)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (ep : Epoch h) (msg first : M) (answer : Option (GXMSS.Signature R H h v))
    (hused : history ep = some (first, answer)) :
    (encodingSigningOracle hash sk (ep, msg)).run history = pure (none, history) := by
  change encodingSigningOracle hash sk (ep, msg) history = _
  simp [encodingSigningOracle, hused]

private theorem encodingSigningOracle_unused
    (hash : HashInstance PP T X H h w v)
    (sk : GXMSS.SecretKey PP H h v)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (ep : Epoch h) (msg : M) (hunused : history ep = none) :
    (encodingSigningOracle hash sk (ep, msg)).run history = (do
      let answer ← ((unifSpec + TargetCollisionResistance.challengeSpec M R
        (Epoch h) v (2 ^ w)).query (.inr (msg, ep)))
      let signature := answer.map (GXMSS.signatureOfWord hash sk ep)
      pure (signature, Function.update history ep (some (msg, signature)))) := by
  change encodingSigningOracle hash sk (ep, msg) history = _
  simp [encodingSigningOracle, hunused]

/-- A source signing handler that retains the successful or exhausted encoding record alongside
the exact signing history.  Its first projection is the ordinary source signing handler. -/
private def encodingSourceCoupledImpl [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) ProbComp) :=
  fun q state =>
    match q with
    | .inl uniform => do
        let answer ← liftM ((unifSpec.query uniform) : ProbComp _)
        return (answer, state)
    | .inr (ep, msg) =>
        match state.1 ep with
        | some _ => pure (none, state)
        | none => do
            let answer ← enc.retry ($ᵗ R) sk.seed msg ep K
            let signature := answer.map (GXMSS.signatureOfWord hash sk ep)
            let history := Function.update state.1 ep (some (msg, signature))
            let transcript := state.2 ++ [⟨ep, msg, answer⟩]
            return (signature, (history, transcript))

private def sourceSigningImpl [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) ProbComp) +
    SyncSignatureUnforgeability.signingOracle (GXMSS.scheme hash enc K) sk

/-- The coupled source handler projects to the exact admitted synchronized-signature
handler, including returned failure. -/
private theorem encodingSourceCoupledImpl_proj [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Domain)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) :
    Prod.map id Prod.fst <$> (encodingSourceCoupledImpl hash enc K sk q).run state =
      (sourceSigningImpl hash enc K sk q).run state.1 := by
  cases q with
  | inl uniform =>
    change Prod.map id Prod.fst <$> encodingSourceCoupledImpl hash enc K sk (.inl uniform)
      state = sourceSigningImpl hash enc K sk (.inl uniform) state.1
    dsimp [encodingSourceCoupledImpl, sourceSigningImpl]
    simp [map_eq_bind_pure_comp, bind_assoc]
    rfl
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change Prod.map id Prod.fst <$> encodingSourceCoupledImpl hash enc K sk (.inr (ep, msg))
      state = sourceSigningImpl hash enc K sk (.inr (ep, msg)) state.1
    by_cases hused : state.1 ep = none
    · dsimp [encodingSourceCoupledImpl, sourceSigningImpl,
        SyncSignatureUnforgeability.signingOracle]
      rw [hused]
      simp [GXMSS.scheme, GXMSS.sign, map_eq_bind_pure_comp, bind_assoc]
    · cases hentry : state.1 ep with
      | none => exact False.elim (hused hentry)
      | some entry =>
        dsimp [encodingSourceCoupledImpl, sourceSigningImpl,
          SyncSignatureUnforgeability.signingOracle]
        rw [hentry]
        simp

/-- First-request consumption agrees between the synchronized signing history and the
encoding target transcript. -/
private def encodingHistoryMatches
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (transcript : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) : Prop :=
  ∀ ep, (history ep = none ↔ TargetCollisionResistance.used transcript ep = false)

private theorem encodingHistoryMatches_empty :
    encodingHistoryMatches (H := H) (M := M) (R := R) (h := h) (v := v) (w := w)
      (SyncSignatureUnforgeability.emptyHistory (E := Epoch h) (M := M)
        (S := GXMSS.Signature R H h v))
      ([] : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) := by
  intro ep
  simp [SyncSignatureUnforgeability.emptyHistory, TargetCollisionResistance.used]

private theorem encodingSourceCoupledImpl_preserves_match [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Domain)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hmatch : encodingHistoryMatches state.1 state.2)
    (out : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Range q ×
      (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support ((encodingSourceCoupledImpl hash enc K sk q).run state)) :
    encodingHistoryMatches out.2.1 out.2.2 := by
  cases q with
  | inl uniform =>
    change out ∈ support
      ((unifSpec.query uniform : ProbComp _) >>= fun answer => pure (answer, state)) at hout
    simp only [mem_support_bind_iff] at hout
    obtain ⟨answer, _, hreturn⟩ := hout
    simp only [support_pure, Set.mem_singleton_iff] at hreturn
    subst out
    exact hmatch
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change out ∈ support (encodingSourceCoupledImpl hash enc K sk (.inr (ep, msg))
      state) at hout
    dsimp [encodingSourceCoupledImpl] at hout
    by_cases hused : state.1 ep = none
    · rw [hused] at hout
      change out ∈ support
        ((enc.retry ($ᵗ R) sk.seed msg ep K) >>= fun answer =>
          pure (answer.map (GXMSS.signatureOfWord hash sk ep),
            (Function.update state.1 ep
              (some (msg, answer.map (GXMSS.signatureOfWord hash sk ep))),
              state.2 ++ [⟨ep, msg, answer⟩]))) at hout
      obtain ⟨answer, _, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
      have hreturn' := (mem_support_pure_iff _ _).mp hreturn
      subst out
      intro other
      by_cases heq : other = ep
      · subst other
        simp [Function.update, TargetCollisionResistance.used]
      · have hprev := hmatch other
        have hne : ep ≠ other := Ne.symm heq
        simpa [Function.update, heq, hne, TargetCollisionResistance.used,
          List.any_append] using hprev
    · cases hentry : state.1 ep with
      | none => exact False.elim (hused hentry)
      | some entry =>
        rw [hentry] at hout
        simp only [support_pure, Set.mem_singleton_iff] at hout
        subst out
        exact hmatch

/-- Forgetting only the auxiliary encoding transcript recovers the actual source interaction. -/
private theorem encodingSourceCoupled_run_proj [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pk : GXMSS.PublicKey PP H) :
    Prod.map id Prod.fst <$>
      (simulateQ (encodingSourceCoupledImpl hash enc K sk) (adv.forge pk)).run
        (SyncSignatureUnforgeability.emptyHistory, []) =
      (simulateQ (sourceSigningImpl hash enc K sk) (adv.forge pk)).run
        SyncSignatureUnforgeability.emptyHistory := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (encodingSourceCoupledImpl hash enc K sk) (sourceSigningImpl hash enc K sk)
    Prod.fst (fun q state => encodingSourceCoupledImpl_proj hash enc K sk q state)
    (adv.forge pk) (SyncSignatureUnforgeability.emptyHistory, [])

private def encodingGameInnerImpl
    (hash : HashInstance PP T X H h w v)
    (sk : GXMSS.SecretKey PP H h v) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))
        (OracleComp (unifSpec + TargetCollisionResistance.challengeSpec
          M R (Epoch h) v (2 ^ w)))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (unifSpec +
    TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) (OracleComp (unifSpec +
          TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))) +
    encodingSigningOracle (M := M) (R := R) (h := h) (w := w) (v := v) hash sk

/-- The fixed reduction's signing handler interpreted by the authoritative encoding challenge
oracle, with both state components retained. -/
private def encodingGameCoupledImpl [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (sk : GXMSS.SecretKey PP H h v) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) ProbComp) :=
  ((TargetCollisionResistance.oracles (encodingTCRProblem hash enc qs K) sk.seed).mapStateTBase
    (encodingGameInnerImpl (M := M) (R := R) hash sk)).flattenStateT

private theorem encodingGameCoupledImpl_eq_source_of_capacity [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Domain)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hmatch : encodingHistoryMatches state.1 state.2)
    (hspace : q.isRight = true → state.2.length < qs) :
    (encodingGameCoupledImpl hash enc qs K sk q).run state =
      (encodingSourceCoupledImpl hash enc K sk q).run state := by
  cases q with
  | inl uniform =>
    change encodingGameCoupledImpl hash enc qs K sk (.inl uniform) state =
      encodingSourceCoupledImpl hash enc K sk (.inl uniform) state
    simp [encodingGameCoupledImpl, encodingGameInnerImpl,
      encodingSourceCoupledImpl, TargetCollisionResistance.oracles,
      QueryImpl.flattenStateT, QueryImpl.mapStateTBase]
    dsimp [StateT.mk]
    rfl
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change encodingGameCoupledImpl hash enc qs K sk (.inr (ep, msg)) state =
      encodingSourceCoupledImpl hash enc K sk (.inr (ep, msg)) state
    by_cases hused : state.1 ep = none
    · have hfresh : TargetCollisionResistance.used state.2 ep = false :=
        (hmatch ep).mp hused
      have hlen : state.2.length < qs := hspace (by simp)
      have hcap := encodingFreshQuery_capacity qs state.2 ep hlen hfresh
      simp only [add_apply_inr, InductiveMerkleTree.range_def,
        encodingGameCoupledImpl, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase, TargetCollisionResistance.oracles,
        QueryImpl.ofLift_eq_id', encodingTCRProblem, encodingGameInnerImpl,
        QueryImpl.add_apply_inr, StateT.run_mk, map_eq_bind_pure_comp,
        encodingSourceCoupledImpl, hused, bind_pure_comp]
      dsimp [StateT.mk]
      rw [encodingSigningOracle_unused hash sk state.1 ep msg hused]
      simp [simulateQ_bind, simulateQ_query,
        TargetCollisionResistance.challengeOracle, hcap,
        TargetCollisionResistance.finish, TargetCollisionResistance.retry,
        map_eq_bind_pure_comp, bind_assoc]
    · cases hentry : state.1 ep with
      | none => exact False.elim (hused hentry)
      | some entry =>
        simp only [add_apply_inr, InductiveMerkleTree.range_def,
          encodingGameCoupledImpl, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, TargetCollisionResistance.oracles,
          QueryImpl.ofLift_eq_id', encodingGameInnerImpl,
          QueryImpl.add_apply_inr, StateT.run_mk,
          encodingSourceCoupledImpl, hentry]
        dsimp [StateT.mk]
        rw [encodingSigningOracle_used hash sk state.1 ep msg entry.1 entry.2 hentry]
        simp

private theorem encodingSourceCoupledImpl_length [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Domain)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (out : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Range q ×
      (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support ((encodingSourceCoupledImpl hash enc K sk q).run state)) :
    out.2.2.length ≤ state.2.length + (if q matches .inr _ then 1 else 0) := by
  cases q with
  | inl uniform =>
    change out ∈ support
      ((unifSpec.query uniform : ProbComp _) >>= fun answer => pure (answer, state)) at hout
    obtain ⟨answer, _, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
    have heq := (mem_support_pure_iff _ _).mp hreturn
    subst out
    simp
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change out ∈ support (encodingSourceCoupledImpl hash enc K sk (.inr (ep, msg))
      state) at hout
    dsimp [encodingSourceCoupledImpl] at hout
    cases hentry : state.1 ep with
    | some entry =>
      rw [hentry] at hout
      have heq := (mem_support_pure_iff _ _).mp hout
      subst out
      simp
    | none =>
      rw [hentry] at hout
      obtain ⟨answer, _, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
      have heq := (mem_support_pure_iff _ _).mp hreturn
      subst out
      simp

/-- Every successful signing reply in the coupled state names an admitted, successful
encoding challenge record and its exact word/randomizer. -/
private def encodingSuccessfulRecordsMatch
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) : Prop :=
  ∀ ep msg sig, state.1 ep = some (msg, some sig) →
    ∃ wr, (⟨ep, msg, some wr⟩ : TargetCollisionResistance.Record M R
      (Epoch h) v (2 ^ w)) ∈ state.2 ∧
      sig = GXMSS.signatureOfWord hash sk ep wr ∧
      enc.value sk.seed msg wr.2 ep = some wr.1

private theorem encodingSuccessfulRecordsMatch_empty
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v) :
    encodingSuccessfulRecordsMatch hash enc sk
      (SyncSignatureUnforgeability.emptyHistory, []) := by
  intro ep msg sig hrecord
  simp [SyncSignatureUnforgeability.emptyHistory] at hrecord

private theorem encodingSourceCoupledImpl_preserves_successfulRecords [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Domain)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hinv : encodingSuccessfulRecordsMatch hash enc sk state)
    (out : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Range q ×
      (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support ((encodingSourceCoupledImpl hash enc K sk q).run state)) :
    encodingSuccessfulRecordsMatch hash enc sk out.2 := by
  cases q with
  | inl uniform =>
    change out ∈ support
      ((unifSpec.query uniform : ProbComp _) >>= fun answer => pure (answer, state)) at hout
    obtain ⟨answer, _, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
    have heq := (mem_support_pure_iff _ _).mp hreturn
    subst out
    exact hinv
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change out ∈ support (encodingSourceCoupledImpl hash enc K sk (.inr (ep, msg))
      state) at hout
    dsimp [encodingSourceCoupledImpl] at hout
    cases hentry : state.1 ep with
    | some entry =>
      rw [hentry] at hout
      have heq := (mem_support_pure_iff _ _).mp hout
      subst out
      exact hinv
    | none =>
      rw [hentry] at hout
      obtain ⟨answer, hanswer, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
      have heq := (mem_support_pure_iff _ _).mp hreturn
      subst out
      intro other first signature hrecord
      by_cases heq : other = ep
      · subst other
        cases answer with
        | none => simp [Function.update] at hrecord
        | some wr =>
          have hpair : first = msg ∧ signature = GXMSS.signatureOfWord hash sk ep wr := by
            simpa [Function.update] using hrecord.symm
          rcases hpair with ⟨hfirst, hsignature⟩
          refine ⟨wr, ?_, hsignature, ?_⟩
          · simp [hfirst]
          · simpa [hfirst] using IncomparableEncoding.Retry.value_eq_some_of_mem_retry
              enc ($ᵗ R) sk.seed msg ep K wr.1 wr.2 hanswer
      · have hold : state.1 other = some (first, some signature) := by
          simpa [Function.update, heq] using hrecord
        obtain ⟨wr, hmem, hsig, hword⟩ := hinv other first signature hold
        exact ⟨wr, List.mem_append.mpr (Or.inl hmem), hsig, hword⟩

/-- On a returned successful-record difference, the coupled transcript makes the exact
fixed encoding reduction candidate win the authoritative target-collision predicate. -/
private theorem encodingSuccessfulDifference_valid [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v) (out : Result PP H M R h v)
    (transcript : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hseed : out.pk.seed = sk.seed)
    (hrecords : encodingSuccessfulRecordsMatch hash enc sk (out.history, transcript))
    (hdiff : successfulEncodingDifference hash enc K out = true) :
    TargetCollisionResistance.valid enc sk.seed transcript
      (out.forgery.2.1, out.forgery.2.2.randomizer, out.forgery.1) = true := by
  cases hsource : forgedEpochSource out with
  | unused => simp [successfulEncodingDifference, hsource] at hdiff
  | failedConsumed msg => simp [successfulEncodingDifference, hsource] at hdiff
  | successful msg sig =>
    have hd : gameOneObservation hash enc K out = true ∧
        (!gameTwoObservation hash enc K out) = true := by
      simpa only [successfulEncodingDifference, hsource, Bool.and_true,
        Bool.and_eq_true] using hdiff
    have hwin : gameOneObservation hash enc K out = true := by
      exact hd.1
    have hremoved : gameTwoObservation hash enc K out = false := by
      cases htwo : gameTwoObservation hash enc K out <;> simp [htwo] at hd ⊢
    have hrecord := history_of_successful_source out msg sig hsource
    obtain ⟨wr, hmem, hsig, hvalue⟩ := hrecords out.forgery.1 msg sig hrecord
    have hhonest : ∃ word, enc.value out.pk.seed msg sig.randomizer
        out.forgery.1 = some word := by
      refine ⟨wr.1, ?_⟩
      simpa [hseed, hsig, GXMSS.signatureOfWord] using hvalue
    obtain ⟨word, hhonestWord, hforgedWord, hne⟩ :=
      successful_encoding_difference_witness hash enc K out msg sig hsource
        hhonest hwin hremoved
    have hword : word = wr.1 := by
      rw [hseed] at hhonestWord
      have hsigR : sig.randomizer = wr.2 := by simp [hsig, GXMSS.signatureOfWord]
      rw [hsigR, hvalue] at hhonestWord
      exact Option.some.inj hhonestWord.symm
    apply encodingTargetValid_of_successful_record enc sk.seed transcript
      out.forgery.1 msg out.forgery.2.1 wr.2 out.forgery.2.2.randomizer wr.1 hmem
    · simpa [hseed, hword] using hforgedWord
    · simpa [hsig, GXMSS.signatureOfWord] using hne

private theorem encodingSourceCoupled_run_successfulRecords
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pk : GXMSS.PublicKey PP H)
    (out : (Epoch h × (M × GXMSS.Signature R H h v)) ×
      (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support
      ((simulateQ (encodingSourceCoupledImpl hash enc K sk) (adv.forge pk)).run
        (SyncSignatureUnforgeability.emptyHistory, []))) :
    encodingSuccessfulRecordsMatch hash enc sk out.2 := by
  classical
  apply OracleComp.simulateQ_run_preservesInv
    (encodingSourceCoupledImpl hash enc K sk)
    (encodingSuccessfulRecordsMatch hash enc sk)
    (fun q state hstate answer hans =>
      encodingSourceCoupledImpl_preserves_successfulRecords hash enc K sk q state
        hstate answer hans)
    (adv.forge pk) (SyncSignatureUnforgeability.emptyHistory, [])
  · intro ep msg sig hrecord
    simp [SyncSignatureUnforgeability.emptyHistory] at hrecord
  · exact hout

/-- Honest source generation with the challenge transcript retained only for the coupling. -/
private def encodingSourceCoupledProgram [SampleableType H] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    ProbComp (Result PP H M R h v ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) := do
  let pp ← (HashInstance.thf hash).seedGen
  let starts ← GXMSS.sampleStarts H h v
  let keys := GXMSS.keys hash pp starts
  let (forgery, state) ←
    (simulateQ (encodingSourceCoupledImpl hash enc K keys.2) (adv.forge keys.1)).run
      (SyncSignatureUnforgeability.emptyHistory, [])
  return (⟨keys.1, keys.2, forgery, state.1⟩, state.2)

private theorem encodingSourceCoupledProgram_proj [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    Prod.fst <$> encodingSourceCoupledProgram hash enc K adv =
      sourceProgram hash enc K adv := by
  simp only [encodingSourceCoupledProgram, sourceProgram, GXMSS.keygen,
    runWithKeys, map_bind, map_pure, bind_assoc]
  congr 1
  funext pp
  congr 1
  funext starts
  let keys := GXMSS.keys hash pp starts
  simp only [pure_bind]
  have hproj := congrArg
    (fun c => (fun z => (⟨keys.1, keys.2, z.1, z.2⟩ : Result PP H M R h v)) <$> c)
    (encodingSourceCoupled_run_proj hash enc K keys.2 adv keys.1)
  simpa only [sourceSigningImpl, Functor.map_map, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq] using hproj

private theorem encodingSourceCoupledProgram_support [SampleableType H] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (out : Result PP H M R h v ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hout : out ∈ support (encodingSourceCoupledProgram hash enc K adv)) :
    out.1.pk.seed = out.1.sk.seed ∧
      encodingSuccessfulRecordsMatch hash enc out.1.sk (out.1.history, out.2) := by
  unfold encodingSourceCoupledProgram at hout
  obtain ⟨pp, _, hrest⟩ := support_bind_exists hout
  obtain ⟨starts, _, hrest⟩ := support_bind_exists hrest
  obtain ⟨runout, hrun, hret⟩ := support_bind_exists hrest
  have heq := (mem_support_pure_iff _ _).mp hret
  subst out
  constructor
  · rfl
  · exact encodingSourceCoupled_run_successfulRecords hash enc K
      (GXMSS.keys hash pp starts).2 adv (GXMSS.keys hash pp starts).1 runout hrun

/-- A pathwise source signing bound leaves strict transcript room before each permitted
signing call, so the actual challenge handler fits the `qs`-record problem. -/
private theorem encodingGameCoupled_run_eq_source_of_bound {α : Type} [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (oa : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec
      (Epoch h) M (GXMSS.Signature R H h v)) α)
    (budget : ℕ)
    (hbound : oa.IsQueryBoundP (fun q => q.isRight = true) budget)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hmatch : encodingHistoryMatches state.1 state.2)
    (hlen : state.2.length + budget ≤ qs) :
    (simulateQ (encodingGameCoupledImpl hash enc qs K sk) oa).run state =
      (simulateQ (encodingSourceCoupledImpl hash enc K sk) oa).run state := by
  induction oa using OracleComp.inductionOn generalizing budget state with
  | pure value => rfl
  | query_bind q next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind]
    have hspace : q.isRight = true → state.2.length < qs := by
      intro hsign
      cases q with
      | inl uniform => simp at hsign
      | inr signing =>
        have hpositive : 0 < budget := hbound.1.resolve_left (by simp)
        omega
    rw [encodingGameCoupledImpl_eq_source_of_capacity hash enc qs K sk q state
      hmatch hspace]
    apply bind_congr_of_forall_mem_support
    intro output houtput
    have hmatch' := encodingSourceCoupledImpl_preserves_match hash enc K sk q
      state hmatch output houtput
    have hstep := encodingSourceCoupledImpl_length hash enc K sk q state output houtput
    have hnext : output.2.2.length +
        (if q.isRight = true then budget - 1 else budget) ≤ qs := by
      cases q with
      | inl uniform =>
        simp only [Sum.isRight, Bool.false_eq_true, ite_false] at hstep ⊢
        omega
      | inr signing =>
        simp only [Sum.isRight, ite_true] at hstep ⊢
        have hpositive : 0 < budget := hbound.1.resolve_left (by simp)
        omega
    exact ih output.1 (if q.isRight = true then budget - 1 else budget)
      (hbound.2 output.1) output.2 hmatch' hnext

/-- Encoding target-collision reduction using only the successful source transcript. -/
noncomputable def encodingTargetCollisionReduction [SampleableType H] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (advGXMSS : SchemeAdversary PP H M R h v) :
    Encoding.TargetCollisionResistance.Adversary (encodingTCRProblem hash enc qs K) where
  find pp := do
    let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
    let keys := GXMSS.keys hash pp starts
    let impl : QueryImpl
        (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
          (GXMSS.Signature R H h v))
        (StateT (SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v)) (OracleComp (unifSpec +
            Encoding.TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))) :=
      (QueryImpl.ofLift unifSpec (OracleComp (unifSpec +
        Encoding.TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))).liftTarget
          (StateT (SyncSignatureUnforgeability.History (Epoch h) M
            (GXMSS.Signature R H h v)) (OracleComp (unifSpec +
              Encoding.TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))) +
        encodingSigningOracle (M := M) (R := R) (h := h) (w := w) (v := v) hash keys.2
    let (forgery, _history) ←
      (simulateQ impl (advGXMSS.forge keys.1)).run SyncSignatureUnforgeability.emptyHistory
    let forgedEpoch := forgery.1
    let forgedPayload := forgery.2
    let forgedMessage := forgedPayload.1
    let forgedSignature := forgedPayload.2
    return (forgedMessage, forgedSignature.randomizer, forgedEpoch)

private def encodingFinalFind
    (out : Result PP H M R h v) :
    OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R
      (Epoch h) v (2 ^ w)) (M × R × Epoch h) :=
  pure (out.forgery.2.1, out.forgery.2.2.randomizer, out.forgery.1)

private noncomputable def encodingTargetTail [SampleableType R]
    [DecidableEq M] [DecidableEq R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (out : Result PP H M R h v ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) : ProbComp Bool := do
  let (collision, transcript) ←
    (simulateQ
      (TargetCollisionResistance.oracles (encodingTCRProblem hash enc qs K) out.1.sk.seed)
      (encodingFinalFind out.1)).run out.2
  return TargetCollisionResistance.valid enc out.1.sk.seed transcript collision

private theorem encodingTargetTail_successfulDifference
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (out : Result PP H M R h v ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hseed : out.1.pk.seed = out.1.sk.seed)
    (hrecords : encodingSuccessfulRecordsMatch hash enc out.1.sk
      (out.1.history, out.2))
    (hdiff : successfulEncodingDifference hash enc K out.1 = true) :
    encodingTargetTail hash enc qs K out = pure true := by
  have hvalid := encodingSuccessfulDifference_valid hash enc K out.1.sk
    out.1 out.2 hseed hrecords hdiff
  cases hsource : forgedEpochSource out.1 with
  | unused => simp [successfulEncodingDifference, hsource] at hdiff
  | failedConsumed msg => simp [successfulEncodingDifference, hsource] at hdiff
  | successful msg sig =>
    simp [encodingTargetTail, encodingFinalFind, hvalid, simulateQ_pure]

private theorem encodingOuter_liftStarts [SampleableType H] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (pp : PP) :
    (simulateQ (TargetCollisionResistance.oracles (encodingTCRProblem hash enc qs K) pp)
      (OracleComp.liftComp (GXMSS.sampleStarts H h v)
        (unifSpec + TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))).run
      ([] : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) =
    (fun starts => (starts, ([] : TargetCollisionResistance.Transcript M R
      (Epoch h) v (2 ^ w)))) <$> GXMSS.sampleStarts H h v := by
  simp [TargetCollisionResistance.oracles, QueryImpl.simulateQ_add_liftM_left,
    simulateQ_liftTarget]

private theorem encodingOuter_inner_run_eq_source [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs)
    (pp : PP) (starts : Epoch h → Fin v → H) :
    let keys := GXMSS.keys hash pp starts
    (simulateQ
      ((TargetCollisionResistance.oracles (encodingTCRProblem hash enc qs K) pp).mapStateTBase
        (encodingGameInnerImpl (M := M) (R := R) hash keys.2)).flattenStateT
      (adv.forge keys.1)).run (SyncSignatureUnforgeability.emptyHistory, []) =
    (simulateQ (encodingSourceCoupledImpl hash enc K keys.2)
      (adv.forge keys.1)).run (SyncSignatureUnforgeability.emptyHistory, []) := by
  dsimp
  change (simulateQ (encodingGameCoupledImpl hash enc qs K (GXMSS.keys hash pp starts).2)
    (adv.forge (GXMSS.keys hash pp starts).1)).run
      (SyncSignatureUnforgeability.emptyHistory, []) = _
  exact encodingGameCoupled_run_eq_source_of_bound hash enc qs K
    (GXMSS.keys hash pp starts).2 (adv.forge (GXMSS.keys hash pp starts).1) qs
    (hbound (GXMSS.keys hash pp starts).1)
    (SyncSignatureUnforgeability.emptyHistory, [])
    encodingHistoryMatches_empty (by simp)

private theorem encodingNested_run_eq_source [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs)
    (pp : PP) (starts : Epoch h → Fin v → H) :
    let keys := GXMSS.keys hash pp starts
    (simulateQ (TargetCollisionResistance.oracles (encodingTCRProblem hash enc qs K) pp)
      ((simulateQ
        ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec +
          TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))).liftTarget
            (StateT (SyncSignatureUnforgeability.History (Epoch h) M
              (GXMSS.Signature R H h v)) (OracleComp (unifSpec +
                TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))) +
          encodingSigningOracle (M := M) (R := R) (h := h) (w := w) (v := v) hash keys.2)
        (adv.forge keys.1)).run SyncSignatureUnforgeability.emptyHistory)).run
      ([] : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) =
    (fun z => ((z.1, z.2.1), z.2.2)) <$>
      (simulateQ (encodingSourceCoupledImpl hash enc K keys.2)
        (adv.forge keys.1)).run (SyncSignatureUnforgeability.emptyHistory, []) := by
  dsimp
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change (fun z => ((z.1, z.2.1), z.2.2)) <$>
      (simulateQ (encodingGameCoupledImpl hash enc qs K (GXMSS.keys hash pp starts).2)
        (adv.forge (GXMSS.keys hash pp starts).1)).run
        (SyncSignatureUnforgeability.emptyHistory, []) = _
  exact congrArg (fun c => (fun z => ((z.1, z.2.1), z.2.2)) <$> c)
    (encodingGameCoupled_run_eq_source_of_bound hash enc qs K
      (GXMSS.keys hash pp starts).2 (adv.forge (GXMSS.keys hash pp starts).1) qs
      (hbound (GXMSS.keys hash pp starts).1)
      (SyncSignatureUnforgeability.emptyHistory, [])
      encodingHistoryMatches_empty (by simp))

private theorem encodingTargetExperiment_eq_coupled
    [SampleableType H] [SampleableType R]
    [DecidableEq M] [DecidableEq R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    TargetCollisionResistance.experiment
      (encodingTargetCollisionReduction hash enc qs K adv) =
      encodingSourceCoupledProgram hash enc K adv >>= encodingTargetTail hash enc qs K := by
  unfold TargetCollisionResistance.experiment encodingTargetCollisionReduction
  unfold encodingSourceCoupledProgram encodingTargetTail
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]
  simp only [encodingOuter_liftStarts]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  apply congrArg (fun (f : PP → ProbComp Bool) => hash.thf.seedGen >>= f)
  funext pp
  apply congrArg (fun (f : (Epoch h → Fin v → H) → ProbComp Bool) =>
    GXMSS.sampleStarts H h v >>= f)
  funext starts
  rw [encodingNested_run_eq_source hash enc qs K adv hbound pp starts]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rfl

end GXMSS.Reductions
