/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
import all HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
import all HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Auxiliary.Encoding
import all HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
public import HashSig.GXMSS.Security.Reductions.Problems
import all HashSig.GXMSS.Security.Reductions.Problems
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Target registration and collision reductions

Honest chain and tree targets are registered before seed revelation. The named reductions
return accepted registration indices and oriented collision inputs.
-/

public section
namespace GXMSS.Reductions
open Encoding ENNReal OracleComp OracleSpec GXMSS.Security TweakableHash
variable {PP T X H M R E S : Type} {h w v n radix : ℕ}
/-- Local registration state used while choosing honest SM-DT-TCR targets. -/
abbrev TCRSetupM (hash : HashInstance PP T X H h w v) (targets : ℕ) :=
  StateT (List (T × X)) (OracleComp (unifSpec + (SM_DT_TCR_challengeSpec T X H +
    collectionSpec (SM_DT_TCR_Problem.standalone hash.thf targets).thColl)))
/-- Key material obtained by registering every honest target before the public seed is revealed. -/
structure TCRKeyState (PP T X H : Type) (h v : ℕ) where
  /-- Sampled initial value for every epoch and chain. -/
  starts : Fin (2 ^ h) → Fin v → H
  /-- Endpoint array returned by the registered chain computations. -/
  endpoints : Fin (2 ^ h) → Fin v → H
  /-- Root digest of the registered honest Merkle tree. -/
  root : H
  /-- Accepted honest tweak/input pairs in registration order. -/
  targets : List (T × X)
  /-- Independently sampled fallback digest retained by the reduction. -/
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
          match GXMSS.Security.findUnequalCoordinate signature.ots forgedSignature.ots with
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

end GXMSS.Reductions
