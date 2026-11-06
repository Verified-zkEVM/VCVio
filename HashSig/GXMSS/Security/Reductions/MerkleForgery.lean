/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
import all HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Merkle
import all HashSig.GXMSS.Merkle
public import HashSig.GXMSS.Security.Auxiliary.CompleteBounds
import all HashSig.GXMSS.Security.Auxiliary.CompleteBounds
public import HashSig.GXMSS.Security.Auxiliary.Encoding
import all HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.HashWitnesses
import all HashSig.GXMSS.Security.Auxiliary.HashWitnesses
public import HashSig.GXMSS.Security.Auxiliary.SigningQueries
import all HashSig.GXMSS.Security.Auxiliary.SigningQueries
public import HashSig.GXMSS.Security.Auxiliary.SourcePartition
import all HashSig.GXMSS.Security.Auxiliary.SourcePartition
public import HashSig.GXMSS.Security.Reductions.Experiments
import all HashSig.GXMSS.Security.Reductions.Experiments
public import HashSig.GXMSS.Security.Reductions.TCRSimulation
import all HashSig.GXMSS.Security.Reductions.TCRSimulation
public import Lean.Elab.Command
public import Lean.Util.CollectAxioms
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Uniqueness
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# Merkle forgery collision witnesses

A valid complete-tree forgery with a different opening yields a collision against an honest
registered Merkle target.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The exact universally closed Merkle-forgery proposition audited below. -/
@[expose]
def ValidForgeryYieldsMerkleCollisionStatement [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (pk : GXMSS.PublicKey PP H) (sk : GXMSS.SecretKey PP H h v)
    (epoch : Fin (2 ^ h))
    (forgedMessage : M) (forgedRandomizer : R) (forgedWord : Codeword v (2 ^ w))
    (forgedOTS : Fin v → H) (forgedPath : Fin h → H) : Prop :=
  let honestEndpoints := sk.endpoints
  let honestLeaf := honestEndpoints epoch
  let honestPath := hash.authPath pk.seed honestEndpoints epoch
  let forgedLeaf := fun i =>
    hash.chain pk.seed epoch i (forgedWord i)
      (2 ^ w - 1 - (forgedWord i).val) (forgedOTS i)
  (GXMSS.scheme hash enc K).Generated ProbCompRuntime.probComp (pk, sk) →
  GXMSS.Consistent hash pk sk →
  enc.value pk.seed forgedMessage forgedRandomizer epoch = some forgedWord →
  GXMSS.verify hash enc pk epoch forgedMessage
    ⟨forgedRandomizer, forgedOTS, forgedPath⟩ = true →
  hash.recoverRoot pk.seed epoch honestLeaf honestPath = pk.root →
  hash.recoverRoot pk.seed epoch forgedLeaf forgedPath = pk.root →
  (honestLeaf, honestPath) ≠ (forgedLeaf, forgedPath) →
  ∃ collision : GXMSS.Security.HashCollision T X,
    hash.findMerkleCollision pk.seed epoch honestLeaf forgedLeaf honestPath forgedPath =
      some collision ∧
    collision.Sound hash.thf pk.seed ∧
    (collision.tweak, collision.first) ∈
      hash.merkleOpeningQueries pk.seed epoch honestLeaf honestPath ∧
    (collision.tweak, collision.second) ∈
      hash.merkleOpeningQueries pk.seed epoch forgedLeaf forgedPath ∧
    ((honestLeaf ≠ forgedLeaf ∧
        collision = ⟨hash.treeTweak (0, epoch), hash.vectorInput honestLeaf,
          hash.vectorInput forgedLeaf⟩) ∨
      ∃ (z : Fin h) (u : H × H),
        collision = ⟨hash.treeTweak (Merkle.parentAddress epoch z),
          hash.pairInput (hash.honestMerkleChildren pk.seed honestEndpoints epoch z),
          hash.pairInput u⟩ ∧
        hash.honestMerkleChildren pk.seed honestEndpoints epoch z ≠ u)

/-- A generated-key, accepted forgery with a different complete raw opening yields the existing
computable honest-first Merkle collision. The statement includes raw-leaf and path-only
disagreement, and at height zero the `Fin h` branch is empty. It assumes neither unequal leaf
digests nor hash injectivity, a secret predecessor, or reduction challenge timing. -/
theorem ValidForgeryYieldsMerkleCollision [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (pk : GXMSS.PublicKey PP H) (sk : GXMSS.SecretKey PP H h v)
    (epoch : Fin (2 ^ h))
    (forgedMessage : M) (forgedRandomizer : R) (forgedWord : Codeword v (2 ^ w))
    (forgedOTS : Fin v → H) (forgedPath : Fin h → H) :
    ValidForgeryYieldsMerkleCollisionStatement hash enc K pk sk epoch forgedMessage
      forgedRandomizer forgedWord forgedOTS forgedPath := by
  unfold ValidForgeryYieldsMerkleCollisionStatement
  dsimp only
  intro _ _ _ _ hhonestRoot hforgedRoot hne
  have hroot : hash.recoverRoot pk.seed epoch (sk.endpoints epoch)
      (hash.authPath pk.seed sk.endpoints epoch) =
      hash.recoverRoot pk.seed epoch
        (fun i => hash.chain pk.seed epoch i (forgedWord i)
          (2 ^ w - 1 - (forgedWord i).val) (forgedOTS i)) forgedPath :=
    hhonestRoot.trans hforgedRoot.symm
  have hisSome := hash.findMerkleCollision_isSome pk.seed epoch
    (sk.endpoints epoch)
    (fun i => hash.chain pk.seed epoch i (forgedWord i)
      (2 ^ w - 1 - (forgedWord i).val) (forgedOTS i))
    (hash.authPath pk.seed sk.endpoints epoch) forgedPath hne hroot
  obtain ⟨collision, hcollision⟩ := Option.isSome_iff_exists.mp hisSome
  have hsound := hash.findMerkleCollision_sound _ _ _ _ _ _ hcollision
  have hmem := hash.findMerkleCollision_mem_queries _ _ _ _ _ _ hcollision
  have hshape := hash.findMerkleCollision_honest_shape pk.seed sk.endpoints epoch _ _ hcollision
  exact ⟨collision, hcollision, hsound, hmem.1, hmem.2, hshape⟩

/-- A different complete opening to the honest root gives the exact registered challenge index
and a winning second input for the stand-alone Merkle target-collision game. -/
theorem merkleCollision_registeredTarget_wins
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (hv : 0 < v)
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (ep : Fin (2 ^ h)) (forgedLeaf : Fin v → H) (forgedPath : Fin h → H)
    (hne : ((GXMSS.endpoints hash pp starts) ep,
      hash.authPath pp (GXMSS.endpoints hash pp starts) ep) ≠ (forgedLeaf, forgedPath))
    (hroot : hash.recoverRoot pp ep forgedLeaf forgedPath =
      hash.merkleRoot pp (GXMSS.endpoints hash pp starts)) :
    ∃ collision : GXMSS.Security.HashCollision T X,
      hash.findMerkleCollision pp ep ((GXMSS.endpoints hash pp starts) ep)
        forgedLeaf (hash.authPath pp (GXMSS.endpoints hash pp starts) ep) forgedPath =
          some collision ∧
      let history := GXMSS.Reductions.endpointTargets hash pp starts ++
        GXMSS.Reductions.merkleTargets hash pp (GXMSS.endpoints hash pp starts)
      let j := GXMSS.Reductions.registeredIndex history collision.tweak collision.first
      j < history.length ∧ history[j]? = some (collision.tweak, collision.first) ∧
        j < (GXMSS.Reductions.merkleTCRProblem hash).numTargets ∧
        decide (collision.second ≠ collision.first ∧
          (HashInstance.thf hash).eval pp collision.tweak collision.second =
            (HashInstance.thf hash).eval pp collision.tweak collision.first) = true := by
  have hisSome := hash.findMerkleCollision_isSome_of_honest pp
    (GXMSS.endpoints hash pp starts) ep forgedLeaf forgedPath hne hroot
  obtain ⟨collision, hcollision⟩ := Option.isSome_iff_exists.mp hisSome
  have hsound := hash.findMerkleCollision_sound pp ep _ _ _ _ hcollision
  have hmem := (hash.findMerkleCollision_mem_queries pp ep _ _ _ _ hcollision).1
  have hspec := GXMSS.Reductions.merkleOpeningTarget_registeredIndex_spec
    hash pp starts (GXMSS.endpoints hash pp starts) ep
    (collision.tweak, collision.first) hmem
    (GXMSS.Reductions.merkleTCRProblem hash).numTargets (by
      simpa only [List.length_append, GXMSS.Reductions.endpointTargets_length,
        GXMSS.Reductions.merkleTargets_length] using
          GXMSS.Reductions.merkleProblem_capacity hash hv)
  refine ⟨collision, hcollision, ?_⟩
  dsimp only
  obtain ⟨hindex, hlookup, hcapacity⟩ := hspec
  refine ⟨hindex, hlookup, hcapacity, ?_⟩
  obtain ⟨hinputs, himage⟩ := hsound
  exact decide_eq_true (And.intro (Ne.symm hinputs) himage.symm)

run_cmd Lean.Elab.Command.liftTermElabM do
  let name := ``ValidForgeryYieldsMerkleCollision
  let env ← Lean.getEnv
  let info? : Option Lean.ConstantInfo := env.find? name
  let some (.thmInfo info) := info?
    | throwError "{name} is not a theorem defined in this module"
  Lean.Meta.forallTelescope info.type fun fvars result => do
    let levelParams := info.levelParams
    let levels := levelParams.map Lean.Level.param
    let expected := Lean.mkAppN (Lean.mkConst ``ValidForgeryYieldsMerkleCollisionStatement levels)
      fvars
    unless (← Lean.Meta.isDefEq result expected) do
      throwError "{name} does not have the exact named Merkle-forgery proposition"
    let resultType ← Lean.Meta.inferType result
    unless (← Lean.Meta.isDefEq resultType (Lean.mkSort Lean.Level.zero)) do
      throwError "{name} is not a universally closed proposition"
  let axioms ← Lean.collectAxioms name
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := axioms.filter fun ax => !allowed.contains ax
  unless unexpected.isEmpty do
    throwError "unapproved transitive axioms for {name}: {unexpected.toList}"


end

end GXMSS.Unforgeability
