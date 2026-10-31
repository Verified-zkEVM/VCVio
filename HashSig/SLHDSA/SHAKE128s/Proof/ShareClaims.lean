/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareWhole
public import HashSig.SLHDSA.SHAKE128s.Proof.VerifierProbes
public import HashSig.SLHDSA.SHAKE128s.Proof.VerifierNaturality
public import HashSig.SLHDSA.SHAKE128s.Proof.FaultCharge

/-!
# The forgery's claims read only what the verifier asked

`ClaimedProbes.claimedCandidatesOf` replays a cache three times: for the forgery's digest, for
the FORS public key it recovers, and for the messages its hypertree climbs through. Every input
any of the three replays consults is one the verifier itself asks when replayed at the same
cache (`VerifierProbes.queriesUnder_verify_fors`, `queriesUnder_verify_hypertree`, and the
digest at the head of the verifier). So two caches that agree on the verifier's own probes give
the same claimed candidates (`claimedCandidatesOf_congr`) — which is how the lenient game's
claims, read off the cache it can see, are the real game's claims.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.ShareClaims

open Security CacheReplay VerifierProbes

/-- A replayed Merkle recovery is the replay of the generic one. -/
theorem merkle_replay (cache : QueryCache HashSpec) (leaf : Fin (2 ^ subtreeHeight))
    (signature : XmssSignature) (message publicSeed : Digest) (address : Address) :
    @Merkle.publicKeyFromSignature Id _ (replayQuery cache) leaf signature message publicSeed
        address =
      (simulateQ (replay cache)
        (Merkle.publicKeyFromSignature (m := OracleComp HashSpec) leaf signature message publicSeed
          address) : Id Digest) :=
  (@VerifierNaturality.merkle_simulate Id _ _ (replay cache) (replayQuery cache)
    (FaultCharge.replay_agrees cache) leaf signature message publicSeed address).symm

/-- **The climb's messages read only what the climb's recovery asks.** -/
theorem forgedAt_congr (publicSeed : Digest) :
    ∀ (remaining : Nat) (signatures : Fin remaining → XmssSignature) (layer tree : Nat)
      (leaf : Hypertree.LeafIndex) (message : Digest) (i : Nat) (left right : QueryCache HashSpec),
      (∀ probe, QueriesUnder left
        (Hypertree.rootFromSignature (m := OracleComp HashSpec) publicSeed remaining signatures
          layer tree leaf message) probe → left probe = right probe) →
      @WotsResidueReduction.forgedAt (replayQuery left) publicSeed remaining signatures layer tree
          leaf message i =
        @WotsResidueReduction.forgedAt (replayQuery right) publicSeed remaining signatures layer
          tree leaf message i := by
  intro remaining
  induction remaining with
  | zero => intro _ _ _ _ _ _ _ _ _; rfl
  | succ remaining ih =>
    intro signatures layer tree leaf message i left right hagree
    cases i with
    | zero => rfl
    | succ i =>
      have hmerkle : @Merkle.publicKeyFromSignature Id _ (replayQuery left) leaf (signatures 0)
            message publicSeed (Hypertree.address layer tree) =
          @Merkle.publicKeyFromSignature Id _ (replayQuery right) leaf (signatures 0) message
            publicSeed (Hypertree.address layer tree) := by
        rw [merkle_replay, merkle_replay]
        refine simulateQ_replay_congr _ left right fun probe hprobe => hagree probe ?_
        simp only [Hypertree.rootFromSignature_succ]
        exact queriesUnder_bind left _ _ probe hprobe
      change @WotsResidueReduction.forgedAt (replayQuery left) publicSeed remaining
          (fun j => signatures j.succ) (layer + 1) (tree / 2 ^ subtreeHeight)
          (Hypertree.nextLeaf tree)
          (@Merkle.publicKeyFromSignature Id _ (replayQuery left) leaf (signatures 0) message
            publicSeed (Hypertree.address layer tree)) i =
        @WotsResidueReduction.forgedAt (replayQuery right) publicSeed remaining
          (fun j => signatures j.succ) (layer + 1) (tree / 2 ^ subtreeHeight)
          (Hypertree.nextLeaf tree)
          (@Merkle.publicKeyFromSignature Id _ (replayQuery right) leaf (signatures 0) message
            publicSeed (Hypertree.address layer tree)) i
      rw [← hmerkle]
      refine ih _ _ _ _ _ i left right fun probe hprobe => hagree probe ?_
      simp only [Hypertree.rootFromSignature_succ]
      refine queriesUnder_bind_right left _ _ probe ?_
      rw [← merkle_replay]
      exact hprobe

/-- **The forgery's digest is the verifier's first probe.** -/
theorem queriesUnder_verify_digest (cache : QueryCache HashSpec) (pk : PublicKey)
    (request : Message) (signature : Bytes) (message : Bytes) (parsed : Signature)
    (hframe : request.frame = some message)
    (hparsed : Signature.fromBytes? signature = some parsed) (probe : Bytes)
    (hquery : QueriesUnder cache
      (Hashing.messageDigest (m := OracleComp HashSpec) parsed.randomizer pk message) probe) :
    QueriesUnder cache (Scheme.verify (m := OracleComp HashSpec) pk request signature) probe := by
  simp only [Scheme.verify, Scheme.verifyInternal, hframe, hparsed]
  exact queriesUnder_bind cache _ _ probe hquery

/-- **Two caches that agree on the verifier's probes give the same claimed candidates.** -/
theorem claimedCandidatesOf_congr (publicSeed : Digest) (left right : QueryCache HashSpec)
    (pk : PublicKey) (request : Message) (signature : Bytes) (message : Bytes) (parsed : Signature)
    (hframe : request.frame = some message)
    (hparsed : Signature.fromBytes? signature = some parsed)
    (hseed : publicSeed = pk.seed)
    (hagree : ∀ probe, QueriesUnder left
      (Scheme.verify (m := OracleComp HashSpec) pk request signature) probe →
        left probe = right probe) :
    @ClaimedProbes.claimedCandidatesOf (replayQuery left) publicSeed left pk message parsed =
      @ClaimedProbes.claimedCandidatesOf (replayQuery right) publicSeed right pk message
        parsed := by
  subst hseed
  have hdig : digestOf left pk message parsed = digestOf right pk message parsed := by
    rw [← simulateQ_messageDigest, ← simulateQ_messageDigest]
    exact simulateQ_replay_congr _ left right fun probe hprobe =>
      hagree probe (queriesUnder_verify_digest left pk request signature message parsed hframe
        hparsed probe hprobe)
  have hforsSim : ∀ cache : QueryCache HashSpec, forsKeyOf cache pk message parsed =
      (simulateQ (replay cache) (Fors.publicKeyFromSignature (m := OracleComp HashSpec) parsed.fors
        (MessageDigest.forsIndices (digestOf cache pk message parsed)) pk.seed
        (Scheme.forsAddress (digestOf cache pk message parsed))) : Id Digest) := fun cache =>
    (@VerifierNaturality.fors_simulate Id Id.instMonad _ (replay cache) (replayQuery cache)
      (FaultCharge.replay_agrees cache) _ _ _ _).symm
  have hfors : forsKeyOf left pk message parsed = forsKeyOf right pk message parsed := by
    rw [hforsSim left, hforsSim right, ← hdig]
    exact simulateQ_replay_congr _ left right fun probe hprobe =>
      hagree probe (queriesUnder_verify_fors left pk request signature message parsed hframe
        hparsed probe hprobe)
  have hsteps : @ClaimedProbes.forgedSteps (replayQuery left) pk.seed parsed
        (MessageDigest.treeIndex (digestOf left pk message parsed)).toNat
        (MessageDigest.leafIndex (digestOf left pk message parsed)).toFin
        (forsKeyOf left pk message parsed) =
      @ClaimedProbes.forgedSteps (replayQuery right) pk.seed parsed
        (MessageDigest.treeIndex (digestOf left pk message parsed)).toNat
        (MessageDigest.leafIndex (digestOf left pk message parsed)).toFin
        (forsKeyOf left pk message parsed) := by
    funext layer chain
    unfold ClaimedProbes.forgedSteps ClaimedProbes.forgedStep
    rw [forgedAt_congr pk.seed _ _ _ _ _ _ _ left right fun probe hprobe => hagree probe
      (queriesUnder_verify_hypertree left pk request signature message parsed hframe hparsed probe
        hprobe)]
  unfold ClaimedProbes.claimedCandidatesOf
  rw [← hdig, ← hfors, hsteps]

end SLHDSA.SHAKE128s.ShareClaims
