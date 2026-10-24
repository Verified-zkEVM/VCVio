/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.FaultCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsBranch

/-!
# The verifier's own queries, as cache entries

Both halves of the split end at a composition whose remaining hypotheses are all of one kind:
*this byte input is in the final cache*. They are all true for the same reason — the verifier
computed that hash — and `CacheReplay.cached_of_queriesUnder` turns that reason into the
hypothesis, provided one can say *where in the verifier* the input is consulted. Saying that is
what this file does.

The descent is `Scheme.verify → verifyInternal → Fors.publicKeyFromSignature` on one side and
`Scheme.verify → verifyInternal → Hypertree.verify → rootFromSignature` on the other. Framing and
parsing make no oracle call, so a forgery that framed and parsed contributes nothing there; past
them the verifier is three binds, and `CacheReplay.queriesUnder_bind` descends into a prefix while
`queriesUnder_bind_right` steps over one. Stepping over a prefix fixes its value to the replayed
one, which is why `digestOf` and `forsKeyOf` appear: they are what the *replayed* verifier
computes, and they are what the extraction's statements are indexed by.

Reaching the FORS sites needs Algorithm 17 in the shape the generic path lemmas expect. Its
per-tree fold is the binary path fold, but its parity test reads the leaf index within the tree
while the extraction's reads the global index; the two agree because a tree's offset is even at
every height below the tree's own. `fors_pathInput` settles that once, and
`fors_eq_trees_bind_compression` then presents the recovery as fourteen leaf-then-path
computations followed by one compression — a `sequenceFin` whose components are reached by
stepping over the earlier ones.

What comes out is the four hypotheses the charges ask for: one for the hypertree fault, and the
compression, path and leaf entries the FORS branch takes.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.VerifierProbes

open CacheReplay Extraction CanonicalGraph

/-! ## What the replayed verifier computes -/

/-- The message digest the replayed verifier computes for this forgery. -/
@[expose] def digestOf (cache : QueryCache HashSpec) (pk : PublicKey) (message : Bytes)
    (parsed : Signature) : HashOutput :=
  @Hashing.messageDigest Id (CacheReplay.replayQuery cache) parsed.randomizer pk message

/-- The FORS public key the replayed verifier recovers from this forgery. -/
@[expose] def forsKeyOf (cache : QueryCache HashSpec) (pk : PublicKey) (message : Bytes)
    (parsed : Signature) : Digest :=
  @SlhDsaSecurity.Fors.publicKeyFromSignature Id Id.instMonad (CacheReplay.replayQuery cache)
    parsed.fors (MessageDigest.forsIndices (digestOf cache pk message parsed)) pk.seed
    (Scheme.forsAddress (digestOf cache pk message parsed))

/-- Replaying the message-digest computation against a cache yields `digestOf`. -/
theorem simulateQ_messageDigest (cache : QueryCache HashSpec) (pk : PublicKey) (message : Bytes)
    (parsed : Signature) :
    (simulateQ (CacheReplay.replay cache)
        (Hashing.messageDigest (m := OracleComp HashSpec) parsed.randomizer pk message) :
        Id HashOutput) = digestOf cache pk message parsed := rfl

/-! ## Descending into the verifier -/

/-- **The verifier's FORS recovery is reached.** -/
theorem queriesUnder_verify_fors (cache : QueryCache HashSpec) (pk : PublicKey)
    (request : Message) (signature : Bytes) (message : Bytes) (parsed : Signature)
    (hframe : request.frame = some message)
    (hparsed : Signature.fromBytes? signature = some parsed) (probe : Bytes)
    (hquery : QueriesUnder cache
      (SlhDsaSecurity.Fors.publicKeyFromSignature (m := OracleComp HashSpec) parsed.fors
        (MessageDigest.forsIndices (digestOf cache pk message parsed)) pk.seed
        (Scheme.forsAddress (digestOf cache pk message parsed))) probe) :
    QueriesUnder cache (Scheme.verify (m := OracleComp HashSpec) pk request signature) probe := by
  simp only [Scheme.verify, Scheme.verifyInternal, hframe, hparsed]
  refine queriesUnder_bind_right cache _ _ probe ?_
  rw [simulateQ_messageDigest]
  exact queriesUnder_bind cache _ _ probe hquery

/-- **The verifier's hypertree recovery is reached.** -/
theorem queriesUnder_verify_hypertree (cache : QueryCache HashSpec) (pk : PublicKey)
    (request : Message) (signature : Bytes) (message : Bytes) (parsed : Signature)
    (hframe : request.frame = some message)
    (hparsed : Signature.fromBytes? signature = some parsed) (probe : Bytes)
    (hquery : QueriesUnder cache
      (SlhDsaSecurity.Hypertree.rootFromSignature (m := OracleComp HashSpec) pk.seed layers
        parsed.hypertree 0 (MessageDigest.treeIndex (digestOf cache pk message parsed)).toNat
        (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin
        (forsKeyOf cache pk message parsed)) probe) :
    QueriesUnder cache (Scheme.verify (m := OracleComp HashSpec) pk request signature) probe := by
  simp only [Scheme.verify, Scheme.verifyInternal, hframe, hparsed]
  refine queriesUnder_bind_right cache _ _ probe ?_
  rw [simulateQ_messageDigest]
  refine queriesUnder_bind_right cache _ _ probe ?_
  rw [show (simulateQ (CacheReplay.replay cache)
      (SlhDsaSecurity.Fors.publicKeyFromSignature (m := OracleComp HashSpec) parsed.fors
        (MessageDigest.forsIndices (digestOf cache pk message parsed)) pk.seed
        (Scheme.forsAddress (digestOf cache pk message parsed))) : Id Digest) =
      forsKeyOf cache pk message parsed from
    @VerifierNaturality.fors_simulate Id Id.instMonad _ (CacheReplay.replay cache)
      (CacheReplay.replayQuery cache) (FaultCharge.replay_agrees cache) _ _ _ _]
  exact queriesUnder_bind cache _ _ probe hquery

/-- **(A) Every input the verifier's hypertree recovery consults is in the final cache.** -/
theorem cached_hypertree_probe (cache initialCache : QueryCache HashSpec) (pk : PublicKey)
    (request : Message) (signature : Bytes) (message : Bytes) (parsed : Signature)
    (verified : Bool)
    (hframe : request.frame = some message)
    (hparsed : Signature.fromBytes? signature = some parsed)
    (hmem : (verified, cache) ∈ support ((simulateQ randomOracle
      (Scheme.verify (m := OracleComp HashSpec) pk request signature)).run initialCache)) :
    ∀ probe, QueriesUnder cache
      (SlhDsaSecurity.Hypertree.rootFromSignature (m := OracleComp HashSpec) pk.seed layers
        parsed.hypertree 0 (MessageDigest.treeIndex (digestOf cache pk message parsed)).toNat
        (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin
        (forsKeyOf cache pk message parsed)) probe → cache probe ≠ none :=
  fun probe hquery => cached_of_queriesUnder _ initialCache cache verified probe
    (queriesUnder_verify_hypertree cache pk request signature message parsed hframe hparsed probe
      hquery) hmem

/-! ## The FORS recovery, in path-fold form

Algorithm 17 authenticates each of the fourteen revealed secrets and compresses the roots. Its
per-tree fold is the generic binary path fold, but its parity test reads the leaf index *within*
the tree while the extraction's reads the global index; the two agree because the offset of a
tree is even at every height below the tree's own (`Correctness.offset_even`). With that settled
the recovery is a `sequenceFin` of leaf-then-path computations followed by one compression, which
is the shape every descent below needs. -/

/-- The scheme's per-tree payload is the extraction's ordered pair of bytes. -/
theorem fors_pathInput (signature : ForsSignature)
    (indices : SlhDsaSecurity.Fors.Indices) (publicSeed : Digest) (address : Address)
    (i : Fin forsTrees) (value : Digest) (step : Fin forsHeight) :
    Hashing.tweakableInput publicSeed
        (SlhDsaSecurity.Fors.nodeAddress address (step.val + 1)
          (Extraction.Fors.leafIndex indices i / 2 ^ (step.val + 1)))
        (if (indices i).val / 2 ^ step.val % 2 = 0 then
            bytesBE n value ++ bytesBE n ((signature i).authentication step)
          else bytesBE n ((signature i).authentication step) ++ bytesBE n value) =
      PathEntry.pathInput publicSeed (SlhDsaSecurity.Fors.nodeAddress address)
        (Extraction.Fors.leafIndex indices i) (Extraction.Fors.siblings signature i) value
        step := by
  have hparity : Extraction.Fors.leafIndex indices i / 2 ^ step.val % 2 =
      (indices i).val / 2 ^ step.val % 2 := by
    have heven := Correctness.offset_even i.val forsHeight step.val step.isLt
    rw [Extraction.Fors.leafIndex,
      Correctness.offset_div_pow _ _ _ _ (Nat.le_of_lt step.isLt)]
    simp [Nat.add_mod, heven]
  simp only [PathEntry.pathInput, BinaryPath.pairBytes, BinaryPath.ordered, hparity,
    Extraction.Fors.siblings, dite_eq_left step.isLt, Fin.eta]
  split <;> rfl

/-- One FORS tree's root recovery: compress the revealed secret, then climb the authentication
path, with the path written in the form `PathEntry` names. -/
@[expose] def forsTreeRoot (signature : ForsSignature) (indices : SlhDsaSecurity.Fors.Indices)
    (publicSeed : Digest) (address : Address) (i : Fin forsTrees) : OracleComp HashSpec Digest :=
  (Hashing.shortHash (m := OracleComp HashSpec)
      (Hashing.tweakableInput publicSeed
        (SlhDsaSecurity.Fors.nodeAddress address 0 (Extraction.Fors.leafIndex indices i))
        (bytesBE n (signature i).secret))) >>= fun leaf =>
    (List.finRange forsHeight).foldlM (m := OracleComp HashSpec)
      (fun value step => Hashing.shortHash
        (PathEntry.pathInput publicSeed (SlhDsaSecurity.Fors.nodeAddress address)
          (Extraction.Fors.leafIndex indices i) (Extraction.Fors.siblings signature i) value step))
      leaf

/-- Algorithm 17 is the fourteen tree recoveries, then one compression. -/
theorem fors_eq_trees_bind_compression (signature : ForsSignature)
    (indices : SlhDsaSecurity.Fors.Indices) (publicSeed : Digest) (address : Address) :
    (SlhDsaSecurity.Fors.publicKeyFromSignature (m := OracleComp HashSpec) signature indices
        publicSeed address) =
      sequenceFin forsTrees (forsTreeRoot signature indices publicSeed address) >>= fun roots =>
        Hashing.shortHash (m := OracleComp HashSpec)
          (Hashing.tweakableInput publicSeed (Extraction.Fors.rootAddress address)
            (digestArrayBytes roots)) := by
  refine congrArg (fun trees : OracleComp HashSpec (Fin forsTrees → Digest) =>
    trees >>= fun roots => Hashing.shortHash (m := OracleComp HashSpec)
      (Hashing.tweakableInput publicSeed (Extraction.Fors.rootAddress address)
        (digestArrayBytes roots))) ?_
  refine congrArg (sequenceFin forsTrees) (funext fun i => ?_)
  refine congrArg (Bind.bind _) (funext fun leaf => ?_)
  refine congrArg (fun body => (List.finRange forsHeight).foldlM
    (m := OracleComp HashSpec) body leaf) (funext fun value => funext fun step => ?_)
  rw [← fors_pathInput signature indices publicSeed address i value step]
  rfl

/-- The replayed tree recovery is the extraction's recovered root. -/
theorem simulateQ_forsTreeRoot (cache : QueryCache HashSpec) (signature : ForsSignature)
    (indices : SlhDsaSecurity.Fors.Indices) (publicSeed : Digest) (address : Address)
    (i : Fin forsTrees) :
    (simulateQ (CacheReplay.replay cache)
        (forsTreeRoot signature indices publicSeed address i) : Id Digest) =
      @Extraction.Fors.recoveredRoot (CacheReplay.replayQuery cache) signature indices publicSeed
        address i := by
  rw [forsTreeRoot]
  simp only [simulateQ_bind, VerifierNaturality.foldlM_simulate (CacheReplay.replay cache),
    Correctness.foldlM_id]
  simp only [Extraction.Fors.recoveredRoot]
  refine congrArg (fun body => (List.finRange forsHeight).foldl body
    (@Extraction.Fors.recoveredLeaf (CacheReplay.replayQuery cache) signature indices publicSeed
      address i)) (funext fun value => funext fun step => ?_)
  rw [← fors_pathInput signature indices publicSeed address i value step]
  rfl

/-- The replayed recovery of all fourteen trees. -/
theorem simulateQ_forsTrees (cache : QueryCache HashSpec) (signature : ForsSignature)
    (indices : SlhDsaSecurity.Fors.Indices) (publicSeed : Digest) (address : Address) :
    (simulateQ (CacheReplay.replay cache)
        (sequenceFin forsTrees (forsTreeRoot signature indices publicSeed address)) :
          Id (Fin forsTrees → Digest)) =
      @Extraction.Fors.recoveredRoot (CacheReplay.replayQuery cache) signature indices publicSeed
        address := by
  rw [VerifierNaturality.sequenceFin_simulate (CacheReplay.replay cache),
    Correctness.sequenceFin_id]
  funext i
  exact simulateQ_forsTreeRoot cache signature indices publicSeed address i

/-! ## The three FORS sites -/

/-- Descend into the recovery of one FORS tree. -/
theorem queriesUnder_fors_tree (cache : QueryCache HashSpec) (signature : ForsSignature)
    (indices : SlhDsaSecurity.Fors.Indices) (publicSeed : Digest) (address : Address)
    (i : Fin forsTrees) (probe : Bytes)
    (hquery : QueriesUnder cache (forsTreeRoot signature indices publicSeed address i) probe) :
    QueriesUnder cache
      (SlhDsaSecurity.Fors.publicKeyFromSignature (m := OracleComp HashSpec) signature indices
        publicSeed address) probe := by
  rw [fors_eq_trees_bind_compression]
  exact queriesUnder_bind cache _ _ probe
    (FaultCharge.queriesUnder_sequenceFin cache forsTrees _ i probe hquery)

/-- **The root compression consults the recovered roots' bytes.** -/
theorem queriesUnder_fors_compression (cache : QueryCache HashSpec) (signature : ForsSignature)
    (indices : SlhDsaSecurity.Fors.Indices) (publicSeed : Digest) (address : Address) :
    QueriesUnder cache
      (SlhDsaSecurity.Fors.publicKeyFromSignature (m := OracleComp HashSpec) signature indices
        publicSeed address)
      (Hashing.tweakableInput publicSeed (Extraction.Fors.rootAddress address)
        (digestArrayBytes (@Extraction.Fors.recoveredRoot (CacheReplay.replayQuery cache)
          signature indices publicSeed address))) := by
  rw [fors_eq_trees_bind_compression, ← simulateQ_forsTrees]
  exact queriesUnder_compression cache _ publicSeed _ digestArrayBytes

/-- **Each tree's leaf compression consults the revealed secret's bytes.** -/
theorem queriesUnder_fors_leaf (cache : QueryCache HashSpec) (signature : ForsSignature)
    (indices : SlhDsaSecurity.Fors.Indices) (publicSeed : Digest) (address : Address)
    (i : Fin forsTrees) :
    QueriesUnder cache
      (SlhDsaSecurity.Fors.publicKeyFromSignature (m := OracleComp HashSpec) signature indices
        publicSeed address)
      (Hashing.tweakableInput publicSeed
        (SlhDsaSecurity.Fors.nodeAddress address 0 (Extraction.Fors.leafIndex indices i))
        (bytesBE n (signature i).secret)) :=
  queriesUnder_fors_tree cache signature indices publicSeed address i _
    (queriesUnder_shortHash cache _ _)

/-- **Each step of each tree's authentication path consults its input**, at the running value
the extraction's `BinaryPath.value` names. -/
theorem queriesUnder_fors_path (cache : QueryCache HashSpec) (signature : ForsSignature)
    (indices : SlhDsaSecurity.Fors.Indices) (publicSeed : Digest) (address : Address)
    (i : Fin forsTrees) (step : Fin forsHeight) :
    QueriesUnder cache
      (SlhDsaSecurity.Fors.publicKeyFromSignature (m := OracleComp HashSpec) signature indices
        publicSeed address)
      (PathEntry.pathInput publicSeed (SlhDsaSecurity.Fors.nodeAddress address)
        (Extraction.Fors.leafIndex indices i) (Extraction.Fors.siblings signature i)
        (BinaryPath.value
          (PathEntry.pathCombine cache publicSeed (SlhDsaSecurity.Fors.nodeAddress address))
          (Extraction.Fors.leafIndex indices i)
          (@Extraction.Fors.recoveredLeaf (CacheReplay.replayQuery cache) signature indices
            publicSeed address i)
          (Extraction.Fors.siblings signature i) step.val) step) := by
  refine queriesUnder_fors_tree cache signature indices publicSeed address i _ ?_
  rw [forsTreeRoot]
  refine queriesUnder_bind_right cache _ _ _ ?_
  rw [show (simulateQ (CacheReplay.replay cache) (Hashing.shortHash (m := OracleComp HashSpec)
      (Hashing.tweakableInput publicSeed
        (SlhDsaSecurity.Fors.nodeAddress address 0 (Extraction.Fors.leafIndex indices i))
        (bytesBE n (signature i).secret))) : Id Digest) =
      @Extraction.Fors.recoveredLeaf (CacheReplay.replayQuery cache) signature indices publicSeed
        address i from rfl]
  exact PathEntry.queriesUnder_pathInput cache publicSeed _ _ _ _ step

/-! ## The FORS entries, from the verification run

The three hypotheses `ForsBranch.deviatingCollision_or_secrets` takes, each discharged from the
same run: the verifier recovered the FORS key, so it made every one of these calls. The address
is the verifier's own `Scheme.forsAddress` of the digest it computed; a caller holding the
matching `CanonicalGraph.ForsKey` rewrites it to `key.address`, which is the same address. -/

/-- **(B.1) The root compression's input is in the final cache.** -/
theorem cached_fors_compression_probe (cache initialCache : QueryCache HashSpec)
    (pk : PublicKey) (request : Message) (signature : Bytes) (message : Bytes)
    (parsed : Signature) (verified : Bool)
    (hframe : request.frame = some message)
    (hparsed : Signature.fromBytes? signature = some parsed)
    (hmem : (verified, cache) ∈ support ((simulateQ randomOracle
      (Scheme.verify (m := OracleComp HashSpec) pk request signature)).run initialCache)) :
    cache (Hashing.tweakableInput pk.seed
      (Extraction.Fors.rootAddress (Scheme.forsAddress (digestOf cache pk message parsed)))
      (digestArrayBytes (@Extraction.Fors.recoveredRoot (CacheReplay.replayQuery cache)
        parsed.fors (MessageDigest.forsIndices (digestOf cache pk message parsed)) pk.seed
        (Scheme.forsAddress (digestOf cache pk message parsed))))) ≠ none :=
  cached_of_queriesUnder _ initialCache cache verified _
    (queriesUnder_verify_fors cache pk request signature message parsed hframe hparsed _
      (queriesUnder_fors_compression cache parsed.fors _ pk.seed _)) hmem

/-- **(B.2) Every authentication-path input is in the final cache.** -/
theorem cached_fors_path_probe (cache initialCache : QueryCache HashSpec)
    (pk : PublicKey) (request : Message) (signature : Bytes) (message : Bytes)
    (parsed : Signature) (verified : Bool)
    (hframe : request.frame = some message)
    (hparsed : Signature.fromBytes? signature = some parsed)
    (hmem : (verified, cache) ∈ support ((simulateQ randomOracle
      (Scheme.verify (m := OracleComp HashSpec) pk request signature)).run initialCache))
    (i : Fin forsTrees) (step : Fin forsHeight) :
    cache (PathEntry.pathInput pk.seed
      (SlhDsaSecurity.Fors.nodeAddress (Scheme.forsAddress (digestOf cache pk message parsed)))
      (Extraction.Fors.leafIndex (MessageDigest.forsIndices (digestOf cache pk message parsed)) i)
      (Extraction.Fors.siblings parsed.fors i)
      (BinaryPath.value
        (PathEntry.pathCombine cache pk.seed (SlhDsaSecurity.Fors.nodeAddress
          (Scheme.forsAddress (digestOf cache pk message parsed))))
        (Extraction.Fors.leafIndex (MessageDigest.forsIndices (digestOf cache pk message parsed)) i)
        (@Extraction.Fors.recoveredLeaf (CacheReplay.replayQuery cache) parsed.fors
          (MessageDigest.forsIndices (digestOf cache pk message parsed)) pk.seed
          (Scheme.forsAddress (digestOf cache pk message parsed)) i)
        (Extraction.Fors.siblings parsed.fors i) step.val) step) ≠ none :=
  cached_of_queriesUnder _ initialCache cache verified _
    (queriesUnder_verify_fors cache pk request signature message parsed hframe hparsed _
      (queriesUnder_fors_path cache parsed.fors _ pk.seed _ i step)) hmem

/-- **(B.3) Every revealed secret's compression input is in the final cache.** -/
theorem cached_fors_leaf_probe (cache initialCache : QueryCache HashSpec)
    (pk : PublicKey) (request : Message) (signature : Bytes) (message : Bytes)
    (parsed : Signature) (verified : Bool)
    (hframe : request.frame = some message)
    (hparsed : Signature.fromBytes? signature = some parsed)
    (hmem : (verified, cache) ∈ support ((simulateQ randomOracle
      (Scheme.verify (m := OracleComp HashSpec) pk request signature)).run initialCache))
    (i : Fin forsTrees) :
    cache (Hashing.tweakableInput pk.seed
      (SlhDsaSecurity.Fors.nodeAddress (Scheme.forsAddress (digestOf cache pk message parsed)) 0
        (Extraction.Fors.leafIndex
          (MessageDigest.forsIndices (digestOf cache pk message parsed)) i))
      (bytesBE n (parsed.fors i).secret)) ≠ none :=
  cached_of_queriesUnder _ initialCache cache verified _
    (queriesUnder_verify_fors cache pk request signature message parsed hframe hparsed _
      (queriesUnder_fors_leaf cache parsed.fors _ pk.seed _ i)) hmem

/-! ## The charges, supplied

Both halves of the split close against a single verification run: whatever the charge asks
to find in the cache, the verifier put there. -/

/-- **A hypertree fault of a verified forgery is charged or leaves the WOTS residue.** -/
theorem deviatingCollision_or_residue_of_verified {α : Type} (secretSeed : Digest)
    (cache initialCache : QueryCache HashSpec) (pk : PublicKey) (request : Message)
    (signature : Bytes) (message : Bytes) (parsed : Signature) (verified : Bool)
    (expectedInput : Digest)
    (hframe : request.frame = some message)
    (hparsed : Signature.fromBytes? signature = some parsed)
    (hmem : (verified, cache) ∈ support ((simulateQ randomOracle
      (Scheme.verify (m := OracleComp HashSpec) pk request signature)).run initialCache))
    (result : α × QueryCache HashSpec) (hcache : result.2 = cache)
    (hfault : @Extraction.HypertreeChain.HypertreeFault (CacheReplay.replayQuery cache)
      secretSeed pk.seed layers parsed.hypertree 0
      (MessageDigest.treeIndex (digestOf cache pk message parsed)).toNat
      (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin
      (forsKeyOf cache pk message parsed) expectedInput) :
    StructuralTerm.DeviatingCollision pk.seed
        (@value (CacheReplay.replayQuery cache) secretSeed pk.seed) result ∨
      @FaultCharge.WotsResidue (CacheReplay.replayQuery cache) secretSeed pk.seed layers
        parsed.hypertree 0 (MessageDigest.treeIndex (digestOf cache pk message parsed)).toNat
        (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin
        (forsKeyOf cache pk message parsed) expectedInput :=
  FaultCharge.deviatingCollision_or_residue_of_top_fault secretSeed pk.seed cache
    parsed.hypertree (MessageDigest.treeIndex (digestOf cache pk message parsed))
    (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin
    (forsKeyOf cache pk message parsed) expectedInput
    (cached_hypertree_probe cache initialCache pk request signature message parsed verified
      hframe hparsed hmem)
    result hcache hfault

/-- **The FORS branch of a verified forgery is charged or reveals the honest secrets.** -/
theorem deviatingCollision_or_secrets_of_verified {α : Type} (secretSeed : Digest)
    (cache initialCache : QueryCache HashSpec) (pk : PublicKey) (request : Message)
    (signature : Bytes) (message : Bytes) (parsed : Signature) (verified : Bool)
    (key : ForsKey)
    (hkeyAddress : key.address = Scheme.forsAddress (digestOf cache pk message parsed))
    (hframe : request.frame = some message)
    (hparsed : Signature.fromBytes? signature = some parsed)
    (hmem : (verified, cache) ∈ support ((simulateQ randomOracle
      (Scheme.verify (m := OracleComp HashSpec) pk request signature)).run initialCache))
    (result : α × QueryCache HashSpec) (hcache : result.2 = cache)
    (hkey : @SlhDsaSecurity.Fors.publicKeyFromSignature Id Id.instMonad
        (CacheReplay.replayQuery cache) parsed.fors
        (MessageDigest.forsIndices (digestOf cache pk message parsed)) pk.seed key.address =
      @Hashing.tweakable Id Id.instMonad (CacheReplay.replayQuery cache) pk.seed
        (Extraction.Fors.rootAddress key.address)
        (digestArrayBytes (@Extraction.Fors.canonicalRoots (CacheReplay.replayQuery cache)
          secretSeed pk.seed key.address))) :
    StructuralTerm.DeviatingCollision pk.seed
        (@value (CacheReplay.replayQuery cache) secretSeed pk.seed) result ∨
      ∀ i : Fin forsTrees, (parsed.fors i).secret =
        @SlhDsaSecurity.Fors.secret Id Id.instMonad (CacheReplay.replayQuery cache)
          secretSeed pk.seed key.address
          (Extraction.Fors.leafIndex
            (MessageDigest.forsIndices (digestOf cache pk message parsed)) i) :=
  ForsBranch.deviatingCollision_or_secrets secretSeed pk.seed cache key
    (MessageDigest.forsIndices (digestOf cache pk message parsed)) parsed.fors hkey result hcache
    (by
      have hroots : (StructuralNode.forsRoots key).address =
          Extraction.Fors.rootAddress key.address := rfl
      rw [hroots, hkeyAddress]
      exact cached_fors_compression_probe cache initialCache pk request signature message parsed
        verified hframe hparsed hmem)
    (fun i step => by
      rw [hkeyAddress]
      exact cached_fors_path_probe cache initialCache pk request signature message parsed
        verified hframe hparsed hmem i step)
    (fun i => by
      rw [hkeyAddress]
      exact cached_fors_leaf_probe cache initialCache pk request signature message parsed
        verified hframe hparsed hmem i)

/-- **The verifier's FORS branch, pinning the whole signature.** Either a charged collision, or
the forgery's FORS part is the one the signer writes at that key — paths as well as secrets. -/
theorem deviatingCollision_or_canonical_of_verified {α : Type} (secretSeed : Digest)
    (cache initialCache : QueryCache HashSpec) (pk : PublicKey) (request : Message)
    (signature : Bytes) (message : Bytes) (parsed : Signature) (verified : Bool)
    (key : ForsKey)
    (hkeyAddress : key.address = Scheme.forsAddress (digestOf cache pk message parsed))
    (hframe : request.frame = some message)
    (hparsed : Signature.fromBytes? signature = some parsed)
    (hmem : (verified, cache) ∈ support ((simulateQ randomOracle
      (Scheme.verify (m := OracleComp HashSpec) pk request signature)).run initialCache))
    (result : α × QueryCache HashSpec) (hcache : result.2 = cache)
    (hkey : @SlhDsaSecurity.Fors.publicKeyFromSignature Id Id.instMonad
        (CacheReplay.replayQuery cache) parsed.fors
        (MessageDigest.forsIndices (digestOf cache pk message parsed)) pk.seed key.address =
      @Hashing.tweakable Id Id.instMonad (CacheReplay.replayQuery cache) pk.seed
        (Extraction.Fors.rootAddress key.address)
        (digestArrayBytes (@Extraction.Fors.canonicalRoots (CacheReplay.replayQuery cache)
          secretSeed pk.seed key.address))) :
    StructuralTerm.DeviatingCollision pk.seed
        (@value (CacheReplay.replayQuery cache) secretSeed pk.seed) result ∨
      parsed.fors = @SlhDsaSecurity.Fors.sign Id Id.instMonad (CacheReplay.replayQuery cache)
        (MessageDigest.forsIndices (digestOf cache pk message parsed)) secretSeed pk.seed
        key.address :=
  ForsBranch.deviatingCollision_or_canonical secretSeed pk.seed cache key
    (MessageDigest.forsIndices (digestOf cache pk message parsed)) parsed.fors hkey result hcache
    (by
      have hroots : (StructuralNode.forsRoots key).address =
          Extraction.Fors.rootAddress key.address := rfl
      rw [hroots, hkeyAddress]
      exact cached_fors_compression_probe cache initialCache pk request signature message parsed
        verified hframe hparsed hmem)
    (fun i step => by
      rw [hkeyAddress]
      exact cached_fors_path_probe cache initialCache pk request signature message parsed
        verified hframe hparsed hmem i step)
    (fun i => by
      rw [hkeyAddress]
      exact cached_fors_leaf_probe cache initialCache pk request signature message parsed
        verified hframe hparsed hmem i)

end SlhDsaSecurity.VerifierProbes
