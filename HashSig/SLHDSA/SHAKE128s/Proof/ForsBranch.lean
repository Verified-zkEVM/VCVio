/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsDispatch

/-!
# The FORS branch of the split, composed

`HypertreeDispatch.cases_of_accepted` leaves the forgery in one of two states: the hypertree
carries a fault, or the FORS public key the signature recovers is the genuine one. This file
takes the second state apart.

`ForsDispatch.forsCollision_or_canonical_secrets` says a FORS signature reaching the genuine
key either collides — at the root compression, on one tree's authentication path, or at one
revealed leaf — or reveals exactly the honest secrets at the fourteen positions its digest
selects. `ForsDispatch.deviatingCollision_of_forsCollision` charges the first case as a
structural event. So the FORS branch reduces to a charged event or to the *coverage*
statement, which is what the FORS half of the budget is stated about.

Everything here is deterministic. The cache-entry hypotheses are what the charge needs and
what the verifier's own queries supply: the verifier computed each of these hashes, so each
input is in the final cache (`CacheReplay.cached_of_queriesUnder`).
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ForsBranch

open CanonicalGraph Extraction

/-- **The FORS branch: a charged collision, or the FORS part is the one the signer writes.**
The secrets alone do not identify the signature — the authentication paths may still differ —
and identifying the whole of it is what lets a forgery with nothing forged in it be compared
with the signature a request returned. -/
theorem deviatingCollision_or_canonical {α : Type} (secretSeed publicSeed : Digest)
    (cache : QueryCache HashSpec) (key : ForsKey)
    (indices : SlhDsaSecurity.Fors.Indices) (signature : ForsSignature)
    (hkey : @SlhDsaSecurity.Fors.publicKeyFromSignature Id Id.instMonad
        (CacheReplay.replayQuery cache) signature indices publicSeed key.address =
      @Hashing.tweakable Id Id.instMonad (CacheReplay.replayQuery cache) publicSeed
        (Extraction.Fors.rootAddress key.address)
        (digestArrayBytes (@Extraction.Fors.canonicalRoots (CacheReplay.replayQuery cache)
          secretSeed publicSeed key.address)))
    (result : α × QueryCache HashSpec) (hcache : result.2 = cache)
    (hcompressionEntry : cache (Hashing.tweakableInput publicSeed
      (StructuralNode.forsRoots key).address
      (digestArrayBytes (@Extraction.Fors.recoveredRoot (CacheReplay.replayQuery cache)
        signature indices publicSeed key.address))) ≠ none)
    (hpathEntry : ∀ (i : Fin forsTrees) (step : Fin forsHeight),
      cache (PathEntry.pathInput publicSeed (SlhDsaSecurity.Fors.nodeAddress key.address)
        (Extraction.Fors.leafIndex indices i) (Extraction.Fors.siblings signature i)
        (BinaryPath.value
          (PathEntry.pathCombine cache publicSeed
            (SlhDsaSecurity.Fors.nodeAddress key.address))
          (Extraction.Fors.leafIndex indices i)
          (@Extraction.Fors.recoveredLeaf (CacheReplay.replayQuery cache) signature indices
            publicSeed key.address i)
          (Extraction.Fors.siblings signature i) step.val) step) ≠ none)
    (hleafEntry : ∀ i : Fin forsTrees, cache (Hashing.tweakableInput publicSeed
      (SlhDsaSecurity.Fors.nodeAddress key.address 0 (Extraction.Fors.leafIndex indices i))
      (bytesBE n (signature i).secret)) ≠ none) :
    StructuralTerm.DeviatingCollision publicSeed
        (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result ∨
      signature = @SlhDsaSecurity.Fors.sign Id Id.instMonad (CacheReplay.replayQuery cache)
        indices secretSeed publicSeed key.address := by
  rcases @ForsDispatch.forsCollision_or_canonical_signature (CacheReplay.replayQuery cache)
    secretSeed publicSeed key.address indices signature hkey with hcollision | hcanonical
  · exact Or.inl (ForsDispatch.deviatingCollision_of_forsCollision secretSeed publicSeed cache
      key indices signature hcollision result hcache hcompressionEntry hpathEntry hleafEntry)
  · exact Or.inr hcanonical

/-- **The FORS branch: a charged collision, or the honest secrets were revealed.** -/
theorem deviatingCollision_or_secrets {α : Type} (secretSeed publicSeed : Digest)
    (cache : QueryCache HashSpec) (key : ForsKey)
    (indices : SlhDsaSecurity.Fors.Indices) (signature : ForsSignature)
    (hkey : @SlhDsaSecurity.Fors.publicKeyFromSignature Id Id.instMonad
        (CacheReplay.replayQuery cache) signature indices publicSeed key.address =
      @Hashing.tweakable Id Id.instMonad (CacheReplay.replayQuery cache) publicSeed
        (Extraction.Fors.rootAddress key.address)
        (digestArrayBytes (@Extraction.Fors.canonicalRoots (CacheReplay.replayQuery cache)
          secretSeed publicSeed key.address)))
    (result : α × QueryCache HashSpec) (hcache : result.2 = cache)
    (hcompressionEntry : cache (Hashing.tweakableInput publicSeed
      (StructuralNode.forsRoots key).address
      (digestArrayBytes (@Extraction.Fors.recoveredRoot (CacheReplay.replayQuery cache)
        signature indices publicSeed key.address))) ≠ none)
    (hpathEntry : ∀ (i : Fin forsTrees) (step : Fin forsHeight),
      cache (PathEntry.pathInput publicSeed (SlhDsaSecurity.Fors.nodeAddress key.address)
        (Extraction.Fors.leafIndex indices i) (Extraction.Fors.siblings signature i)
        (BinaryPath.value
          (PathEntry.pathCombine cache publicSeed
            (SlhDsaSecurity.Fors.nodeAddress key.address))
          (Extraction.Fors.leafIndex indices i)
          (@Extraction.Fors.recoveredLeaf (CacheReplay.replayQuery cache) signature indices
            publicSeed key.address i)
          (Extraction.Fors.siblings signature i) step.val) step) ≠ none)
    (hleafEntry : ∀ i : Fin forsTrees, cache (Hashing.tweakableInput publicSeed
      (SlhDsaSecurity.Fors.nodeAddress key.address 0 (Extraction.Fors.leafIndex indices i))
      (bytesBE n (signature i).secret)) ≠ none) :
    StructuralTerm.DeviatingCollision publicSeed
        (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result ∨
      ∀ i : Fin forsTrees, (signature i).secret =
        @SlhDsaSecurity.Fors.secret Id Id.instMonad (CacheReplay.replayQuery cache)
          secretSeed publicSeed key.address (Extraction.Fors.leafIndex indices i) := by
  rcases @ForsDispatch.forsCollision_or_canonical_secrets (CacheReplay.replayQuery cache)
    secretSeed publicSeed key.address indices signature hkey with hcollision | hsecrets
  · exact Or.inl (ForsDispatch.deviatingCollision_of_forsCollision secretSeed publicSeed cache
      key indices signature hcollision result hcache hcompressionEntry hpathEntry hleafEntry)
  · exact Or.inr hsecrets

end SlhDsaSecurity.ForsBranch
