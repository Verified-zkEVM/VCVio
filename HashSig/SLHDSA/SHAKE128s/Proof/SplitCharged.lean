/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedSplit
public import HashSig.SLHDSA.SHAKE128s.Proof.VerifierProbes

/-!
# The split, with its structural half charged

`WarmedSplit.cases_of_win` ends the structural reduction: an accepted forgery in the warmed tail
either recovers a FORS public key equal to whichever key one names as honest, or its hypertree
carries a fault. Both branches then have a charge waiting for them, and both charges want the
same thing from the game — the inputs the verifier consulted, as cache entries, which
`VerifierProbes` supplies. This file does the joining, and what comes out is one statement about
the tail whose every index is bound to the forgery.

The join turns on a choice. `Extraction.HypertreeChain.cases_of_accepted` leaves the honest FORS
key a free parameter, so `cases_of_win` holds for *every* value of it; naming the value is the
caller's privilege. Naming it `honestForsKey` — the compression of the fourteen canonical FORS
roots under the genuine secrets, at the address this forgery's digest selects — makes the first
disjunct literally the hypothesis `ForsBranch.deviatingCollision_or_secrets` takes, and makes the
second disjunct's `expectedInput` the same key, which is what the WOTS residue is stated against.
Nothing is bent to fit: the honest key is pinned only on the hypertree side, by
`GameBridge.keygen_publicKey`, and that constraint is consumed by the fault, not by the FORS key.

What is left is three cases, on two sides of the budget. The deviating collision is the
structural event the random oracle pays for. The WOTS residue and the disclosed FORS secrets are
one-wayness and coverage statements about the genuine secrets, and belong to the input half.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.SplitCharged

open Security CacheReplay Extraction CanonicalGraph VerifierProbes

/-- The public key the walk's seeds generate, read from this run's own cache. -/
@[expose] def generatedKey (secretSeed prfSeed publicSeed : Digest) (cache : QueryCache HashSpec) :
    PublicKey :=
  (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery cache)
    secretSeed prfSeed publicSeed).2

/-- The FORS public key the genuine secrets produce at an address. -/
@[expose] def honestForsKey (secretSeed publicSeed : Digest) (cache : QueryCache HashSpec)
    (address : Address) : Digest :=
  @Hashing.tweakable Id Id.instMonad (CacheReplay.replayQuery cache) publicSeed
    (Extraction.Fors.rootAddress address)
    (digestArrayBytes (@Extraction.Fors.canonicalRoots (CacheReplay.replayQuery cache)
      secretSeed publicSeed address))

/-- The canonical-graph FORS key a digest selects. -/
@[expose] def forsKeyOfDigest (digest : HashOutput) : ForsKey :=
  ⟨(MessageDigest.treeIndex digest).toFin, (MessageDigest.leafIndex digest).toFin⟩

/-- The graph's FORS key sits at the address the verifier uses. -/
theorem forsKeyOfDigest_address (digest : HashOutput) :
    (forsKeyOfDigest digest).address = Scheme.forsAddress digest := rfl

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

attribute [local irreducible] Scheme.keygenInternal in
/-- The warmed tail's verification sub-run, at the key the walk's seeds generate, read from the
tail's own final cache. -/
private theorem mem_support_verify_of_tail (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk)) :
    ∃ verifyCache : QueryCache HashSpec,
      (result.1.1.verified, result.2) ∈ support ((simulateQ randomOracle
        (Scheme.verify (m := OracleComp HashSpec)
          (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
          result.1.1.forgery.message result.1.1.forgery.signature)).run verifyCache) := by
  have hrun : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (WarmedGame.afterSeeds adversary walk.1.1))).run walk.2) := by
    rw [WarmedGame.tail] at hresult
    exact hresult
  obtain ⟨keys, keyCache, verifyCache, hkeys, hpersist, hverify⟩ :=
    WarmedSplit.split_afterSeeds adversary walk.1.1 walk.2 result hrun
  rw [WarmedSplit.keygenInternal_liftM, WarmedSplit.run_rom_liftM] at hkeys
  rw [WarmedSplit.verify_liftM, WarmedSplit.run_rom_liftM] at hverify
  rw [WarmedSplit.keygenInternal_eq_replay_of_subset walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2
    keyCache result.2 keys hkeys hpersist] at hverify
  exact ⟨verifyCache, hverify⟩

/-- **A win in the warmed tail is a charged structural collision, a WOTS one-wayness residue,
or a disclosure of the honest FORS secrets.** -/
theorem cases_of_win_charged (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (hverified : result.1.1.verified = true) :
    ∃ (message : Bytes) (parsed : Signature),
      result.1.1.forgery.message.frame = some message ∧
        Signature.fromBytes? result.1.1.forgery.signature = some parsed ∧
          (StructuralTerm.DeviatingCollision walk.1.1.2.2
              (@value (CacheReplay.replayQuery result.2) walk.1.1.1 walk.1.1.2.2) result ∨
            @FaultCharge.WotsResidue (CacheReplay.replayQuery result.2) walk.1.1.1 walk.1.1.2.2
                layers parsed.hypertree 0
                (MessageDigest.treeIndex (digestOf result.2
                  (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
                  message parsed)).toNat
                (MessageDigest.leafIndex (digestOf result.2
                  (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
                  message parsed)).toFin
                (forsKeyOf result.2 (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
                  message parsed)
                (honestForsKey walk.1.1.1 walk.1.1.2.2 result.2
                  (Scheme.forsAddress (digestOf result.2
                    (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
                    message parsed))) ∨
              ∀ i : Fin forsTrees, (parsed.fors i).secret =
                @SlhDsaSecurity.Fors.secret Id Id.instMonad (CacheReplay.replayQuery result.2)
                  walk.1.1.1 walk.1.1.2.2
                  (Scheme.forsAddress (digestOf result.2
                    (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed))
                  (Extraction.Fors.leafIndex (MessageDigest.forsIndices (digestOf result.2
                    (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed))
                    i)) := by
  obtain ⟨message, parsed, hframe, hparsed, hcases⟩ :=
    WarmedSplit.cases_of_win adversary hresult hverified
  refine ⟨message, parsed, hframe, hparsed, ?_⟩
  -- The verification sub-run, at the key the walk's seeds generated.
  obtain ⟨verifyCache, hverify⟩ := mem_support_verify_of_tail adversary hresult
  -- The honest FORS public key at the address this forgery's digest selects.
  rcases hcases (honestForsKey walk.1.1.1 walk.1.1.2.2 result.2
    (Scheme.forsAddress (digestOf result.2
      (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed)))
    with hkey | hfault
  · -- The recovered FORS key is the genuine one, so the FORS branch applies.
    rcases VerifierProbes.deviatingCollision_or_secrets_of_verified walk.1.1.1 result.2
      verifyCache (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
      result.1.1.forgery.message result.1.1.forgery.signature message parsed
      result.1.1.verified (forsKeyOfDigest (digestOf result.2
        (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed))
      (forsKeyOfDigest_address _) hframe hparsed hverify result rfl hkey
      with hdeviating | hsecrets
    · exact Or.inl hdeviating
    · exact Or.inr (Or.inr hsecrets)
  · -- The hypertree carries a fault, which the fault charge consumes.
    rcases VerifierProbes.deviatingCollision_or_residue_of_verified walk.1.1.1 result.2
      verifyCache (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
      result.1.1.forgery.message result.1.1.forgery.signature message parsed
      result.1.1.verified (honestForsKey walk.1.1.1 walk.1.1.2.2 result.2
        (Scheme.forsAddress (digestOf result.2
          (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed)))
      hframe hparsed hverify result rfl hfault with hdeviating | hresidue
    · exact Or.inl hdeviating
    · exact Or.inr (Or.inl hresidue)

end SlhDsaSecurity.SplitCharged
