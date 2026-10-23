/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SplitCharged
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalSignature

/-!
# A win leaves a fault, a collision, or the signer's own signature

`SplitCharged.cases_of_win_charged` ends its third branch at the forgery's FORS *secrets*, and
that is not enough to say anything about the forgery as a whole: two different signatures can
open the same secrets. Both dichotomies pin more than that — the hypertree chain's
fault-free branch gives the whole signature array and the FORS dichotomy gives the whole FORS
part — so the branch can end where it has to, at the forgery being the signature the signer
writes for that message.

That is what the replay case needs. A forgery that repeats a signed message with the signer's
randomiser produces the same digest, hence the same FORS instance and the same addresses; if
neither dichotomy fires, every part of it is the signer's and `CanonicalSignature.eq_signInternal`
identifies it with the signature a request returned, which strong freshness forbids.

Nothing here decides which branch a given win lands in; the two taken jointly are the content.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CanonicalSplit

open Security CacheReplay Extraction CanonicalGraph VerifierProbes SplitCharged

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

set_option maxHeartbeats 400000 in
-- Unifying the verifier's digest and FORS-key terms across both dichotomies is expensive.
/-- **A win in the warmed tail is a charged structural collision, a WOTS one-wayness residue, or
a forgery whose FORS part and hypertree are both the signer's own.** -/
theorem cases_of_win_canonical (adversary : Adversary)
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
              (forsKeyOf result.2 (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
                  message parsed =
                  honestForsKey walk.1.1.1 walk.1.1.2.2 result.2
                    (Scheme.forsAddress (digestOf result.2
                      (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
                      message parsed)) ∧
                parsed.fors = @SlhDsaSecurity.Fors.sign Id Id.instMonad
                  (CacheReplay.replayQuery result.2)
                  (MessageDigest.forsIndices (digestOf result.2
                    (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed))
                  walk.1.1.1 walk.1.1.2.2
                  (Scheme.forsAddress (digestOf result.2
                    (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
                    message parsed)) ∧
                parsed.hypertree = @SlhDsaSecurity.Hypertree.signLayers Id Id.instMonad
                  (CacheReplay.replayQuery result.2) walk.1.1.1 walk.1.1.2.2 layers 0
                  (MessageDigest.treeIndex (digestOf result.2
                    (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
                    message parsed)).toNat
                  (MessageDigest.leafIndex (digestOf result.2
                    (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
                    message parsed)).toFin
                  (honestForsKey walk.1.1.1 walk.1.1.2.2 result.2
                    (Scheme.forsAddress (digestOf result.2
                      (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
                      message parsed))))) := by
  -- The verification sub-run, at the key the walk's seeds generated.
  have hrun : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (WarmedGame.afterSeeds adversary walk.1.1))).run walk.2) := hresult
  obtain ⟨keys, keyCache, verifyCache, hkeys, hpersist, hverify⟩ :=
    WarmedSplit.split_afterSeeds adversary walk.1.1 walk.2 result hrun
  rw [WarmedSplit.keygenInternal_liftM, WarmedSplit.run_rom_liftM] at hkeys
  rw [WarmedSplit.verify_liftM, WarmedSplit.run_rom_liftM] at hverify
  have hkeyreplay : keys = @Scheme.keygenInternal Id Id.instMonad
      (CacheReplay.replayQuery result.2) walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 :=
    WarmedSplit.keygenInternal_eq_replay_of_subset _ _ _ walk.2 keyCache result.2 keys hkeys
      hpersist
  rw [hkeyreplay] at hverify
  have hverifyreplay : result.1.1.verified =
      @Scheme.verify Id Id.instMonad (CacheReplay.replayQuery result.2)
        (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery result.2)
          walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2).2
        result.1.1.forgery.message result.1.1.forgery.signature :=
    GameBridge.verify_eq_replay _ _ _ verifyCache result.2 _ hverify
  have haccept : @Scheme.verify Id Id.instMonad (CacheReplay.replayQuery result.2)
      (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery result.2)
        walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2).2
      result.1.1.forgery.message result.1.1.forgery.signature = true := by
    rw [← hverifyreplay, hverified]
  obtain ⟨message, parsed, hframe, hparsed, hinternal⟩ :=
    @GameBridge.verifyInternal_of_verify (CacheReplay.replayQuery result.2) _ _ _ haccept
  refine ⟨message, parsed, hframe, hparsed, ?_⟩
  rcases @HypertreeDispatch.cases_of_accepted_signed (CacheReplay.replayQuery result.2)
      walk.1.1.1 walk.1.1.2.2 _ _ _ _
      (honestForsKey walk.1.1.1 walk.1.1.2.2 result.2
        (Scheme.forsAddress (digestOf result.2
          (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed))) _
      (GameBridge.keygen_publicKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2).1
      (GameBridge.keygen_publicKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2).2
      (@GameBridge.hypertree_of_verifyInternal (CacheReplay.replayQuery result.2) _ _ _ hinternal)
    with ⟨hkey, hhypertree⟩ | hfault
  · -- The recovered FORS key is the genuine one, so the FORS branch applies.
    rcases VerifierProbes.deviatingCollision_or_canonical_of_verified walk.1.1.1 result.2
      verifyCache (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
      result.1.1.forgery.message result.1.1.forgery.signature message parsed
      result.1.1.verified (forsKeyOfDigest (digestOf result.2
        (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed))
      (forsKeyOfDigest_address _) hframe hparsed hverify result rfl hkey
      with hdeviating | hcanonical
    · exact Or.inl hdeviating
    · exact Or.inr (Or.inr ⟨hkey, hcanonical, hhypertree⟩)
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

end SlhDsaSecurity.CanonicalSplit
