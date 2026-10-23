/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsDispatch
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.HypertreeChain
public import HashSig.SLHDSA.SHAKE128s.Proof.SignatureCanonical
public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.Signature
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Fors
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Merkle

/-!
# A forgery with nothing forged in it is the signer's own signature

The two dichotomies now end, in their fault-free branches, at equations between *signatures*
rather than between the values they recover: `ForsDispatch.forsCollision_or_canonical_signature`
gives the FORS part as `Fors.sign` writes it, and
`Extraction.HypertreeChain.verify_fault_or_fors_signed` gives the hypertree part as the signing
loop writes it. This file draws the consequence.

A `Signature` has exactly three fields, so once the randomiser matches too there is nothing left
to differ in, and the parse is `Scheme.signInternal`'s own output. Since parsing is injective on
accepted byte strings — `Signature.toBytes_fromBytes` — the forgery's *bytes* are then the bytes
a signing request on that message would have returned.

That is what closes the replay case. A forgery that repeats a signed message with the signer's
randomiser produces the same digest, hence the same FORS instance and the same addresses; if
neither dichotomy fires, every part of it is the signer's, so the whole signature is, and strong
freshness is contradicted by the log entry that returned it. Strong freshness excludes the
returned *pair*, which is exactly the pair this produces.

The randomiser is a hypothesis here rather than a conclusion. Nothing in the structural
extraction pins it: it is the adversary's choice, and the only reason it coincides with the
signer's in the replay case is that the two message inputs coincide, which is a fact about the
cache rather than about the signature.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CanonicalSignature

variable [HasQuery HashSpec Id]

/-- **A parse whose three parts are canonical is the signature the signer writes.** -/
theorem eq_signInternal (sk : SecretKey) (message : Bytes) (parsed : Signature)
    (hrandomizer : parsed.randomizer =
      Hashing.randomizer (m := Id) sk.prf sk.publicKey.seed message)
    (hfors : parsed.fors = SlhDsaSecurity.Fors.sign (m := Id)
      (MessageDigest.forsIndices
        (Hashing.messageDigest (m := Id) parsed.randomizer sk.publicKey message))
      sk.seed sk.publicKey.seed
      (Scheme.forsAddress
        (Hashing.messageDigest (m := Id) parsed.randomizer sk.publicKey message)))
    (hhypertree : parsed.hypertree = SlhDsaSecurity.Hypertree.signLayers (m := Id) sk.seed
      sk.publicKey.seed layers 0
      (MessageDigest.treeIndex
        (Hashing.messageDigest (m := Id) parsed.randomizer sk.publicKey message)).toNat
      (MessageDigest.leafIndex
        (Hashing.messageDigest (m := Id) parsed.randomizer sk.publicKey message)).toFin
      (SlhDsaSecurity.Fors.publicKeyFromSignature (m := Id) parsed.fors
        (MessageDigest.forsIndices
          (Hashing.messageDigest (m := Id) parsed.randomizer sk.publicKey message))
        sk.publicKey.seed
        (Scheme.forsAddress
          (Hashing.messageDigest (m := Id) parsed.randomizer sk.publicKey message)))) :
    parsed = Scheme.signInternal (m := Id) sk message := by
  obtain ⟨randomizer, fors, hypertree⟩ := parsed
  dsimp only at hrandomizer hfors hhypertree
  subst hrandomizer
  subst hfors
  subst hhypertree
  rfl

/-- **Such a forgery carries the bytes a signing request would have returned.** -/
theorem signature_eq_toBytes (sk : SecretKey) (message : Bytes) (signature : Bytes)
    (parsed : Signature) (hparsed : Signature.fromBytes? signature = some parsed)
    (hcanonical : parsed = Scheme.signInternal (m := Id) sk message) :
    signature = (Scheme.signInternal (m := Id) sk message).toBytes := by
  rw [← hcanonical, Signature.toBytes_fromBytes hparsed]

/-- **So it is not fresh**, given the log entry that returned those bytes. Strong freshness
excludes the returned pair, and this is that pair. -/
theorem not_fresh_of_canonical (sk : SecretKey) (signed : Security.SigningLog)
    (forgery : Security.Forgery) (message : Bytes) (parsed : Signature)
    (hparsed : Signature.fromBytes? forgery.signature = some parsed)
    (hcanonical : parsed = Scheme.signInternal (m := Id) sk message)
    (hlog : ∃ entry ∈ signed, entry.1 = forgery.message ∧
      entry.2 = some (Scheme.signInternal (m := Id) sk message).toBytes) :
    ¬ Security.Fresh signed forgery := by
  obtain ⟨entry, hentry, hmessage, hanswer⟩ := hlog
  intro hfresh
  exact hfresh ⟨entry, hentry, hmessage, by
    rw [hanswer, signature_eq_toBytes sk message forgery.signature parsed hparsed hcanonical]⟩

end SlhDsaSecurity.CanonicalSignature
