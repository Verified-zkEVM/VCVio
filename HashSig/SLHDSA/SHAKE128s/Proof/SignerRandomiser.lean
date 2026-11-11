/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.HonestProbes
public import HashSig.SLHDSA.SHAKE128s.Proof.RandomizerGate

/-!
# The signer, cut at its randomiser

The randomiser deferral's remaining hop replaces the signer's randomiser by a value drawn
outside the oracle, so the first thing it needs is the signer split at that query: everything
after it reads the randomiser as a *value*, and `Scheme.signInternal` already has that shape —
`Hashing.randomizer` is its first line and nothing later queries at `SK.prf`.

`signInternalAt` is the part after the cut and `signInternal_eq` is the cut itself, an equality
of computations that holds by the do-block's own associativity.

What makes the cut worth taking is `probes_signInternalAt`: with the randomiser a parameter,
*none* of the remaining queries is a `PRF_msg` input at `SK.prf` — unless the randomiser handed
in is `SK.prf` itself. The remaining queries are the message digest's input, which opens with
the randomiser, and canonical inputs, which open with `PK.seed`; the first is in the class
exactly on the overlap `RandomizerGate.messageInput_eq_randomizerInput` describes, and the
second never, the two seeds differing on a good walk.

That is the statement the hop's step-law equality rests on. The signer's randomiser query is the
*only* thing it has to move, because everything else the signer does is blind to the class the
charge protects.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.SignerRandomiser

open Security CacheReplay HonestProbes

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `Scheme.signInternal` once its randomiser is in hand. -/
@[expose]
def signInternalAt (randomizer : Digest) (sk : SecretKey) (message : Bytes) : m Signature := do
  let digest ← Hashing.messageDigest randomizer sk.publicKey message
  let indices := MessageDigest.forsIndices digest
  let address := Scheme.forsAddress digest
  let fors ← Fors.sign indices sk.seed sk.publicKey.seed address
  let forsKey ← Fors.publicKeyFromSignature fors indices sk.publicKey.seed address
  let hypertree ← Hypertree.sign forsKey sk.seed sk.publicKey.seed
    (MessageDigest.treeIndex digest) (MessageDigest.leafIndex digest).toFin
  return { randomizer, fors, hypertree }

/-- **The signer is its randomiser query and then the rest.** -/
theorem signInternal_eq (sk : SecretKey) (message : Bytes) :
    Scheme.signInternal (m := m) sk message =
      Hashing.randomizer sk.prf sk.publicKey.seed message >>= fun randomizer =>
        signInternalAt randomizer sk message := rfl

/-- **The rest of the signer consults canonical inputs and its own digest's.** The randomiser is
a parameter here, so this says nothing about `SK.prf` — which is the point. -/
theorem probes_signInternalAt (cache : QueryCache HashSpec) (randomizer : Digest)
    (sk : SecretKey) (message : Bytes) :
    Probes cache (signInternalAt (m := OracleComp HashSpec) randomizer sk message)
      (fun probe =>
        Canonical sk.publicKey.seed (replayCells cache sk.seed sk.publicKey.seed) probe ∨
          probe = Hashing.messageInput randomizer sk.publicKey message) := by
  refine probes_hash cache (Hashing.messageInput randomizer sk.publicKey message) _ _
    (Or.inr rfl) ?_
  generalize (replay cache (Hashing.messageInput randomizer sk.publicKey message)) = digest
  refine probes_bind cache _ _ _
    (@Fors.sign Id _ (replayQuery cache) (MessageDigest.forsIndices digest) sk.seed
      sk.publicKey.seed (forsKeyOf digest).address)
    (fors_sign_replay cache (MessageDigest.forsIndices digest) sk.seed sk.publicKey.seed
      (forsKeyOf digest).address)
    (Probes.mono (probes_fors_sign cache sk.seed sk.publicKey.seed (forsKeyOf digest)
      (MessageDigest.forsIndices digest)) fun _ hprobe => Or.inl hprobe) ?_
  refine probes_bind_replay cache _ _ _
    (Probes.mono (probes_fors_publicKeyFromSignature cache sk.seed sk.publicKey.seed
      (forsKeyOf digest) (MessageDigest.forsIndices digest) _
      (fun _ => by rw [fors_sign_entry]) (fun _ _ => by rw [fors_sign_entry]))
      fun _ hprobe => Or.inl hprobe) ?_
  refine probes_bind_replay cache _ _ _
    (Probes.mono (probes_hypertree_signLayers cache sk.seed sk.publicKey.seed layers 0
      (MessageDigest.treeIndex digest).toNat (MessageDigest.leafIndex digest).toFin _
      (by omega) (MessageDigest.treeIndex digest).isLt)
      fun _ hprobe => Or.inl hprobe) ?_
  exact probes_pure cache _ _

end SLHDSA.SHAKE128s.SignerRandomiser
