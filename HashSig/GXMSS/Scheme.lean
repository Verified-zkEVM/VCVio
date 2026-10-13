/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Chain
public import HashSig.GXMSS.Merkle
public import HashSig.GXMSS.Encoding.Retry
public import VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.EvalDist.IndepProduct

/-!
# Generalized XMSS

Construction 3 of ePrint 2025/055, pages 18–19. Configuration is captured by the scheme;
keys and signatures are raw finite data. Epoch management is external to these algorithms.
-/

public section

namespace GXMSS

open Encoding

/-- Public root and the public seed used by all hashes and encodings. -/
structure PublicKey (PP H : Type) where
  /-- Root of the hashed-leaf Merkle tree. -/
  root : H
  /-- Public hash seed. -/
  seed : PP

/-- Full secret starts and stored public endpoints, with no embedded consistency proofs. -/
structure SecretKey (PP H : Type) (h v : ℕ) where
  /-- Public hash seed. -/
  seed : PP
  /-- Independently sampled chain starts. -/
  starts : Fin (2 ^ h) → Fin v → H
  /-- Stored chain endpoints. -/
  endpoints : Fin (2 ^ h) → Fin v → H

/-- A randomizer, OTS chain prefixes, and a leaf-first authentication path. -/
structure Signature (R H : Type) (h v : ℕ) where
  /-- Randomizer retained from the successful encoding attempt. -/
  randomizer : R
  /-- One prefix-chain value for each digit. -/
  ots : Fin v → H
  /-- One sibling per level, starting at the leaf. -/
  path : Fin h → H

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Full chain endpoints computed from the secret starts. -/
@[expose] def endpoints (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Fin (2 ^ h) → Fin v → H) : Fin (2 ^ h) → Fin v → H :=
  fun ep i => hash.chain pp ep i 0 (2 ^ w - 1) (starts ep i)

/-- Assemble raw keys from a public seed and full start array. -/
@[expose] def keys (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Fin (2 ^ h) → Fin v → H) : PublicKey PP H × SecretKey PP H h v :=
  (⟨hash.merkleRoot pp (endpoints hash pp starts), pp⟩,
    ⟨pp, starts, endpoints hash pp starts⟩)

/-- Independent canonical finite draws for every epoch and chain label. -/
@[expose] def sampleStarts (H : Type) [SampleableType H] (h v : ℕ) :
    ProbComp (Fin (2 ^ h) → Fin v → H) :=
  Fin.mOfFn (2 ^ h) fun _ => Fin.mOfFn v fun _ => $ᵗ H

/-- Parameterless key generation using the existing THF seed generator. -/
@[expose] def keygen [SampleableType H] (hash : HashInstance PP T X H h w v) :
    ProbComp (PublicKey PP H × SecretKey PP H h v) := do
  let pp ← (HashInstance.thf hash).seedGen
  let starts ← sampleStarts H h v
  pure (keys hash pp starts)

/-- Construct the signature data from a successful retry result. -/
@[expose] def signatureOfWord (hash : HashInstance PP T X H h w v)
    (sk : SecretKey PP H h v) (ep : Fin (2 ^ h))
    (wr : Codeword v (2 ^ w) × R) : Signature R H h v :=
  ⟨wr.2, fun i => hash.chain sk.seed ep i 0 (wr.1 i) (sk.starts ep i),
    hash.authPath sk.seed sk.endpoints ep⟩

/-- First-success encoding retry, followed by prefix chains and the canonical path. -/
@[expose] def sign [SampleableType R] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (sk : SecretKey PP H h v) (ep : Fin (2 ^ h)) (msg : M) :
    ProbComp (Option (Signature R H h v)) :=
  Option.map (signatureOfWord hash sk ep) <$> enc.retry ($ᵗ R) sk.seed msg ep K

/-- All-input verification re-encodes, completes chains, and checks the recovered root. -/
@[expose] def verify [DecidableEq H] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (pk : PublicKey PP H) (ep : Fin (2 ^ h)) (msg : M) (sig : Signature R H h v) : Bool :=
  match enc.value pk.seed msg sig.randomizer ep with
  | none => false
  | some word => decide (hash.recoverRoot pk.seed ep
      (fun i => hash.chain pk.seed ep i (word i) (2 ^ w - 1 - (word i).val) (sig.ots i))
      sig.path = pk.root)

/-- Generalized XMSS with its hash, arbitrary incomparable encoding and retry budget captured. -/
@[expose] def scheme [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) :
    SyncSignatureAlg ProbComp M (PublicKey PP H) (SecretKey PP H h v)
      (Signature R H h v) (Fin (2 ^ h)) where
  keygen := keygen hash
  sign := sign hash enc K
  verify := verify hash enc

end GXMSS
