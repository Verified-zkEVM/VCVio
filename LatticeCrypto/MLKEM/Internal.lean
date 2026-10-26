/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.MLKEM.KPKE

/-!
# ML-KEM Internal Algorithms

This file models the deterministic internal algorithms from FIPS 203 Section 6.
-/

@[expose] public section


namespace MLKEM

/-- In the internal spec, the KEM encapsulation key is just the K-PKE public key. -/
abbrev EncapsulationKey (params : Params) (encoding : Encoding params) :=
  KPKE.PublicKey params encoding

/-- In the internal spec, the KEM ciphertext is just the K-PKE ciphertext. -/
abbrev Ciphertext (params : Params) (encoding : Encoding params) :=
  KPKE.Ciphertext params encoding

/-- The ML-KEM decapsulation key packages the PKE secret key, the encapsulation key, its hash,
and the fallback seed used by implicit rejection. -/
structure DecapsulationKey (params : Params) (encoding : Encoding params) where
  /-- The K-PKE decryption key `dk_PKE`, which `ML-KEM.Decaps_internal` (FIPS 203 Algorithm 18)
  uses to decrypt the ciphertext. -/
  dkPKE : KPKE.SecretKey params encoding
  /-- The encapsulation key `ek`, which `ML-KEM.Decaps_internal` (FIPS 203 Algorithm 18) uses to
  re-encrypt the decrypted message and compare the result with the received ciphertext. -/
  ekPKE : EncapsulationKey params encoding
  /-- The hash `H(ek)` of the encapsulation key, hashed with the decrypted message by `G` in
  `ML-KEM.Decaps_internal` (FIPS 203 Algorithm 18). -/
  ekHash : PublicKeyHash
  /-- The 32-byte implicit-rejection seed `z`: `ML-KEM.Decaps_internal` (FIPS 203 Algorithm 18)
  returns `J(z ‖ c)` when re-encryption does not reproduce the ciphertext `c`. -/
  z : Seed32

variable {params : Params}

/-- Hash an encapsulation key using the abstract `H` primitive. -/
def encapsulationKeyHash (encoding : Encoding params) (prims : Primitives params encoding)
    (ek : EncapsulationKey params encoding) : PublicKeyHash :=
  prims.hEncapsulationKey ek.tHatEncoded ek.rho

/-- `ML-KEM.KeyGen_internal`. -/
def keygenInternal (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) (d z : Seed32) :
    EncapsulationKey params encoding × DecapsulationKey params encoding :=
  let (ekPKE, dkPKE) := KPKE.keygenFromSeed ring encoding prims d
  let ekHash := encapsulationKeyHash encoding prims ekPKE
  let dk : DecapsulationKey params encoding := {
    dkPKE := dkPKE
    ekPKE := ekPKE
    ekHash := ekHash
    z := z
  }
  (ekPKE, dk)

/-- `ML-KEM.Encaps_internal`. -/
def encapsInternal (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) (ek : EncapsulationKey params encoding)
    (m : Message) : SharedSecret × Ciphertext params encoding :=
  let ekHash := encapsulationKeyHash encoding prims ek
  let (k, r) := prims.gEncaps m ekHash
  let c := KPKE.encrypt ring encoding prims ek m r
  (k, c)

/-- `ML-KEM.Decaps_internal`. -/
def decapsInternal (ring : NTTRingOps) (encoding : Encoding params)
    [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV]
    (prims : Primitives params encoding)
    (dk : DecapsulationKey params encoding) (c : Ciphertext params encoding) : SharedSecret :=
  let m' := KPKE.decrypt ring encoding prims dk.dkPKE c
  let (k', r') := prims.gEncaps m' dk.ekHash
  let kBar := prims.jReject dk.z c.uEncoded c.vEncoded
  let c' := KPKE.encrypt ring encoding prims dk.ekPKE m' r'
  if c = c' then k' else kBar

end MLKEM
