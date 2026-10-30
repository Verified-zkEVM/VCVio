/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# ML-KEM Parameters

This file collects the fixed constants and approved parameter sets from FIPS 203.
The development stays generic over the variable parameters while exposing the three
named NIST-approved instantiations.
-/

@[expose] public section


namespace MLKEM

/-- A byte, modeled as an unsigned 8-bit integer. -/
abbrev Byte := UInt8

/-- Fixed-length byte strings used throughout the ML-KEM specification. -/
abbrev Bytes (n : ℕ) := Vector Byte n

/-- The standard 32-byte seed length used by ML-KEM. -/
abbrev Seed32 := Bytes 32

/-- ML-KEM plaintext messages are 32-byte strings. -/
abbrev Message := Bytes 32

/-- ML-KEM shared secrets are 32-byte strings. -/
abbrev SharedSecret := Bytes 32

/-- The hash of an encapsulation key is modeled as a 32-byte string. -/
abbrev PublicKeyHash := Bytes 32

/-- Encryption randomness is modeled as a 32-byte string. -/
abbrev Coins := Bytes 32

/-- The variable parameters that distinguish the approved ML-KEM instantiations. -/
structure Params where
  /-- The module rank `k` of FIPS 203 Table 2: the public matrix `Â` is `k × k`, and the
  secret and error vectors and the ciphertext component `u` each have `k` polynomial
  entries. -/
  k : ℕ
  /-- The FIPS 203 parameter `η₁` of the centered binomial distribution `SamplePolyCBD_η₁`
  (Algorithm 8) that samples `s` and `e` in `K-PKE.KeyGen` (Algorithm 13) and `y` in
  `K-PKE.Encrypt` (Algorithm 14). -/
  eta1 : ℕ
  /-- The FIPS 203 parameter `η₂` of the centered binomial distribution `SamplePolyCBD_η₂`
  (Algorithm 8) that samples the encryption noise `e₁` and `e₂` in `K-PKE.Encrypt`
  (Algorithm 14). -/
  eta2 : ℕ
  /-- The FIPS 203 parameter `d_u`: the number of bits per coefficient kept when the ciphertext
  component `u` is compressed by `Compress_du` and serialized by `ByteEncode_du`. -/
  du : ℕ
  /-- The FIPS 203 parameter `d_v`: the number of bits per coefficient kept when the ciphertext
  component `v` is compressed by `Compress_dv` and serialized by `ByteEncode_dv`. -/
  dv : ℕ
deriving Repr, DecidableEq

/-- The fixed ring degree used by FIPS 203. -/
def ringDegree : ℕ := 256

/-- The fixed modulus used by FIPS 203. -/
def modulus : ℕ := 3329

/-- The distinguished root-of-unity constant named in FIPS 203. -/
def zeta : ZMod modulus := 17

namespace Params

/-- The semantic size of an encapsulation key for the chosen parameter set. -/
def publicKeyBytes (params : Params) : ℕ := 384 * params.k + 32

/-- The semantic size of a decapsulation key for the chosen parameter set. -/
def secretKeyBytes (params : Params) : ℕ := 768 * params.k + 96

/-- The semantic size of a ciphertext for the chosen parameter set. -/
def ciphertextBytes (params : Params) : ℕ := 32 * (params.du * params.k + params.dv)

/-- ML-KEM always outputs a 32-byte shared secret. -/
def sharedSecretBytes (_params : Params) : ℕ := 32

end Params

/-- The approved named parameter sets from FIPS 203. -/
inductive ParameterSet where
  | MLKEM512
  | MLKEM768
  | MLKEM1024
deriving Repr, DecidableEq

namespace ParameterSet

/-- Interpret a named parameter set as the corresponding parameter record. -/
def params : ParameterSet → Params
  | .MLKEM512 => { k := 2, eta1 := 3, eta2 := 2, du := 10, dv := 4 }
  | .MLKEM768 => { k := 3, eta1 := 2, eta2 := 2, du := 10, dv := 4 }
  | .MLKEM1024 => { k := 4, eta1 := 2, eta2 := 2, du := 11, dv := 5 }

/-- Required randomness strength from FIPS 203 Section 8. -/
def requiredRBGStrength : ParameterSet → ℕ
  | .MLKEM512 => 128
  | .MLKEM768 => 192
  | .MLKEM1024 => 256

/-- FIPS 203 recommends ML-KEM-768 as the default parameter set. -/
def recommended : ParameterSet := .MLKEM768

end ParameterSet

/-- The approved parameter record for ML-KEM-512. -/
def mlkem512 : Params := ParameterSet.params .MLKEM512

/-- The approved parameter record for ML-KEM-768. -/
def mlkem768 : Params := ParameterSet.params .MLKEM768

/-- The approved parameter record for ML-KEM-1024. -/
def mlkem1024 : Params := ParameterSet.params .MLKEM1024

/-- Recognize the approved FIPS 203 parameter sets. -/
def Params.isApproved (params : Params) : Prop :=
  params = mlkem512 ∨ params = mlkem768 ∨ params = mlkem1024

/-- The recommended default parameter record. -/
def recommendedParams : Params := mlkem768

end MLKEM
