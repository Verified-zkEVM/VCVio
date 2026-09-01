/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Execution
public import HashSig.SLHDSA.Concrete.FIPS

/-!
# SLH-DSA pure-execution tests

Falsifiable order and shape canaries for the streaming Merkle evaluator, plus one end-to-end
approved-profile execution of deterministic key generation, signing, and verification.
-/

public section

namespace SLHDSA.ExecutionTest

open SLHDSA.Concrete

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"{label}: failed"

def fixedBytes (n : ℕ) (byte : Byte) : Bytes n := Vector.replicate n byte

def approvedWireCodec (set : FipsParameterSet) :
    CoreWireCodec set.params (approvedPrimitives set).core := by
  cases set <;>
    exact
      { pkSeed := WireCodec.bytes _
        skSeed := WireCodec.bytes _
        skPrf := WireCodec.bytes _
        y := WireCodec.bytes _ }

/-! ## Structural canaries -/

/-- This value distinguishes leaf order and left/right order at both internal levels. -/
example : Execution.treeHash (fun i => i + 1)
    (fun height index left right => 1000 * height + 100 * index + 10 * left + right)
    2 0 = 13254 := by
  norm_num [Execution.treeHash_succ]

/-- A selected leaf is not included in its own authentication path. -/
example : (Execution.authenticationPath (fun i => i)
    (fun _ _ left right => 10 * left + right) 2 2).toList = [3, 1] := by
  norm_num [Execution.authenticationPath_succ, Execution.treeHash_succ,
    PerfectMerkleTree.sibling]

/-- The executable and canonical tree semantics agree at a nonzero subtree index. -/
example : Execution.treeHash (fun i => i + 7)
    (fun height index left right => height + index + left + 2 * right) 3 5 =
    PerfectMerkleTree.merkleRoot (fun i => i + 7)
      (fun height index left right => height + index + left + 2 * right) 3 5 := by
  exact Execution.treeHash_eq_merkleRoot _ _ _ _

/-! ## End-to-end approved-profile smoke benchmark -/

def exerciseBundle (name : String) (vp : ValidatedParams)
    (prims : Primitives vp.params) [DecidableEq prims.Y]
    (atomic : CoreWireCodec vp.params prims.core)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed)
    (addrnd : prims.Y) : IO Unit := do
  let message : List Byte := [0x00, 0x00, 0x47, 0x39]
  let keygenStart := ← IO.monoMsNow
  let keys := Execution.keygenInternal vp prims skSeed skPrf pkSeed
  let externalKeys := Execution.keygenWithSeeds vp prims skSeed skPrf pkSeed
  let rootByte := (prims.core.yToBytes keys.1.pkRoot).toList.headD 0
  let keygenMs := (← IO.monoMsNow) - keygenStart
  ensure s!"{name}: Algorithm 21 returns SK first"
    (prims.core.yToBytes externalKeys.1.pkRoot == prims.core.yToBytes keys.2.pkRoot)
  ensure s!"{name}: Algorithm 21 returns PK second"
    (prims.core.yToBytes externalKeys.2.pkRoot == prims.core.yToBytes keys.1.pkRoot)
  let publicKeyWire := encodePublicKey atomic keys.1
  let secretKeyWire := encodeSecretKey atomic keys.2
  ensure s!"{name}: public-key wire width" (publicKeyWire.length == vp.params.publicKeyBytes)
  ensure s!"{name}: secret-key wire width" (secretKeyWire.length == vp.params.secretKeyBytes)
  match decodePublicKey atomic publicKeyWire with
  | .error _ => throw <| IO.userError s!"{name}: public-key codec rejected execution output"
  | .ok decoded =>
      ensure s!"{name}: public-key codec round trip"
        (encodePublicKey atomic decoded == publicKeyWire)
  match decodeSecretKey atomic secretKeyWire with
  | .error _ => throw <| IO.userError s!"{name}: secret-key codec rejected execution output"
  | .ok decoded =>
      ensure s!"{name}: secret-key codec round trip"
        (encodeSecretKey atomic decoded == secretKeyWire)
  let signStart := ← IO.monoMsNow
  let signature := Execution.signInternal vp prims message keys.2 addrnd
  let signatureByte := (prims.core.yToBytes signature.randomness).toList.headD 0
  let signatureWire := encodeSignature vp atomic signature
  ensure s!"{name}: signature wire width"
    (signatureWire.length == vp.params.signatureBytes)
  match decodeSignature vp atomic signatureWire with
  | .error _ => throw <| IO.userError s!"{name}: signature codec rejected execution output"
  | .ok decoded =>
      ensure s!"{name}: signature codec round trip"
        (encodeSignature vp atomic decoded == signatureWire)
  let signMs := (← IO.monoMsNow) - signStart
  let verifyStart := ← IO.monoMsNow
  let verified := Execution.verifyInternal vp prims message signature keys.1
  ensure s!"{name}: deterministic signature verifies" verified
  let verifyMs := (← IO.monoMsNow) - verifyStart
  ensure s!"{name}: hypertree width" (signature.hypertree.toArray.size == vp.params.d)
  ensure s!"{name}: FORS width" (signature.fors.toArray.size == vp.params.k)
  IO.println s!"SLH-DSA execution {name}: keygen={keygenMs}ms sign={signMs}ms \
    verify={verifyMs}ms root0={rootByte} R0={signatureByte}"

def exerciseProfile : FipsParameterSet → IO Unit
  | .SLHDSA_SHA2_128s =>
      @exerciseBundle FipsParameterSet.SLHDSA_SHA2_128s.name
        FipsParameterSet.SLHDSA_SHA2_128s.validatedParams
        (approvedPrimitives .SLHDSA_SHA2_128s)
        (inferInstanceAs (DecidableEq (Bytes 16)))
        (approvedWireCodec .SLHDSA_SHA2_128s)
        (fixedBytes 16 0x51) (fixedBytes 16 0x62)
        (fixedBytes 16 0x73) (fixedBytes 16 0x84)
  | .SLHDSA_SHAKE_128f =>
      @exerciseBundle FipsParameterSet.SLHDSA_SHAKE_128f.name
        FipsParameterSet.SLHDSA_SHAKE_128f.validatedParams
        (approvedPrimitives .SLHDSA_SHAKE_128f)
        (inferInstanceAs (DecidableEq (Bytes 16)))
        (approvedWireCodec .SLHDSA_SHAKE_128f)
        (fixedBytes 16 0x91) (fixedBytes 16 0xa2)
        (fixedBytes 16 0xb3) (fixedBytes 16 0xc4)
  | .SLHDSA_SHA2_192s =>
      @exerciseBundle FipsParameterSet.SLHDSA_SHA2_192s.name
        FipsParameterSet.SLHDSA_SHA2_192s.validatedParams
        (approvedPrimitives .SLHDSA_SHA2_192s)
        (inferInstanceAs (DecidableEq (Bytes 24)))
        (approvedWireCodec .SLHDSA_SHA2_192s)
        (fixedBytes 24 0x15) (fixedBytes 24 0x26)
        (fixedBytes 24 0x37) (fixedBytes 24 0x48)
  | .SLHDSA_SHA2_192f =>
      @exerciseBundle FipsParameterSet.SLHDSA_SHA2_192f.name
        FipsParameterSet.SLHDSA_SHA2_192f.validatedParams
        (approvedPrimitives .SLHDSA_SHA2_192f)
        (inferInstanceAs (DecidableEq (Bytes 24)))
        (approvedWireCodec .SLHDSA_SHA2_192f)
        (fixedBytes 24 0x59) (fixedBytes 24 0x6a)
        (fixedBytes 24 0x7b) (fixedBytes 24 0x8c)
  | .SLHDSA_SHA2_256s =>
      @exerciseBundle FipsParameterSet.SLHDSA_SHA2_256s.name
        FipsParameterSet.SLHDSA_SHA2_256s.validatedParams
        (approvedPrimitives .SLHDSA_SHA2_256s)
        (inferInstanceAs (DecidableEq (Bytes 32)))
        (approvedWireCodec .SLHDSA_SHA2_256s)
        (fixedBytes 32 0x19) (fixedBytes 32 0x2a)
        (fixedBytes 32 0x3b) (fixedBytes 32 0x4c)
  | .SLHDSA_SHA2_256f =>
      @exerciseBundle FipsParameterSet.SLHDSA_SHA2_256f.name
        FipsParameterSet.SLHDSA_SHA2_256f.validatedParams
        (approvedPrimitives .SLHDSA_SHA2_256f)
        (inferInstanceAs (DecidableEq (Bytes 32)))
        (approvedWireCodec .SLHDSA_SHA2_256f)
        (fixedBytes 32 0x5d) (fixedBytes 32 0x6e)
        (fixedBytes 32 0x7f) (fixedBytes 32 0x80)
  | _ => pure ()

def main : IO Unit := do
  exerciseProfile .SLHDSA_SHA2_128s
  exerciseProfile .SLHDSA_SHAKE_128f
  exerciseProfile .SLHDSA_SHA2_192s
  exerciseProfile .SLHDSA_SHA2_192f
  exerciseProfile .SLHDSA_SHA2_256s
  exerciseProfile .SLHDSA_SHA2_256f
  IO.println "SLH-DSA pure execution tests: PASS"

end SLHDSA.ExecutionTest

def main : IO Unit := SLHDSA.ExecutionTest.main
