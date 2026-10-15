/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import VCVio.Algorithms.Sha2
import VCVio.Algorithms.Keccak
import Lean.Data.Json

/-!
# Whole-hash differential comparison interface

This executable entry evaluates the actual core SHA2, SHA3 and SHAKE functions
on JSON byte arrays. The external driver compares these results with the pinned
Foundation definitions. These comparisons are executable evidence, separate
from the compression correspondence and the codec component theorems.
-/

namespace Interop.Cryptol.Bridge.HashCLI

open VCVio.Algorithms

/-- Evaluate one supported whole-byte algorithm without truncating malformed input bytes. -/
public def run (algorithm bytesText lengthText : String) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  let parsed : Except String (ByteArray × Nat) := do
    let bytes ← (Lean.Json.parse bytesText).bind (Lean.fromJson? (α := Array Nat))
    unless bytes.all (· < 256) do throw "Expected bytes below 256"
    let some length := lengthText.toNat? | throw "Expected a natural output length"
    pure (ByteArray.mk (bytes.map Nat.toUInt8), length)
  match parsed with
  | .error message => err.putStrLn message; return 1
  | .ok (bytes, length) =>
      let digest ← match algorithm with
        | "sha224" => pure (Sha2.sha224 bytes)
        | "sha256" => pure (Sha2.sha256 bytes)
        | "sha384" => pure (Sha2.sha384 bytes)
        | "sha512" => pure (Sha2.sha512 bytes)
        | "sha512_224" => pure (Sha2.sha512Trunc224 bytes)
        | "sha512_256" => pure (Sha2.sha512Trunc256 bytes)
        | "sha3_224" => pure (Keccak.sha3Digest224 bytes)
        | "sha3_256" => pure (Keccak.sha3Digest256 bytes)
        | "sha3_384" => pure (Keccak.sha3Digest384 bytes)
        | "sha3_512" => pure (Keccak.sha3Digest512 bytes)
        | "shake128" => pure (Keccak.shake128 bytes length)
        | "shake256" => pure (Keccak.shake256 bytes length)
        | "keccak256" => pure (Keccak.keccak256 bytes)
        | _ => err.putStrLn "Unknown hash algorithm"; return 1
      out.putStrLn (Lean.toJson (digest.data.map UInt8.toNat)).compress
      return 0

end Interop.Cryptol.Bridge.HashCLI
