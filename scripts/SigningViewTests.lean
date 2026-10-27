/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
import VCVioTest.CryptoFoundations.SigningViewCounted
import VCVioTest.CryptoFoundations.SigningViewEncoding
import VCVioTest.CryptoFoundations.SigningViewUniverse
import VCVioTest.CryptoFoundations.SigningViewUnforgeability

/-! # Executable signing-view observation checks -/

/-- Run the signing-view observation checks. -/
public def main : IO Unit := do
  VCVioTest.CryptoFoundations.SigningViewCounted.run
  VCVioTest.CryptoFoundations.SigningViewEncoding.run
  VCVioTest.CryptoFoundations.SigningViewUniverse.run
  let completed ← IO.mkRef ([] : List String)
  let complete : String → IO Unit := fun token => completed.modify (· ++ [token])
  VCVioTest.CryptoFoundations.SigningViewUnforgeability.run complete
  let expected := ["f4-unforgeability"]
  unless (← completed.get) == expected do
    throw (IO.userError "Signing-view completion mismatch")
