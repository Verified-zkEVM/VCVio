/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
import VCVioTest.CryptoFoundations.SigningViewCounted
import VCVioTest.CryptoFoundations.SigningViewEncoding

/-! # Executable signing-view observation checks -/

/-- Run the signing-view observation checks. -/
public def main : IO Unit := do
  VCVioTest.CryptoFoundations.SigningViewCounted.run
  VCVioTest.CryptoFoundations.SigningViewEncoding.run
