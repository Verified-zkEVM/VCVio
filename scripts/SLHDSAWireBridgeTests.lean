/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
import HashSigTest.SLHDSA.SHAKE128s.WireBridge

/-! # Executable entry point for fixed-context wire translation checks -/

/-- Execute the fixed-context wire translation controls. -/
public def main : IO Unit := SLHDSA.SHAKE128s.WireBridgeTest.check
