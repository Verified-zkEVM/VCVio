/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
import HashSigTest.SLHDSA.Refactor.WotsIntegration

/-! # Executable entrypoint for WOTS construction observations -/

/-- Execute the WOTS construction and stateful observation controls. -/
public def main : IO Unit := SLHDSA.Refactor.WotsIntegration.runTests
