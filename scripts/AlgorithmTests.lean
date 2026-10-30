/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
import VCVioTest.Algorithms.Hash
import VCVioTest.PointerChainPuzzle.LeanSeal
import VCVioTest.PointerChainPuzzle.LeanSealEnvelope

/-! # Executable entry point for shared algorithm regressions -/

public section

/-- Run the pure algorithm tests and the leanSeal puzzle and envelope known answers, without a
native backend. -/
def main : IO Unit := do
  VCVioTest.Algorithms.Hash.run
  VCVioTest.LeanSeal.run
  VCVioTest.LeanSealEnvelope.run
