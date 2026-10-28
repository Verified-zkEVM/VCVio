/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
import VCVioTest.Algorithms.Hash

/-! # Executable entry point for shared algorithm regressions -/

public section

/-- Run pure algorithm tests without importing a scheme or native backend. -/
def main : IO Unit := VCVioTest.Algorithms.Hash.run
