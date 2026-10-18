/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
import VCVioTest.UniformThreshold
import VCVioTest.RejectionTiming

/-! # Executable entry point for threshold and rejection tape regressions -/

public section

/-- Run exact deterministic tape tests without a production random-number source. -/
def main : IO Unit := do
  UniformThresholdTest.run
  RejectionTimingTest.run
