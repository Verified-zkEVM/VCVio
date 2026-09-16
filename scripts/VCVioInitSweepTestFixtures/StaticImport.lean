/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Pi

/-! # Observable initializer for the static-import contract

The test supplies a temporary marker path. A normal Lean import executes this initializer;
the sweep must inspect its declaration without creating the marker.
-/

public section
namespace VCVioInitSweepTestFixtures.StaticImport

/-- Positive control whose side effect distinguishes execution from inspection. -/
initialize executed : Bool ← do
  if let some path ← IO.getEnv "VCVIO_INIT_SWEEP_SIDE_EFFECT_PATH" then
    IO.FS.writeFile path "initializer executed"
  pure true

end VCVioInitSweepTestFixtures.StaticImport
