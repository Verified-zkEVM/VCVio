/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

/-! # A root that does not reach Mathlib

Swept on its own, none of `InitSweep.enumerationEntryPoints` exists in the environment, so
the name test would match nothing and report a clean verdict on a tree it never looked at.
`InitSweep.checkEntryPoints` turns that into an infrastructure failure instead, and this
module is what proves it does.
-/

public section

namespace VCVioInitSweepTestFixtures.Standalone

/-- A load-time value with nothing to say. -/
def marker : Nat := 7

end VCVioInitSweepTestFixtures.Standalone
