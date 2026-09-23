/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Data.Fintype.Pi

/-! # The value the kernel hides

`opaque x : T := v` hides `v` from unification, not from the backend: the emitted C assigns
`x` from an `_init_` function that evaluates `v` exactly as it would for a `def`. The gate
therefore reads an `opaque` declaration's value like any other, which is also why the
blind-spot line of its summary can stay at zero.
-/

public section

namespace VCVioInitSweepTestFixtures.Hazard.Opaque

/-- An eight-element enumeration, built when the module is loaded and unreadable to anything
that stops at the kernel's view of the constant. -/
opaque enumeration : Finset (Fin 3 → Bool) := Finset.univ

end VCVioInitSweepTestFixtures.Hazard.Opaque
