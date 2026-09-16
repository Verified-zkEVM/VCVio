/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Data.Fintype.Pi

/-! # The obvious spelling

Elaborates at zero errors, builds clean, and passes every other gate in this repository.
The instance is a top-level constant of non-function type, so the backend evaluates it
when the module is loaded.
-/

public section

namespace VCVioInitSweepTestFixtures.Hazard.Plain

/-- A bundle of carriers; the `Fintype` is demanded for a field. -/
structure Primitives where
  Y : Type

/-- An eight-element carrier: the fixture reproduces the *shape*, not the size. -/
@[expose] def bundle : Primitives := { Y := Fin 3 → Bool }

/-- The hazard. -/
instance : Fintype bundle.Y := inferInstanceAs (Fintype (Fin 3 → Bool))

end VCVioInitSweepTestFixtures.Hazard.Plain
