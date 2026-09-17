/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Data.Fintype.Pi

/-! # The spelling that looks like a fix

`noncomputable` removes the instance's own compiled code and leaves the compiled
auxiliary that carries the enumeration, so the constant the gate flags here is the same
one it flags for the plain spelling.
-/

public section

namespace VCVioInitSweepTestFixtures.Hazard.Noncomputable

/-- A bundle of carriers; the `Fintype` is demanded for a field. -/
structure Primitives where
  Y : Type

/-- An eight-element carrier: the fixture reproduces the *shape*, not the size. -/
@[expose] def bundle : Primitives := { Y := Fin 3 → Bool }

/-- The same hazard, with the marker that does not fix it. -/
noncomputable instance : Fintype bundle.Y := inferInstanceAs (Fintype (Fin 3 → Bool))

end VCVioInitSweepTestFixtures.Hazard.Noncomputable
