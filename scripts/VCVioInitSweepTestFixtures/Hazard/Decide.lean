/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Data.Fintype.Pi

/-! # The route with no `Fintype` in the source at all

A top-level decidability check over a bounded quantifier enumerates the carrier when the
module is loaded, through the `Decidable` instance the elaborator picks. The author wrote no
instance and named no enumeration function; the constant the gate has to see is the `Fintype`
the `Decidable` instance carries.
-/

public section

namespace VCVioInitSweepTestFixtures.Hazard.Decide

/-- An eight-element carrier behind an alias, which is the shape the hazard takes: nothing at
the use site below says how large it is. -/
abbrev Carrier : Type := Fin 3 → Bool

/-- Evaluated when the module is loaded, and it enumerates `Carrier` to get there. -/
def everyPointFixesZero : Bool := decide (∀ x : Carrier, x 0 = x 0)

end VCVioInitSweepTestFixtures.Hazard.Decide
