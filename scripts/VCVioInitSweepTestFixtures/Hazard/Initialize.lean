/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Data.Fintype.Pi

/-! # The route that has no parameterless value at all

`initialize x : T ← e` leaves `x` itself valueless and stores `e` in a separate
initialiser function, which the module initialiser calls. Reading `x` alone would find
nothing to test, so the gate follows the registered initialiser instead.
-/

public section

namespace VCVioInitSweepTestFixtures.Hazard.Initialize

initialize enumeration : Finset (Fin 3 → Bool) ← pure Finset.univ

end VCVioInitSweepTestFixtures.Hazard.Initialize
