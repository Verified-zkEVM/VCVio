/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Data.Fintype.Pi

/-! # The work that has no constant to read

A declaration with parameters is not itself initialised at module load — but the compiler
may lift a parameterless *specialisation* out of its body, and when that specialisation's
result is a ground value the backend assigns it in the module initialiser like any other
value. The module below has no parameterless environment constant at all: the only thing its
initialiser assigns is `Fintype.card._at_.….carrierCount.spec_0`, which enumerates the
carrier through `Fintype.piFinset` before `main` runs. Reading environment constants cannot
see it, which is why the sweep also walks the module's compiled declarations and tests the
names the specialiser builds.
-/

public section

namespace VCVioInitSweepTestFixtures.Hazard.Specialised

/-- A function over an eight-element carrier, so the value clause is right to leave it
alone — and the specialisation the compiler lifts out of it is not left alone. Nothing else
is declared here: the module has no parameterless environment constant, so the only thing
the gate can see is the compiled declaration. -/
def carrierCount (_u : Unit) : Nat := Fintype.card (Fin 3 → Bool)

end VCVioInitSweepTestFixtures.Hazard.Specialised
