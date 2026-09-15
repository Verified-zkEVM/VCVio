/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.FinEnum

/-! # The work that has no constant to read

A declaration with parameters is not itself initialised at module load — but the compiler
may lift a parameterless *specialisation* out of its body, and when that specialisation's
result is a ground value the backend assigns it in the module initialiser like any other
value. The module below has no parameterless environment constant at all, and its initialiser
assigns three specialisations that enumerate their carrier before `main` runs. Reading
environment constants cannot see any of them, which is why the sweep also walks the module's
compiled declarations.

The three are one per kind of evidence the name carries: `Fintype.card` is on the
entry-point list; `FinEnum.toList` is on it for the other enumeration class; and `countOf` is
a *user* function, on no list at all, which gives itself away by taking a `Fintype` instance
as an argument. A clause that tested only the entry-point list would accept the third, and
one that tested only what a segment returns would accept all three — `Fintype.card` returns
`ℕ`, `FinEnum.toList` returns a `List`.
-/

public section

namespace VCVioInitSweepTestFixtures.Hazard.Specialised

/-- A function over an eight-element carrier, so the value clause is right to leave it
alone — and the specialisation the compiler lifts out of it is not left alone. Nothing here
is a parameterless environment constant, so the only thing the gate can see is the compiled
declaration. -/
def carrierCount (_u : Unit) : Nat := Fintype.card (Fin 3 → Bool)

/-- The same shape in the other enumeration class. `FinEnum.toList` returns a `List`, so a
test on what a segment *returns* cannot see it. -/
def carrierList (_u : Unit) : Nat := (FinEnum.toList (Fin 2 × Fin 2 × Fin 2)).length

/-- A user helper that enumerates: on no entry-point list, and identified by the instance it
takes. -/
def countOf (α : Type) [Fintype α] : Nat := (Finset.univ : Finset α).card

/-- Its call site, which is what makes the specialisation parameterless. -/
def carrierCountViaHelper (_u : Unit) : Nat := countOf (Fin 3 → Bool)

end VCVioInitSweepTestFixtures.Hazard.Specialised
