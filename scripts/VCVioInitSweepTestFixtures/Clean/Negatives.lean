/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Data.Fintype.Pi

/-! # One negative control per clause of the predicate

A gate whose baseline is zero is only worth something if the zero is hard to reach by
accident. These are the three ways a declaration can name an enumeration entry point, or
be eagerly initialised, and still be harmless.
-/

public section

namespace VCVioInitSweepTestFixtures.Clean.Negatives

/-- Parameter clause: this names `Finset.univ` and compiles, but it takes a parameter, so
the backend emits a procedure and nothing runs until someone calls it. -/
def enumerate (α : Type) [Fintype α] : Finset α := Finset.univ

/-- Compiled-code clause: a theorem names `Fintype.card` and carries no compiled code at
all, so no initialiser exists to be slow. -/
theorem card_pos : 0 < Fintype.card (Fin 3 → Bool) := Fintype.card_pos

/-- Entry-point clause: eagerly initialised, and bounded by an explicit numeral. This is
the shape of the one legitimate `List.range` in the swept tree, and the reason numeric
ranges are not in `InitSweep.enumerationEntryPoints`. -/
def table : List Nat := List.range 8

/-- Entry-point clause again: an eagerly-initialised `Finset` whose elements are written
out, so its cost is the literal and not the size of a type. -/
def small : Finset Nat := {1, 2, 3}

/-- An `initialize` declaration whose body allocates one cell. Its initialiser runs at
load time and is read by the gate, which is the point of following it — and it names no
entry point, so it is not flagged. -/
initialize counter : IO.Ref Nat ← IO.mkRef 0

end VCVioInitSweepTestFixtures.Clean.Negatives
