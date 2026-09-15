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

/-- Parameter clause again, this time against the class disjunct: the value names
`Pi.instFintype`, whose type is an application of `Fintype`, and `Fintype.elems` besides —
both kinds of evidence the gate looks for — but the declaration takes a parameter, so the
backend emits a procedure and nothing is enumerated until someone calls it. -/
def enumerationSizeOf (n : ℕ) : ℕ :=
  (Pi.instFintype (α := Fin n) (β := fun _ => Bool)).elems.card

/-- Compiled-code clause: a theorem names `Fintype.card` and carries no compiled code at
all, so no initialiser exists to be slow. -/
theorem card_pos : 0 < Fintype.card (Fin 3 → Bool) := Fintype.card_pos

/-- Enumeration clause: eagerly initialised, and sized by a numeral the author wrote at the
site rather than by a type. That is the boundary `InitSweep.enumerationEntryPoints` draws,
and this is the shape of the one `List.range` in the swept tree's load-time population
(`SLHDSA.Concrete.Keccak.piLUT`). -/
def table : List Nat := List.range 8

/-- Entry-point clause again: an eagerly-initialised `Finset` whose elements are written
out, so its cost is the literal and not the size of a type. -/
def small : Finset Nat := {1, 2, 3}

/-- An `initialize` declaration whose body allocates one cell. Its initialiser runs at
load time and is read by the gate, which is the point of following it — and it names no
entry point, so it is not flagged. -/
initialize counter : IO.Ref Nat ← IO.mkRef 0

end VCVioInitSweepTestFixtures.Clean.Negatives
