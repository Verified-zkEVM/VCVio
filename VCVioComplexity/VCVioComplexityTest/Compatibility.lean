/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Complexitylib.Encoding.Pairing
public import Complexitylib.Models.TuringMachine.SpaceTime.Defs
public import VCVioComplexity.Backend.OutputBounds

/-!
# Compiling complexitylib capability canaries

This module pins the dependency surface that is usable unchanged on VCVio's Lean toolchain: the
base deterministic machine, exact reachability and time predicates, canonical word pairing, and
definitions-only time/space observations. The shell preflight separately reports the unavailable
composition stack without importing a module that cannot produce an object file.
-/

@[expose] public section

namespace VCVioComplexityTest.Compatibility

open _root_.Complexity
open VCVioComplexity.Backend.TuringMachine

/-- The canonical complexitylib parser still retracts its paired word encoding. -/
example (left right : List Bool) : unpair? (pair left right) = some (left, right) := by
  simp

/-- The adapter's closed representation grammar currently uses its original one-bit terminator. -/
example : WordCodec.pair [] [] = [true] :=
  rfl

/-- complexitylib's machine subroutines use the doubled-bit codec with a two-bit separator. -/
example : _root_.Complexity.pair [] [] = [false, true] :=
  rfl

/-- The two concrete empty-pair encodings differ, so machine reuse needs a proved translation. -/
theorem pair_codecs_ne :
    WordCodec.pair [] [] ≠ _root_.Complexity.pair [] [] := by
  decide

/-- Pointwise enlargement of a concrete time bound is available from the compiling base API. -/
example {workTapes : ℕ} {machine : TM workTapes} {function : List Bool → List Bool}
    {bound larger : ℕ → ℕ} (hle : ∀ size, bound size ≤ larger size)
    (computes : machine.ComputesInTime function bound) :
    machine.ComputesInTime function larger :=
  computes.mono hle

/-- The local base-only proof extracts an honest output bound from the same run theorem. -/
example {workTapes : ℕ} {machine : TM workTapes} {function : List Bool → List Bool}
    {bound : ℕ → ℕ} (computes : machine.ComputesInTime function bound)
    (word : List Bool) : (function word).length ≤ bound word.length :=
  output_length_le_of_computesInTime computes word

end VCVioComplexityTest.Compatibility
