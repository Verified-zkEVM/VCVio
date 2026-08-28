/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Complexitylib.Classes.P.Cobham.Defs
public import Complexitylib.Models.TuringMachine
public import VCVio.OracleComp.OracleComp
public import VCVioComplexity.Asymptotics.PolyBound
public import VCVioComplexity.Backend.OutputBounds
public import VCVioComplexity.Backend.Polynomial
public import VCVioComplexity.Backend.TuringMachine

/-!
# complexitylib backend substrate

This optional package checks that VCVio and a pinned complexitylib revision can coexist under
VCVio's Lean and Mathlib versions. It exposes complexitylib's word-machine and Cobham substrates
and an exact-machine certificate adapter for PolyFun quantitative realizability.

This module deliberately does not define a polynomial-time predicate for `OracleComp`. Importing a
machine model and charging its exact transitions is not yet an oracle-machine adequacy proof. Such
a predicate is introduced only after compilation preserves results, oracle transcripts,
randomness, and a proved polynomial overhead.
-/

@[expose] public section

namespace VCVioComplexity

/-- The concrete word type used by the pinned complexitylib backend. -/
abbrev Word := List Bool

/-- complexitylib's deterministic multi-tape Turing-machine type. -/
abbrev Machine (workTapes : ℕ) := Complexity.TM workTapes

/-- Configurations of complexitylib's concrete machine model. -/
abbrev Configuration (workTapes : ℕ) (state : Type) := Complexity.Cfg workTapes state

/-- Exact pointwise polynomial domination used for resource accounting. -/
abbrev PointwisePolyBound := PolyBound

/-- Cobham's syntax-directed class of feasible fixed-arity word functions. -/
abbrev CobhamFunction {arity : ℕ} (f : (Fin arity → Word) → Word) : Prop :=
  Complexity.Cobham f

/-- The unary Cobham class, exposed as a prospective certificate frontend. -/
abbrev CobhamWordFunction := Complexity.CobhamFP

end VCVioComplexity
