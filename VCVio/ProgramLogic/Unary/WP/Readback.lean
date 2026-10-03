/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Prelude.Core

/-!
# Readback of the bound readings' verification conditions

Core's `vcgen` leaves the verification conditions of a triple of the lower or upper reading in the
vocabulary of its lattice: `Lean.Order.PartialOrder.rel` for the order, `binderNameHint` on
continuations, the `pushOption`/`pushExcept` of a transformer's postcondition, the reading's
bottom, and, under the upper reading, everything inside `OrderDual.toDual`. The two simp sets
registered here read those conditions back into `≤` on `ℝ≥0∞`:

* `lower_readback`: `rel` is `≤`, the bottom is `0`, a predicate indicator is an indicator;
* `upper_readback`: `rel` is `≤` with its sides swapped (`OracleComp.Upper.rel_iff`), and
  `ofDual` is pushed through sums, products, numerals and the expectation.

`prvcgen` runs the set of its reading on every verification condition; after a bare `vcgen`,
`simp only [upper_readback]` (respectively `lower_readback`) does the same. Under the upper-bound
reading the set must run before any other `simp`: `simp` alone rewrites `toDual 5` to the dual
numeral and `rel` to the dual's order, leaving `5 ≤ 3` in `ℝ≥0∞ᵒᵈ`, which holds but which no
numeral tactic closes. The lemmas are tagged where they live, in
`VCVio.ProgramLogic.Unary.WP.LowerSpecs` and `VCVio.ProgramLogic.Unary.WP.Upper`.
-/

public section

/-- Readback of the lower-bound reading's verification conditions: `rel` as `≤`, the reading's
bottom as `0`, `binderNameHint`, `pushOption`/`pushExcept` and predicate indicators unfolded. -/
register_simp_attr lower_readback

/-- Readback of the upper-bound reading's verification conditions: `rel` as `≤` with its sides
swapped, `ofDual` pushed through the arithmetic and the expectation, `binderNameHint`,
`pushOption`/`pushExcept` and predicate indicators unfolded. -/
register_simp_attr upper_readback
