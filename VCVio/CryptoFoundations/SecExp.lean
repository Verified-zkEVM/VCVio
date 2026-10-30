/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.SecExp.Measure
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Security Experiments

This file defines `BoundedAdversary α β`, an oracle computation bundled with a query bound, and
re-exports the Boolean hidden-bit lemmas of `VCVio.CryptoFoundations.SecExp.Measure`.
-/

@[expose] public section

universe u v w

open MeasureTheory OracleComp OracleSpec ENNReal Polynomial Prod

/-- A security adversary bundling a computation with a bound on the number of queries it makes,
where the bound must be shown to satisfy `IsQueryBound`.
We also require an explicit list of all oracles used in the computation,
which is necessary in order to make certain reductions computable. -/
structure BoundedAdversary {ι : Type u} [DecidableEq ι]
    (spec : OracleSpec ι) (α β : Type u) where
  /-- The adversary's computation on an input, with access to the oracles of `spec`. -/
  run : α → OracleComp spec β
  /-- The per-oracle query bound: on every input, `run` queries oracle `i` at most `qb i`
  times. -/
  qb : ι → ℕ
  qb_isQueryBound (x : α) : IsPerIndexQueryBound (run x) (qb)
  /-- The oracles the adversary may query, listed explicitly: exactly those with a nonzero query
  bound. -/
  activeOracles : List ι
  mem_activeOracles_iff (i : ι) : i ∈ activeOracles ↔ qb i ≠ 0

namespace BoundedAdversary

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}

end BoundedAdversary
