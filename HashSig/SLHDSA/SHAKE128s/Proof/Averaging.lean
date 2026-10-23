/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment

/-!
# Averaging a bound over a prefix

The warmed game draws its seeds and walks the canonical graph before the adversary runs, and
every charge then applies to the rest of the run with the cells held fixed. Turning those
per-prefix bounds into a bound on the whole run is the one probabilistic step involved, and it
is the obvious one: a bound that holds for every value of the prefix holds on average.

Stated for a prefix whose value is kept — which is what the halves need, since the event they
describe names the prefix's cells.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Averaging

/-- **A bound that holds after every prefix holds over the pair.** -/
theorem probEvent_bind_pair_le {α β : Type} (first : ProbComp α) (rest : α → ProbComp β)
    (event : α → β → Prop) (bound : ℝ≥0∞)
    (hrest : ∀ value ∈ support first, Pr{let x ← rest value}[(event value) x] ≤ bound) :
    Pr{let pair ← (do let value ← first; let result ← rest value; pure (value, result))}[event pair.1 pair.2] ≤ bound := by
  refine prEvent_bind_le_of_forall_le_of_support first _ _ fun value hvalue => ?_
  rw [bind_pure_comp, prEvent_map]
  exact hrest value hvalue

/-- Equal laws have equal supports — the one thing needed to read a support off a
presampling identity. -/
theorem support_eq_of_evalDistEq {α : Type} {left right : ProbComp α}
    (hlaw : left =ᵈ right) : support left = support right :=
  OracleComp.support_eq_of_evalDistEq hlaw

end SlhDsaSecurity.Averaging
