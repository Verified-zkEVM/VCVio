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
  rw [OracleComp.prEvent_bind_eq_tsum]
  calc ∑' value, Pr{let x ← first}[x = value] *
        Pr{let pair ← rest value >>= fun result => pure (value, result)}[event pair.1 pair.2]
      = ∑' value, Pr{let x ← first}[x = value] * Pr{let x ← rest value}[(event value) x] :=
        tsum_congr fun value => congrArg _ (by rw [bind_pure_comp, prEvent_map]; rfl)
    _ ≤ ∑' value, Pr{let x ← first}[x = value] * bound := by
        refine ENNReal.tsum_le_tsum fun value => ?_
        by_cases hmem : value ∈ support first
        · exact mul_le_mul' le_rfl (hrest value hmem)
        · rw [(prEvent_eq_zero_of_not_mem_support _) hmem, zero_mul]
          exact zero_le
    _ = (∑' value, Pr{let x ← first}[x = value]) * bound := ENNReal.tsum_mul_right
    _ ≤ 1 * bound := mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl
    _ = bound := one_mul bound

/-- Equal laws have equal supports — the one thing needed to read a support off a
presampling identity. -/
theorem support_eq_of_evalDistEq {α : Type} {left right : ProbComp α}
    (hlaw : 𝒟[left] = 𝒟[right]) : support left = support right := by
  ext value
  rw [mem_support_iff, mem_support_iff, prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton, hlaw]

end SlhDsaSecurity.Averaging
