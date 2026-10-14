/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.Instability.Basic
public import VCVio.OracleComp.QueryTracking.Birthday

/-!
# Instability of the collision property

The collision property is the set of databases in which two distinct inputs have the same answer
(`OracleComp.CacheHasCollision`). One fresh answer cannot remove a collision, and it creates one
only by hitting an answer already in the database. So, when every answer type has at least `n`
elements, the instability of the collision property with query bound `t` is at most `(t - 1) / n`.

## Main statements

* `OracleComp.CacheHasCollision.mono`: collisions persist when a database is extended.
* `OracleSpec.QueryCache.flip_cacheHasCollision_compl`: the flip probability from "collision" to
  "no collision" is `0`.
* `OracleSpec.QueryCache.flip_compl_cacheHasCollision_le`: the flip probability from
  "no collision" to "collision" is at most `(t - 1) / n`.
* `OracleSpec.QueryCache.instability_cacheHasCollision_le`: the resulting instability bound, with
  the corollaries `instability_cacheHasCollision_le_div` (the bound `t / n`) and
  `instability_cacheHasCollision_lt` (the strict bound `t / n` for `0 < t`).

## Implementation notes

Index and answer types both live in `Type`, as in `OracleComp.CacheHasCollision` and the counting
lemma `OracleComp.card_responses_creating_cacheCollision_le` that this file builds on.

## References

* Alessandro Chiesa, Peter Manohar, Nicholas Spooner, *Succinct Arguments in the Quantum Random
  Oracle Model*, TCC 2019: Lemma 6.11. The printed bound `I(P_col, t) < t / 2^λ` is strict and
  fails at `t = 0`, where both sides are `0`; `instability_cacheHasCollision_lt` assumes `0 < t`.
* Alessandro Chiesa, Zijing Di, Zihan Hu, Yuxi Zheng, *How to Prove Post-Quantum Security for
  Succinct Non-Interactive Reductions*, 2026: Lemma 8.7.
-/

public section

open ENNReal OracleComp Set

namespace OracleComp

/-- A collision in a database persists in every extension of it. -/
theorem CacheHasCollision.mono {ι : Type*} {spec : OracleSpec ι} {D D' : spec.QueryCache}
    (h : D ≤ D') (hD : CacheHasCollision D) : CacheHasCollision D' := by
  obtain ⟨x₁, x₂, u₁, u₂, hne, h₁, h₂, hu⟩ := hD
  exact ⟨x₁, x₂, u₁, u₂, hne, h h₁, h h₂, hu⟩

end OracleComp

namespace OracleSpec.QueryCache

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} [DecidableEq ι]

/-- One fresh answer never removes a collision: the flip probability from "collision" to
"no collision" is `0`. -/
theorem flip_cacheHasCollision_compl [AnswerMeasure spec] (t : ℕ) :
    flip {D : QueryCache spec | CacheHasCollision D} {D | CacheHasCollision D}ᶜ t = 0 :=
  nonpos_iff_eq_zero.mp <| flip_le_iff.mpr fun D hD _ _ hx =>
    (prEvent_eq_zero_of_forall_not _ _ fun _ hu =>
      hu (CacheHasCollision.mono (le_cacheQuery D hx) hD)).le

variable [UniformAnswerMeasure spec] [∀ x, Fintype (spec.Range x)]

/-- Extending a collision-free database at `x` creates a collision with probability at most the
number of populated keys over the number of answers at `x`. The finite set `S` need only cover
the populated keys. -/
theorem extendProb_cacheHasCollision_le {D : QueryCache spec} (hD : ¬CacheHasCollision D)
    {S : Finset spec.Domain} (hS : ∀ x', D x' ≠ none → x' ∈ S) (x : spec.Domain) :
    D.extendProb x {D' | CacheHasCollision D'} ≤
      (S.card : ℝ≥0∞) / Fintype.card (spec.Range x) := by
  classical
  rw [extendProb_eq_card_div]
  exact ENNReal.div_le_div_right
    (by exact_mod_cast card_responses_creating_cacheCollision_le (t := x) hD hS) _

/-- The flip probability from "no collision" to "collision" with query bound `t` is at most
`(t - 1) / n` when every answer type has at least `n` elements. -/
theorem flip_compl_cacheHasCollision_le {n : ℕ} (hn : ∀ x, n ≤ Fintype.card (spec.Range x))
    (t : ℕ) :
    flip {D : QueryCache spec | CacheHasCollision D}ᶜ {D | CacheHasCollision D} t ≤
      ((t - 1 : ℕ) : ℝ≥0∞) / n := by
  refine flip_le_iff.mpr fun D hD hlt x _ => ?_
  obtain ⟨S, hScard, hS⟩ := exists_finset_card_lt_of_encard_lt hlt
  exact (extendProb_cacheHasCollision_le hD hS x).trans
    (ENNReal.div_le_div (by exact_mod_cast Nat.le_sub_one_of_lt hScard)
      (by exact_mod_cast hn x))

/-- The instability of the collision property with query bound `t` is at most `(t - 1) / n` when
every answer type has at least `n` elements. -/
theorem instability_cacheHasCollision_le {n : ℕ} (hn : ∀ x, n ≤ Fintype.card (spec.Range x))
    (t : ℕ) :
    instability {D : QueryCache spec | CacheHasCollision D} t ≤ ((t - 1 : ℕ) : ℝ≥0∞) / n :=
  max_le (flip_compl_cacheHasCollision_le hn t)
    ((flip_cacheHasCollision_compl t).trans_le zero_le)

/-- The instability of the collision property with query bound `t` is at most `t / n` when every
answer type has at least `n` elements. -/
theorem instability_cacheHasCollision_le_div {n : ℕ}
    (hn : ∀ x, n ≤ Fintype.card (spec.Range x)) (t : ℕ) :
    instability {D : QueryCache spec | CacheHasCollision D} t ≤ (t : ℝ≥0∞) / n :=
  (instability_cacheHasCollision_le hn t).trans
    (ENNReal.div_le_div_right (by exact_mod_cast Nat.sub_le t 1) _)

/-- For a positive query bound `t`, the instability of the collision property is strictly below
`t / n` when every answer type has at least `n ≥ 1` elements. -/
theorem instability_cacheHasCollision_lt {n : ℕ} (hn : ∀ x, n ≤ Fintype.card (spec.Range x))
    (hn0 : 0 < n) {t : ℕ} (ht : 0 < t) :
    instability {D : QueryCache spec | CacheHasCollision D} t < (t : ℝ≥0∞) / n :=
  (instability_cacheHasCollision_le hn t).trans_lt
    (ENNReal.div_lt_div_right (by exact_mod_cast hn0.ne') (ENNReal.natCast_ne_top n)
      (by exact_mod_cast Nat.sub_one_lt ht.ne'))

end OracleSpec.QueryCache
