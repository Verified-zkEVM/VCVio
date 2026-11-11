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

The collision property is the set of databases with equal answers at two distinct inputs
(`OracleComp.CacheHasCollision`; answers at different inputs may have different types and are
compared by heterogeneous equality). Extending a database never removes a collision, whatever the
answer measure.

For the quantitative bound, answers are uniform on finite answer types with at least `n` elements
each. A database with fewer than `t` entries stores at most `t - 1` answers, and a fresh answer
creates a collision only by equalling one of them. So the instability of the collision property
with query bound `t` is at most `(t - 1) / n`. Here `t - 1` is subtraction in `ℕ`, so the bound is
`0` at `t = 0`, and division is in `ℝ≥0∞`, so `n = 0` is allowed.

This is a classical bound for one fresh extension. A quantum collision-success bound also needs
the compressed-oracle norm estimate and an argument accumulating amplitude across queries.
For example, CMS19 Lemma 5.7 (ePrint 2019/834, PDF p. 24) gives `6 q² I(P,q)` for a database
game, using the associated property (with the empty database outside it) and the lifting hypotheses.
This is not obtained by summing the classical one-step probabilities. No quantum accumulation
theorem is proved here.

Collision persistence supports arbitrary equal input and answer universes, as does
`CacheHasCollision`. The quantitative counting API is restricted to `Type` by the existing
`Birthday` counting lemma. The Merkle application separately inherits its `Type` query and label
restriction from `MerkleTreeExtractability.NodeQueryModel`.

## Main statements

* `OracleComp.CacheHasCollision.mono`: collisions persist when a database is extended.
* `OracleSpec.QueryCache.flip_cacheHasCollision_compl`: the flip probability from "collision" to
  "no collision" is `0`.
* `OracleSpec.QueryCache.flip_compl_cacheHasCollision_le`: the flip probability from
  "no collision" to "collision" is at most `(t - 1) / n`.
* `OracleSpec.QueryCache.instability_cacheHasCollision_le`: the resulting instability bound, with
  the corollaries `instability_cacheHasCollision_le_div` (the bound `t / n`) and
  `instability_cacheHasCollision_lt` (the strict bound `t / n` for `0 < t` and `0 < n`).

## References

* A. Chiesa, P. Manohar, N. Spooner, *Succinct Arguments in the Quantum Random Oracle Model*,
  TCC 2019, ePrint 2019/834: Lemma 6.11 (PDF p. 35). The printed bound `I(P_col, t) < t / 2^λ` is
  strict, and fails at `t = 0`, where both sides are `0`; `instability_cacheHasCollision_lt`
  assumes `0 < t`.
* A. Chiesa, Z. Di, Z. Hu, Y. Zheng, *How to Prove Post-Quantum Security for Succinct
  Non-Interactive Reductions*, ePrint 2025/2166: Lemma 8.7 (PDF p. 56), the non-strict bound
  `t / 2^σ`.
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

universe u

/-- One fresh answer never removes a collision: the flip probability from "collision" to
"no collision" is `0`. -/
theorem flip_cacheHasCollision_compl {ι : Type u} {spec : OracleSpec.{u, u} ι}
    [DecidableEq ι] [AnswerMeasure spec] (t : ℕ) :
    flip {D : QueryCache spec | CacheHasCollision D} {D | CacheHasCollision D}ᶜ t = 0 := by
  apply nonpos_iff_eq_zero.mp
  apply flip_le_iff.mpr
  intro D hD _ x hx
  have hempty : {a : spec.Range x | D.cacheQuery x a ∈
      ({D : QueryCache spec | CacheHasCollision D}ᶜ)} = ∅ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
    exact not_not.mpr (CacheHasCollision.mono (le_cacheQuery D hx) hD)
  rw [updateProb, hempty, MeasureTheory.measure_empty]

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} [DecidableEq ι]

variable [UniformAnswerMeasure spec] [∀ x, Fintype (spec.Range x)]

/-- With uniform answers on finite answer types, updating a collision-free cache `D` at `x`
creates a collision with probability at most `|S| / |spec.Range x|`, where the finite set `S`
contains every populated key of `D`.

The update may overwrite an occupied key. A collision after the update must match the new answer
with an answer stored at another key, so at most `|S|` answers are bad. For a fresh `x`, this is the
counting step in CMS19 Lemma 6.11 (ePrint 2019/834, PDF p. 35). -/
theorem updateProb_cacheHasCollision_le {D : QueryCache spec} (hD : ¬CacheHasCollision D)
    {S : Finset spec.Domain} (hS : ∀ x', D x' ≠ none → x' ∈ S) (x : spec.Domain) :
    D.updateProb x {D' | CacheHasCollision D'} ≤
      (S.card : ℝ≥0∞) / Fintype.card (spec.Range x) := by
  classical
  rw [updateProb_eq_card_div]
  exact ENNReal.div_le_div_right
    (by exact_mod_cast card_responses_creating_cacheCollision_le (t := x) hD hS) _

/-- With uniform answers on finite answer types of cardinality at least `n`,
`flip(P_colᶜ → P_col,t) ≤ (t - 1) / n`. The initial database has fewer than `t` entries and the
updated input is fresh. Subtraction is in `ℕ` before casting to `ℝ≥0∞`.

This is the entering-collision estimate underlying CMS19 Lemma 6.11 (ePrint 2019/834, PDF p. 35)
and CDHZ Lemma 8.7 (ePrint 2025/2166, PDF p. 56). -/
theorem flip_compl_cacheHasCollision_le {n : ℕ} (hn : ∀ x, n ≤ Fintype.card (spec.Range x))
    (t : ℕ) :
    flip {D : QueryCache spec | CacheHasCollision D}ᶜ {D | CacheHasCollision D} t ≤
      ((t - 1 : ℕ) : ℝ≥0∞) / n := by
  refine flip_le_iff.mpr fun D hD hlt x _ => ?_
  obtain ⟨S, hScard, hS⟩ := exists_finset_card_lt_of_encard_lt hlt
  exact (updateProb_cacheHasCollision_le hD hS x).trans
    (ENNReal.div_le_div (by exact_mod_cast Nat.le_sub_one_of_lt hScard)
      (by exact_mod_cast hn x))

/-- With uniform answers on finite answer types of at least `n` elements each, the collision
property has instability at most `(t - 1) / n` with query bound `t`. Here `t - 1` is subtraction
in `ℕ` before the cast to `ℝ≥0∞`.

A fresh answer never removes a collision, and creates one only by equalling one of the at most
`t - 1` stored answers. For `n > 0` this sharpens Chiesa–Manohar–Spooner, Lemma 6.11 (ePrint
2019/834, PDF p. 35), and Chiesa–Di–Hu–Zheng, Lemma 8.7 (ePrint 2025/2166, PDF p. 56). -/
theorem instability_cacheHasCollision_le {n : ℕ} (hn : ∀ x, n ≤ Fintype.card (spec.Range x))
    (t : ℕ) :
    instability {D : QueryCache spec | CacheHasCollision D} t ≤ ((t - 1 : ℕ) : ℝ≥0∞) / n :=
  max_le (flip_compl_cacheHasCollision_le hn t)
    ((flip_cacheHasCollision_compl t).trans_le zero_le)

/-- With uniform answers on finite answer types of cardinality at least `n`, collision
instability satisfies `I(P_col,t) ≤ t / n`. This follows from
`instability_cacheHasCollision_le`; see CDHZ Lemma 8.7 (ePrint 2025/2166, PDF p. 56). -/
theorem instability_cacheHasCollision_le_div {n : ℕ}
    (hn : ∀ x, n ≤ Fintype.card (spec.Range x)) (t : ℕ) :
    instability {D : QueryCache spec | CacheHasCollision D} t ≤ (t : ℝ≥0∞) / n :=
  (instability_cacheHasCollision_le hn t).trans
    (ENNReal.div_le_div_right (by exact_mod_cast Nat.sub_le t 1) _)

/-- With uniform answers on finite answer types of cardinality at least `n > 0`, collision
instability satisfies `I(P_col,t) < t / n` for `t > 0`.
This is the strict form of CMS19 Lemma 6.11 (ePrint 2019/834, PDF p. 35), with the positive-query
hypothesis needed because both sides are zero at `t = 0`. -/
theorem instability_cacheHasCollision_lt {n : ℕ} (hn : ∀ x, n ≤ Fintype.card (spec.Range x))
    (hn0 : 0 < n) {t : ℕ} (ht : 0 < t) :
    instability {D : QueryCache spec | CacheHasCollision D} t < (t : ℝ≥0∞) / n :=
  (instability_cacheHasCollision_le hn t).trans_lt
    (ENNReal.div_lt_div_right (by exact_mod_cast hn0.ne') (ENNReal.natCast_ne_top n)
      (by exact_mod_cast Nat.sub_one_lt ht.ne'))

end OracleSpec.QueryCache
