/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option

/-!
# Collision extraction from a settled climb against a settled honest root

A climb `climbM nodeHash idx node auth` recomputes the root of a perfect tree from a leaf value
and its sibling path; `merkleRootM leaf nodeHash hp t` computes the honest root of the height-`hp`
subtree at index `t` from the honest leaves.  When both are settled under one partial oracle and
agree, the honest and the climbed values agree at some height and, one level down, either still
agree or split.  Following the root path of `idx` downward from the root, the descent
(`climbM_merkleRootM_cases`) either reaches the leaf, so that `node` is the settled honest leaf
at `idx`, or stops at an internal node where two settled `nodeHash` queries with the same height,
the same index and the same answer have different inputs, one input pair being the settled honest
children of that node.  `climbM_merkleRootM_step` is the one-level descent.

## Scope

* No property of any particular oracle implementation is proved here; `impl` is any
  interpretation into `Option`.
* The leaf program and the node-hash program are arbitrary: nothing here depends on how the
  honest leaves are derived.
* Nothing here is probabilistic, and nothing here is quantum.

## Labels

Two declarations: `climbM_merkleRootM_step`, `climbM_merkleRootM_cases`.
-/

public section

namespace PerfectMerkleTree

open OracleComp OracleSpec

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {Y : Type v} (impl : QueryImpl spec Option)
  (leaf : ℕ → OracleComp spec Y) (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)

/-- One level of the descent.  If the climb along the first `k + 1` siblings and the honest
height-`(k + 1)` ancestor of `idx` are settled at the same value, then either the climb along
the first `k` siblings and the honest height-`k` ancestor are settled at the same value, or the
honest children of the height-`(k + 1)` ancestor and the climb's input pair there differ while
both `nodeHash` queries are settled at that value. -/
theorem climbM_merkleRootM_step (idx : ℕ) (node : Y) (auth : List Y) (k : ℕ)
    (hk : k < auth.length) {w : Y}
    (hclimb : simulateQ impl (climbM nodeHash idx node (auth.take (k + 1))) = some w)
    (hnode : simulateQ impl (merkleRootM leaf nodeHash (k + 1) (idx / 2 ^ (k + 1))) = some w) :
    (∃ v, simulateQ impl (climbM nodeHash idx node (auth.take k)) = some v ∧
        simulateQ impl (merkleRootM leaf nodeHash k (idx / 2 ^ k)) = some v) ∨
    ∃ l r l' r', (l, r) ≠ (l', r') ∧
      simulateQ impl (merkleRootM leaf nodeHash k (2 * (idx / 2 ^ (k + 1)))) = some l ∧
      simulateQ impl (merkleRootM leaf nodeHash k (2 * (idx / 2 ^ (k + 1)) + 1)) = some r ∧
      simulateQ impl (nodeHash (k + 1) (idx / 2 ^ (k + 1)) l r) = some w ∧
      simulateQ impl (nodeHash (k + 1) (idx / 2 ^ (k + 1)) l' r') = some w := by
  have hk' : k < (auth.take (k + 1)).length := by simp [List.length_take]; omega
  obtain ⟨v, w', hv, hw', hq⟩ :=
    simulateQ_climbM_query_settled impl nodeHash idx node (auth.take (k + 1)) hclimb hk'
  rw [List.take_take, Nat.min_self, hclimb] at hw'
  rw [List.take_take, Nat.min_eq_left (Nat.le_succ k)] at hv
  obtain rfl := Option.some.inj hw'
  rw [List.getElem_take] at hq
  obtain ⟨l, r, hl, hr, hq'⟩ :=
    (simulateQ_merkleRootM_succ_eq_some_iff impl leaf nodeHash k (idx / 2 ^ (k + 1))).mp hnode
  have hdiv : idx / 2 ^ (k + 1) = idx / 2 ^ k / 2 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have hdm := Nat.div_add_mod (idx / 2 ^ k) 2
  split_ifs at hq with hpar
  · have h2 : 2 * (idx / 2 ^ (k + 1)) = idx / 2 ^ k := by omega
    by_cases heq : (l, r) = (v, auth[k])
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact Or.inl ⟨l, hv, h2 ▸ hl⟩
    · exact Or.inr ⟨l, r, v, auth[k], heq, hl, hr, hq', hq⟩
  · have h2 : 2 * (idx / 2 ^ (k + 1)) + 1 = idx / 2 ^ k := by omega
    by_cases heq : (l, r) = (auth[k], v)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact Or.inl ⟨r, hv, h2 ▸ hr⟩
    · exact Or.inr ⟨l, r, auth[k], v, heq, hl, hr, hq', hq⟩

/-- A settled climb from `node` at leaf `idx` along a path of length `hp` that reaches the
settled honest root of the height-`hp` subtree containing `idx` either starts at the settled
honest leaf `idx`, or exhibits at some internal node `(h, idx / 2 ^ h)` on the root path of `idx`
two settled `nodeHash` queries with the same answer, one on the settled honest children of that
node and one on a different pair. -/
theorem climbM_merkleRootM_cases (idx hp t : ℕ) (hidx : idx / 2 ^ hp = t) (node : Y)
    (auth : List Y) (hlen : auth.length = hp) {root : Y}
    (hclimb : simulateQ impl (climbM nodeHash idx node auth) = some root)
    (hroot : simulateQ impl (merkleRootM leaf nodeHash hp t) = some root) :
    simulateQ impl (leaf idx) = some node ∨
    ∃ h l r l' r' v, 0 < h ∧ h ≤ hp ∧ (l, r) ≠ (l', r') ∧
      simulateQ impl (merkleRootM leaf nodeHash (h - 1) (2 * (idx / 2 ^ h))) = some l ∧
      simulateQ impl (merkleRootM leaf nodeHash (h - 1) (2 * (idx / 2 ^ h) + 1)) = some r ∧
      simulateQ impl (nodeHash h (idx / 2 ^ h) l r) = some v ∧
      simulateQ impl (nodeHash h (idx / 2 ^ h) l' r') = some v := by
  suffices key : ∀ n ≤ hp,
      (∃ v, simulateQ impl (climbM nodeHash idx node (auth.take (hp - n))) = some v ∧
        simulateQ impl (merkleRootM leaf nodeHash (hp - n) (idx / 2 ^ (hp - n))) = some v) ∨
      ∃ h l r l' r' v, 0 < h ∧ h ≤ hp ∧ (l, r) ≠ (l', r') ∧
        simulateQ impl (merkleRootM leaf nodeHash (h - 1) (2 * (idx / 2 ^ h))) = some l ∧
        simulateQ impl (merkleRootM leaf nodeHash (h - 1) (2 * (idx / 2 ^ h) + 1)) = some r ∧
        simulateQ impl (nodeHash h (idx / 2 ^ h) l r) = some v ∧
        simulateQ impl (nodeHash h (idx / 2 ^ h) l' r') = some v by
    refine (key hp le_rfl).imp (fun ⟨v, hv, hm⟩ => ?_) id
    simp only [Nat.sub_self, List.take_zero, climbM_nil, simulateQ_pure_eq_some_iff] at hv
    simpa [merkleRootM, hv] using hm
  intro n
  induction n with
  | zero =>
    intro _
    exact Or.inl ⟨root, by rwa [Nat.sub_zero, List.take_of_length_le hlen.le],
      by rwa [Nat.sub_zero, hidx]⟩
  | succ n ih =>
    intro hn
    refine (ih (Nat.le_of_succ_le hn)).elim (fun ⟨w, hw, hm⟩ => ?_) Or.inr
    have hsub : hp - n = hp - (n + 1) + 1 := by omega
    rw [hsub] at hw hm
    refine (climbM_merkleRootM_step impl leaf nodeHash idx node auth (hp - (n + 1)) (by omega)
      hw hm).imp id fun ⟨l, r, l', r', hne, hl, hr, hq, hq'⟩ => ?_
    exact ⟨hp - (n + 1) + 1, l, r, l', r', w, Nat.succ_pos _, by omega, hne, by simpa using hl,
      by simpa using hr, hq, hq'⟩

end PerfectMerkleTree
