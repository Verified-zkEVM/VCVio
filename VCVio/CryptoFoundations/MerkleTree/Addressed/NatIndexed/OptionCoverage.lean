/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option

/-!
# Coverage of a perfect Merkle tree under a partial oracle

What a settled reading of a perfect-tree program settles below it, when the oracle is interpreted
into `Option`.  A settled subtree root settles the root of every subtree under it
(`exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq`).  A settled authentication path is settled
entrywise: entry `j` is the settled root of the sibling subtree at height `j`
(`simulateQ_intrinsicAuthPathM_eq_some_iff`).  A settled climb from a settled leaf along a
settled authentication path settles every ancestor of the leaf, the running value of the climb being
the settled sub-root at each height (`simulateQ_merkleRootM_div_pow_eq_some_of_climbM`); conversely,
a settled ancestor settles the climb to it (`simulateQ_climbM_eq_some_of_merkleRootM`). An
authentication path settled under one implementation is settled at the same value under another
that settles its sibling sub-roots alike (`simulateQ_intrinsicAuthPathM_of_merkleRootM`).

## Scope

* The one-step decompositions these rest on (`simulateQ_merkleRootM_succ_eq_some_iff`,
  `simulateQ_intrinsicAuthPathM_succ_eq_some_iff`, `simulateQ_climbM_concat_eq_some_iff`) are in
  `VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option`.
* No property of any particular oracle implementation is proved here.
* Nothing here is probabilistic, and nothing here is quantum.

## Labels

Five declarations.

*Settled subtrees*: `exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq`.

*Settled paths*: `simulateQ_intrinsicAuthPathM_eq_some_iff`.

*Settled climbs*: `simulateQ_merkleRootM_div_pow_eq_some_of_climbM`,
`simulateQ_climbM_eq_some_of_merkleRootM`.

*Transferred paths*: `simulateQ_intrinsicAuthPathM_of_merkleRootM`.
-/

public section

namespace PerfectMerkleTree

open OracleComp OracleSpec

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {Y : Type v} (impl : QueryImpl spec Option)
  (leaf : ℕ → OracleComp spec Y) (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)

/-! ## Settled subtrees -/

/-- A settled subtree root settles the root of every subtree below it. -/
theorem exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq {z t : ℕ} {r : Y}
    (h : simulateQ impl (merkleRootM leaf nodeHash z t) = some r) {z' t' : ℕ} (hz : z' ≤ z)
    (ht : t' / 2 ^ (z - z') = t) :
    ∃ v, simulateQ impl (merkleRootM leaf nodeHash z' t') = some v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hz
  clear hz
  induction k generalizing t r with
  | zero =>
    simp only [Nat.add_zero, Nat.sub_self, pow_zero, Nat.div_one] at ht
    exact ⟨r, ht ▸ h⟩
  | succ k ih =>
    obtain ⟨l, rr, hl, hr, -⟩ :=
      (simulateQ_merkleRootM_succ_eq_some_iff impl leaf nodeHash (z' + k) t).mp h
    have hsplit : t' / 2 ^ (z' + k - z') / 2 = t := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ, ← ht, Nat.add_sub_cancel_left,
        Nat.add_sub_cancel_left]
    rcases Nat.even_or_odd (t' / 2 ^ (z' + k - z')) with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact ih hl (by omega)
    · exact ih hr (by omega)

/-! ## Settled paths -/

/-- An authentication path is settled exactly when it is settled entrywise: entry `j` is the
settled root of the sibling subtree at height `j`. -/
theorem simulateQ_intrinsicAuthPathM_eq_some_iff (idx : ℕ) {z : ℕ} {path : Vector Y z} :
    simulateQ impl (intrinsicAuthPathM leaf nodeHash idx z) = some path ↔
      ∀ j : Fin z, simulateQ impl (merkleRootM leaf nodeHash j (sibling (idx / 2 ^ j.val))) =
        some path[j] := by
  induction z with
  | zero =>
    simp only [intrinsicAuthPathM, simulateQ_pure_eq_some_iff]
    exact ⟨fun _ j => j.elim0, fun _ => Vector.eq_empty.symm⟩
  | succ z ih =>
    rw [simulateQ_intrinsicAuthPathM_succ_eq_some_iff]
    constructor
    · rintro ⟨prefix_, sib, hpre, hsib, rfl⟩ j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hsib
      · simpa [Vector.getElem_push] using ih.mp hpre j
    · intro h
      refine ⟨path.pop, path[z], ih.mpr fun j => ?_, ?_, Vector.push_pop_back path⟩
      · simpa [Vector.getElem_pop] using h j.castSucc
      · simpa using h (Fin.last z)

/-! ## Settled climbs -/

/-- If leaf `idx` is settled at `y`, its authentication path over `z` levels is settled at
`path`, and the climb from `y` along `path` is settled at `v`, then the height-`z` ancestor of
`idx` is settled, at `v`. -/
theorem simulateQ_merkleRootM_div_pow_eq_some_of_climbM (idx : ℕ) {y : Y}
    (hy : simulateQ impl (leaf idx) = some y) {z : ℕ} {path : Vector Y z} {v : Y}
    (hpath : simulateQ impl (intrinsicAuthPathM leaf nodeHash idx z) = some path)
    (hclimb : simulateQ impl (climbM nodeHash idx y path.toList) = some v) :
    simulateQ impl (merkleRootM leaf nodeHash z (idx / 2 ^ z)) = some v := by
  induction z generalizing v with
  | zero =>
    obtain rfl : y = v := by simpa [Vector.eq_empty (xs := path)] using hclimb
    simpa [merkleRootM] using hy
  | succ z ih =>
    obtain ⟨prefix_, sib, hpre, hsib, rfl⟩ :=
      (simulateQ_intrinsicAuthPathM_succ_eq_some_iff impl leaf nodeHash idx z).mp hpath
    rw [Vector.toList_push] at hclimb
    obtain ⟨w, hw, hq⟩ :=
      (simulateQ_climbM_concat_eq_some_iff impl nodeHash idx y prefix_.toList sib).mp hclimb
    have hnode := ih hpre hw
    rw [Vector.length_toList] at hq
    rw [simulateQ_merkleRootM_succ_eq_some_iff]
    have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    split_ifs at hq with h
    · have hl : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z := by omega
      have hr : 2 * (idx / 2 ^ (z + 1)) + 1 = sibling (idx / 2 ^ z) := by
        simp only [sibling, h, ↓reduceIte]
        omega
      exact ⟨w, sib, hl ▸ hnode, hr ▸ hsib, hq⟩
    · have hl : 2 * (idx / 2 ^ (z + 1)) = sibling (idx / 2 ^ z) := by
        simp only [sibling, h, ↓reduceIte]
        omega
      have hr : 2 * (idx / 2 ^ (z + 1)) + 1 = idx / 2 ^ z := by omega
      exact ⟨sib, w, hl ▸ hsib, hr ▸ hnode, hq⟩

/-- If leaf `idx` is settled at `y`, its authentication path over `z` levels at `path`, and its
height-`z` ancestor at `v`, then the climb from `y` along `path` is settled at `v`. -/
theorem simulateQ_climbM_eq_some_of_merkleRootM (idx : ℕ) {y : Y}
    (hy : simulateQ impl (leaf idx) = some y) {z : ℕ} {path : Vector Y z} {v : Y}
    (hpath : simulateQ impl (intrinsicAuthPathM leaf nodeHash idx z) = some path)
    (hroot : simulateQ impl (merkleRootM leaf nodeHash z (idx / 2 ^ z)) = some v) :
    simulateQ impl (climbM nodeHash idx y path.toList) = some v := by
  induction z generalizing v with
  | zero =>
    simp only [pow_zero, Nat.div_one, merkleRootM] at hroot
    obtain rfl : y = v := Option.some_inj.1 (hy.symm.trans hroot)
    simp [Vector.eq_empty (xs := path), climbM_nil]
  | succ z ih =>
    obtain ⟨prefix_, sib, hpre, hsib, rfl⟩ :=
      (simulateQ_intrinsicAuthPathM_succ_eq_some_iff impl leaf nodeHash idx z).mp hpath
    obtain ⟨l, r, hl, hr, hq⟩ :=
      (simulateQ_merkleRootM_succ_eq_some_iff impl leaf nodeHash z _).mp hroot
    rw [Vector.toList_push, simulateQ_climbM_concat_eq_some_iff, Vector.length_toList]
    have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    split_ifs with h
    · have h1 : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z := by omega
      have h2 : 2 * (idx / 2 ^ (z + 1)) + 1 = sibling (idx / 2 ^ z) := by
        simp only [sibling, h, ↓reduceIte]
        omega
      rw [h1] at hl
      rw [h2, hsib] at hr
      obtain rfl := Option.some_inj.1 hr
      exact ⟨l, ih hpre hl, hq⟩
    · have h1 : 2 * (idx / 2 ^ (z + 1)) = sibling (idx / 2 ^ z) := by
        simp only [sibling, h, ↓reduceIte]
        omega
      have h2 : 2 * (idx / 2 ^ (z + 1)) + 1 = idx / 2 ^ z := by omega
      rw [h1, hsib] at hl
      rw [h2] at hr
      obtain rfl := Option.some_inj.1 hl
      exact ⟨r, ih hpre hr, hq⟩

/-! ## Transferred paths -/

/-- If every sibling sub-root of leaf `idx` below height `z` that is settled under `impl` is
settled at the same value under `impl'`, then an authentication path of `idx` over `z` levels
settled under `impl` is settled at the same value under `impl'`. -/
theorem simulateQ_intrinsicAuthPathM_of_merkleRootM (impl' : QueryImpl spec Option) (idx : ℕ) :
    ∀ {z : ℕ} {path : Vector Y z},
      (∀ z' < z, ∀ w, simulateQ impl (merkleRootM leaf nodeHash z' (sibling (idx / 2 ^ z'))) =
        some w → simulateQ impl' (merkleRootM leaf nodeHash z' (sibling (idx / 2 ^ z'))) =
          some w) →
      simulateQ impl (intrinsicAuthPathM leaf nodeHash idx z) = some path →
      simulateQ impl' (intrinsicAuthPathM leaf nodeHash idx z) = some path :=
  fun hs h => (simulateQ_intrinsicAuthPathM_eq_some_iff impl' leaf nodeHash idx).2 fun j =>
    hs j j.isLt _ ((simulateQ_intrinsicAuthPathM_eq_some_iff impl leaf nodeHash idx).1 h j)

end PerfectMerkleTree
