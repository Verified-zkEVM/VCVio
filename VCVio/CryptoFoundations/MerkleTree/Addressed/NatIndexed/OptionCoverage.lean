/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Coverage of a perfect Merkle tree under a partial oracle

What a settled reading of a perfect-tree program settles below it, when the oracle is
interpreted into `Option`.  A settled subtree root settles the root of every subtree under it,
hence every leaf and every internal hash query of that subtree
(`exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq`,
`exists_simulateQ_leaf_eq_some_of_merkleRootM`,
`exists_simulateQ_nodeHash_eq_some_of_merkleRootM`).  A settled authentication path is settled
entrywise: entry `j` is the settled root of the sibling subtree at height `j`
(`simulateQ_intrinsicAuthPathM_eq_some_iff`).  A settled climb from a settled leaf along a
settled authentication path settles every ancestor of the leaf, the running value of the climb
being the settled sub-root at each height (`simulateQ_merkleRootM_div_pow_eq_some_of_climbM`).

Read through a query cache, that coverage is a *lower bound on the cache*: a settled subtree root
at height `z` forces the `2 ^ z` leaves below it to be settled, so once a leaf-indexed function
picks out one cache entry per leaf and is injective on the leaf range, the cache holds at least
`2 ^ z` entries (`pow_le_enncard_of_simulateQ_merkleRootM`).  At this generality the injectivity
hypothesis is **necessary**, not a convenience: the unconditional bound is false, witnessed by a
one-query specification whose single cache entry settles every height
(`not_forall_pow_le_enncard_of_simulateQ_merkleRootM`).  A concrete instantiation may still
discharge the hypothesis outright, from properties of its own leaf-key function.

## Scope

* The one-step decompositions these rest on (`simulateQ_merkleRootM_succ_eq_some_iff`,
  `simulateQ_intrinsicAuthPathM_succ_eq_some_iff`, `simulateQ_climbM_concat_eq_some_iff`) are in
  `VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option`.
* No property of any particular oracle implementation is proved here.
* Nothing here is probabilistic, and nothing here is quantum.

## Labels

Eight declarations, and two private witnesses of the last one.

*Settled subtrees*: `exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq`,
`exists_simulateQ_leaf_eq_some_of_merkleRootM`,
`exists_simulateQ_nodeHash_eq_some_of_merkleRootM`.

*Settled paths and climbs*: `simulateQ_intrinsicAuthPathM_eq_some_iff`,
`simulateQ_merkleRootM_div_pow_eq_some_of_climbM`.

*Cache-size lower bounds*: `encard_leafRange`, `pow_le_enncard_of_simulateQ_merkleRootM`,
`not_forall_pow_le_enncard_of_simulateQ_merkleRootM`.
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

/-- Every leaf of a settled subtree is settled. -/
theorem exists_simulateQ_leaf_eq_some_of_merkleRootM {z t : ℕ} {r : Y}
    (h : simulateQ impl (merkleRootM leaf nodeHash z t) = some r) {i : ℕ} (hi : i / 2 ^ z = t) :
    ∃ v, simulateQ impl (leaf i) = some v :=
  exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq impl leaf nodeHash h (Nat.zero_le z)
    (by simpa using hi)

/-- Every internal node of a settled subtree has its hash query settled at the settled roots of
its two children. -/
theorem exists_simulateQ_nodeHash_eq_some_of_merkleRootM {z t : ℕ} {r : Y}
    (h : simulateQ impl (merkleRootM leaf nodeHash z t) = some r) (h' i : ℕ) (hpos : 0 < h')
    (hle : h' ≤ z) (hi : i / 2 ^ (z - h') = t) :
    ∃ l rr v, simulateQ impl (merkleRootM leaf nodeHash (h' - 1) (2 * i)) = some l ∧
      simulateQ impl (merkleRootM leaf nodeHash (h' - 1) (2 * i + 1)) = some rr ∧
      simulateQ impl (nodeHash h' i l rr) = some v := by
  obtain ⟨v, hv⟩ := exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq impl leaf nodeHash h hle hi
  obtain ⟨h'', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  obtain ⟨l, rr, hl, hr, hq⟩ :=
    (simulateQ_merkleRootM_succ_eq_some_iff impl leaf nodeHash h'' i).mp hv
  exact ⟨l, rr, v, hl, hr, hq⟩

/-! ## Settled paths and climbs -/

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

/-! ## Cache-size lower bounds -/

/-- The global leaf indices under the subtree at `(height z, index t)` are `2 ^ z` in number. -/
theorem encard_leafRange (z t : ℕ) : {i : ℕ | i / 2 ^ z = t}.encard = (2 ^ z : ℕ) := by
  have hset : {i : ℕ | i / 2 ^ z = t} = ↑(Finset.Ico (t * 2 ^ z) ((t + 1) * 2 ^ z)) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_Ico, Set.mem_Ico]
    rw [show (i / 2 ^ z = t) ↔ (t ≤ i / 2 ^ z ∧ i / 2 ^ z < t + 1) from by omega,
      Nat.le_div_iff_mul_le (Nat.two_pow_pos z), Nat.div_lt_iff_lt_mul (Nat.two_pow_pos z)]
  rw [hset, Set.encard_coe_eq_coe_finsetCard, Nat.card_Ico]
  refine congrArg _ ?_
  simp only [Nat.succ_mul, Nat.add_sub_cancel_left]

/-- **A subtree at height `z` settled by a cache forces `2 ^ z` cache entries**, once the
leaves' certifying entries are pairwise distinct.  Each of the `2 ^ z` leaves below `(z, t)` is
settled, `key i` is a query the settled reading of leaf `i` forces into the cache, and `key` is
injective on that leaf range, so the cache holds `2 ^ z` distinct entries.

At this generality the injectivity hypothesis is **necessary** rather than convenient: the
unconditional statement is false (`not_forall_pow_le_enncard_of_simulateQ_merkleRootM`).  A
concrete instantiation may nonetheless discharge it from properties of its own `key`. -/
theorem pow_le_enncard_of_simulateQ_merkleRootM (c : QueryCache spec) (key : ℕ → spec.Domain)
    (hkey : ∀ i v, simulateQ c.toPartialImpl (leaf i) = some v → (c (key i)).isSome)
    {z t : ℕ} (hinj : Set.InjOn key {i | i / 2 ^ z = t})
    {r : Y} (h : simulateQ c.toPartialImpl (merkleRootM leaf nodeHash z t) = some r) :
    ((2 ^ z : ℕ) : ENNReal) ≤ QueryCache.enncard c := by
  have hsub : ∀ s ∈ key '' {i | i / 2 ^ z = t}, (c s).isSome := by
    rintro s ⟨i, hi, rfl⟩
    obtain ⟨v, hv⟩ :=
      exists_simulateQ_leaf_eq_some_of_merkleRootM c.toPartialImpl leaf nodeHash h hi
    exact hkey i v hv
  calc ((2 ^ z : ℕ) : ENNReal)
      = (((key '' {i | i / 2 ^ z = t}).encard : ℕ∞) : ENNReal) := by
        rw [hinj.encard_image, encard_leafRange]
        simp
    _ ≤ QueryCache.enncard c := QueryCache.encard_le_enncard _ hsub

/-- The one-entry cache of the specification with one query and one answer. -/
private def unitQueryCache : QueryCache (Unit →ₒ Unit) := QueryCache.ofFn fun _ => some ()

/-- That cache holds exactly one entry. -/
private theorem enncard_unitQueryCache : QueryCache.enncard unitQueryCache = 1 := by
  have h : unitQueryCache.toSet = {⟨(), ()⟩} := by
    ext ⟨t, r⟩
    simp [unitQueryCache, QueryCache.mem_toSet]
  rw [QueryCache.enncard, h, Set.encard_singleton]
  simp

/-- **Without the injectivity hypothesis the bound is false.**  Over the specification with one
query and one answer, a cache of a single entry settles the root at every height, so no bound
`2 ^ z ≤ enncard c` follows from a settled height-`z` subtree alone. -/
theorem not_forall_pow_le_enncard_of_simulateQ_merkleRootM :
    ¬ ∀ {ι : Type} {spec : OracleSpec ι} {Y : Type} (c : QueryCache spec)
        (leaf : ℕ → OracleComp spec Y) (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
        {z t : ℕ} {r : Y},
      simulateQ c.toPartialImpl (merkleRootM leaf nodeHash z t) = some r →
        ((2 ^ z : ℕ) : ENNReal) ≤ QueryCache.enncard c := by
  intro hbound
  have hsettled : simulateQ unitQueryCache.toPartialImpl
      (merkleRootM (fun _ => query (spec := Unit →ₒ Unit) ())
        (fun _ _ _ _ => query (spec := Unit →ₒ Unit) ()) 1 0) = some () := by
    simp only [merkleRootM]
    rfl
  have hle := (hbound unitQueryCache _ _ hsettled).trans_eq enncard_unitQueryCache
  norm_num at hle

end PerfectMerkleTree
