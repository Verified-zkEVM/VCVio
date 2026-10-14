/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.ExtractionKernel
public import VCVio.OracleComp.QueryTracking.Instability.Basic

/-!
# One-step Merkle extraction instability

Fix a Merkle opening `(leaf, proof)` at a leaf position `idx` for a claimed root. Take a
collision-free database whose extracted tree at that root does not open `idx` to `(leaf, proof)`.
Extending the database by one fresh answer makes the opening verify only when the answer is one
of the labels that extraction reaches from the root. A full binary skeleton with `L` leaves has
`2 * L - 1` nodes, so the flip probability into "the opening verifies" is at most
`(2 * L - 1) / |Y|`, for every query bound.

This is the one-step form of `fresh_extractedTarget_of_extractor_disagreement`, with the commit
cache the database before the query and the final cache the database after it.

## Main definitions

* `MerkleTreeExtractability.LogRepresentsCache`: a query log lists exactly the entries of a cache.
* `MerkleTreeExtractability.OpeningDisagrees`: an opening differs from the one read off the tree
  that extraction reconstructs from a log.
* `MerkleTreeExtractability.acceptingCaches`: the databases that contain an authentication chain
  for the opening.
* `MerkleTreeExtractability.nonExtractingCaches`: the collision-free databases whose extracted
  tree disagrees with the opening.

## Main statements

* `not_openingDisagrees_of_chainInCache`: in one collision-free database, every authentication
  chain agrees with extraction, so `acceptingCaches` and `nonExtractingCaches` are disjoint.
* `answer_mem_extractedTargets_of_chainInCache_cacheQuery`: a fresh answer that completes a
  disagreeing chain is a label of the extracted tree.
* `flip_nonExtractingCaches_acceptingCaches_le`: the flip probability bound.

## Scope

The opening `(leaf, proof)`, the position and the root are fixed before the supremum over
databases and fresh points is taken, and the target property does not require the extended
database to be collision-free. The statement is therefore a corollary of the deterministic
disagreement kernel for one fixed opening. It is related to the following results and does not
formalize any of them:

* [CMS19, Lemma 6.5] and [CDHZ25, Lemma 8.6] bound the probability that one fresh answer changes
  the *extracted tree*, through the exceptional set of the root and the half-preimages of the
  database. A fresh answer can change the extracted tree without completing the fixed opening, so
  that event is not contained in `acceptingCaches`. Those lemmas also need an extractor that is a
  function of the database; `MerkleTreeExtractor.tree` takes a log, and on a database with a
  collision its output depends on the order of the log.
* [CMS19, Lemma 6.10] bounds the conditional instability of the Micali property given no
  collision. It involves the query that derives the verifier randomness from the root and the
  soundness of the underlying proof, neither of which appears here.

## References

* [CMS19] Alessandro Chiesa, Peter Manohar, Nicholas Spooner, *Succinct Arguments in the Quantum
  Random Oracle Model*, TCC 2019.
* [CDHZ25] Alessandro Chiesa, Zijing Di, Zihan Hu, Yuxi Zheng, *How to Prove Post-Quantum
  Security for Succinct Non-Interactive Reductions*, 2026.
-/

public section

namespace MerkleTreeExtractability

open ENNReal OracleSpec OracleComp BinaryTree InductiveMerkleTree

universe u

variable {Query Y : Type} {Address : Type u}

/-- The query log `log` lists exactly the entries of the cache `cache`. -/
@[expose] def LogRepresentsCache (log : (Query →ₒ Y).QueryLog)
    (cache : (Query →ₒ Y).QueryCache) : Prop :=
  (∀ entry ∈ log, cache entry.1 = some entry.2) ∧
    ∀ input value, cache input = some value → ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value

/-- Every cache with finitely many entries is represented by some query log. -/
lemma exists_logRepresentsCache_of_finite {cache : (Query →ₒ Y).QueryCache}
    (h : cache.toSet.Finite) : ∃ log, LogRepresentsCache log cache :=
  ⟨h.toFinset.toList,
    fun ⟨_, _⟩ hentry => h.mem_toFinset.mp (Finset.mem_toList.mp hentry),
    fun input value hvalue =>
      ⟨⟨input, value⟩, Finset.mem_toList.mpr (h.mem_toFinset.mpr hvalue), rfl, rfl⟩⟩

section extraction

variable [DecidableEq Address] [DecidableEq Y] (model : NodeQueryModel Query Address Y)
  {s : Skeleton} (addressKey : SkeletonInternalIndex s → Address)

/-- The opening `(leaf, proof)` at position `idx` differs, in its leaf or in its authentication
path, from the opening read off the tree that extraction reconstructs from `log` at `root`. -/
@[expose] def OpeningDisagrees (log : (Query →ₒ Y).QueryLog) (leaf root : Y)
    (idx : SkeletonLeafIndex s) (proof : List.Vector Y idx.depth) : Prop :=
  some leaf ≠ (MerkleTreeExtractor.tree model.view s addressKey log root).get idx.toNodeIndex ∨
    proof.toList.map some ≠
      (generateProof (MerkleTreeExtractor.tree model.view s addressKey log root) idx).toList

/-- The databases that contain an authentication chain from `leaf` to `root` along `proof`. -/
@[expose] def acceptingCaches (leaf root : Y) (idx : SkeletonLeafIndex s)
    (proof : List.Vector Y idx.depth) : Set (Query →ₒ Y).QueryCache :=
  {cache | ChainInCache model addressKey cache leaf root idx proof}

/-- The collision-free databases represented by a log whose extracted tree at `root` disagrees
with the opening `(leaf, proof)` at `idx`. -/
@[expose] def nonExtractingCaches (leaf root : Y) (idx : SkeletonLeafIndex s)
    (proof : List.Vector Y idx.depth) : Set (Query →ₒ Y).QueryCache :=
  {cache | ¬CacheHasCollision cache ∧
    ∃ log, LogRepresentsCache log cache ∧ OpeningDisagrees model addressKey log leaf root idx proof}

variable {model addressKey} {log : (Query →ₒ Y).QueryLog} {cache : (Query →ₒ Y).QueryCache}
  {leaf root : Y} {idx : SkeletonLeafIndex s} {proof : List.Vector Y idx.depth}

/-- In one collision-free database, every authentication chain agrees with the tree that
extraction reconstructs from that database. -/
theorem not_openingDisagrees_of_chainInCache (hlog : LogRepresentsCache log cache)
    (hno : ¬CacheHasCollision cache)
    (hchain : ChainInCache model addressKey cache leaf root idx proof) :
    ¬OpeningDisagrees model addressKey log leaf root idx proof := by
  intro hdisagree
  obtain ⟨_, _, _, hsome, hnone⟩ := fresh_extractedTarget_of_extractor_disagreement model
    addressKey idx log cache cache root leaf proof hlog.1 hlog.2 hno le_rfl hchain hdisagree
  exact Option.some_ne_none _ (hsome.symm.trans hnone)

/-- No database both accepts an opening and fails to extract it. -/
theorem disjoint_nonExtractingCaches_acceptingCaches :
    Disjoint (nonExtractingCaches model addressKey leaf root idx proof)
      (acceptingCaches model addressKey leaf root idx proof) :=
  Set.disjoint_left.mpr fun _ ⟨hno, _, hlog, hdisagree⟩ hchain =>
    not_openingDisagrees_of_chainInCache hlog hno hchain hdisagree

variable [DecidableEq Query]

/-- If extending a collision-free database at a fresh point `x` by the answer `u` completes an
authentication chain that disagrees with the tree extracted before the extension, then `u` is a
label of that extracted tree. -/
theorem answer_mem_extractedTargets_of_chainInCache_cacheQuery
    (hlog : LogRepresentsCache log cache) (hno : ¬CacheHasCollision cache)
    (hdisagree : OpeningDisagrees model addressKey log leaf root idx proof)
    {x : Query} (hx : cache x = none) {u : Y}
    (hchain : ChainInCache model addressKey (cache.cacheQuery x u) leaf root idx proof) :
    u ∈ extractedTargets model s addressKey log root := by
  obtain ⟨target, htarget, input, hsome, hnone⟩ :=
    fresh_extractedTarget_of_extractor_disagreement model addressKey idx log cache
      (cache.cacheQuery x u) root leaf proof hlog.1 hlog.2 hno (cache.le_cacheQuery hx) hchain
      hdisagree
  by_cases hinput : input = x
  · subst hinput
    rw [QueryCache.cacheQuery_self] at hsome
    exact Option.some.inj hsome ▸ htarget
  · rw [QueryCache.cacheQuery_of_ne _ _ hinput, hnone] at hsome
    exact (Option.some_ne_none _ hsome.symm).elim

variable [Fintype Y] [UniformAnswerMeasure (Query →ₒ Y)]

/-- Extending a collision-free database whose extracted tree disagrees with an opening, at a
fresh point and by a uniform answer, makes the opening verify with probability at most
`(2 * s.leafCount - 1) / |Y|`. -/
theorem extendProb_acceptingCaches_le (hlog : LogRepresentsCache log cache)
    (hno : ¬CacheHasCollision cache)
    (hdisagree : OpeningDisagrees model addressKey log leaf root idx proof)
    {x : Query} (hx : cache x = none) :
    cache.extendProb x (acceptingCaches model addressKey leaf root idx proof) ≤
      ((2 * s.leafCount - 1 : ℕ) : ℝ≥0∞) / Fintype.card Y := by
  classical
  rw [QueryCache.extendProb_eq_card_div]
  refine ENNReal.div_le_div_right ?_ _
  have hsub : (Finset.univ.filter fun u : Y =>
      cache.cacheQuery x u ∈ acceptingCaches model addressKey leaf root idx proof) ⊆
      (extractedTargets model s addressKey log root).toFinset := fun u hu =>
    List.mem_toFinset.mpr (answer_mem_extractedTargets_of_chainInCache_cacheQuery hlog hno
      hdisagree hx (Finset.mem_filter.mp hu).2)
  exact_mod_cast (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans
    (MerkleTreeExtractor.targets_length_le model.view s addressKey log root))

/-- The flip probability from the collision-free databases whose extracted tree disagrees with an
opening to the databases in which that opening verifies is at most `(2 * s.leafCount - 1) / |Y|`,
for every query bound. -/
theorem flip_nonExtractingCaches_acceptingCaches_le (t : ℕ) :
    QueryCache.flip (nonExtractingCaches model addressKey leaf root idx proof)
        (acceptingCaches model addressKey leaf root idx proof) t ≤
      ((2 * s.leafCount - 1 : ℕ) : ℝ≥0∞) / Fintype.card Y :=
  QueryCache.flip_le_iff.mpr fun _ ⟨hno, _, hlog, hdisagree⟩ _ _ hx =>
    extendProb_acceptingCaches_le hlog hno hdisagree hx

end extraction

end MerkleTreeExtractability
