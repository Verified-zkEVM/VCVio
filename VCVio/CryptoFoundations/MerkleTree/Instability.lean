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
Extending the database by one fresh answer completes its cached authentication chain only when
the answer is one of the labels that extraction reaches from the root. A full binary skeleton with
`L` leaves has `2 * L - 1` nodes, so the flip probability into "the opening verifies" is at most
`(2 * L - 1) / |Y|`, for every query bound. Answers are uniform on the finite
label type `Y`.

This is the one-step form of `fresh_extractedTarget_of_extractor_disagreement`, with the commit
cache the database before the query and the final cache the database after it.

## Main definitions

* `MerkleTreeExtractability.LogRepresentsCache`: a query log whose entries are exactly the entries
  of a cache, in any order and with repetitions.
* `MerkleTreeExtractability.OpeningDisagrees`: an opening differs from the partial tree extracted
  from a log; a missing leaf or sibling counts as disagreement.
* `MerkleTreeExtractability.acceptingCaches`: caches already containing the complete authentication
  chain for the opening, without sampling any further answers.
* `MerkleTreeExtractability.nonExtractingCaches`: the finite collision-free caches whose extracted
  tree disagrees with the opening.

## Main statements

* `tree_eq_of_logRepresentsCache`: representing logs extract the same partial tree from a
  collision-free cache, regardless of order and repetitions.
* `openingDisagrees_iff_of_logRepresentsCache`: disagreement is independent of that log.
* `mem_nonExtractingCaches_iff_of_logRepresentsCache`: any fixed representing log characterizes
  membership in `nonExtractingCaches`.
* `not_openingDisagrees_of_chainInCache`: in one collision-free database, every authentication
  chain agrees with extraction, so `acceptingCaches` and `nonExtractingCaches` are disjoint.
* `answer_mem_extractedTargets_of_chainInCache_cacheQuery`: a fresh answer that completes a
  disagreeing chain is a label of the extracted tree.
* `flip_nonExtractingCaches_acceptingCaches_le`: the flip probability bound.

The query model projects each query to an address and an ordered left/right child pair. Its two
projection laws specify this interface; they do not assume an extraction conclusion. Address maps
need not be injective. Extraction keeps the claimed root even with an empty log, but descendants
may be `none`. The exceptional targets here are root-reachable labels, at most `2 * L - 1` in
number; paper half-preimages are child labels occurring in cached inputs.

## Scope

The opening `(leaf, proof)`, the position and the root are fixed before the supremum over
databases and fresh points is taken, and the target property does not require the extended
database to be collision-free. The statement is therefore a corollary of the deterministic
disagreement kernel for one fixed opening. It is related to the following results and does not
formalize any of them:

* CMS19 Lemma 6.5 (ePrint 2019/834, PDF p. 33) and CDHZ Lemma 8.6 (ePrint 2025/2166,
  PDF p. 55) give deterministic exceptional-set statements for a change of the extracted tree:
  under their respective hypotheses, the new answer must be the root or a half-preimage already
  present in the database. Sampling bounds then follow by measuring this set. CMS19 assumes both
  databases are collision-free. A change of tree need not complete the fixed opening, so it is
  not the event `acceptingCaches` studied here. Our extractor takes a log; the theorem
  `tree_eq_of_logRepresentsCache` makes its value independent of that log for a collision-free
  cache. This invariance need not hold on caches with collisions.
* [CMS19, Lemma 6.10] bounds the conditional instability of the Micali property given no
  collision. It involves the query that derives the verifier randomness from the root and the
  soundness of the underlying proof, neither of which appears here.

## References

* [CMS19] Alessandro Chiesa, Peter Manohar, Nicholas Spooner, *Succinct Arguments in the Quantum
  Random Oracle Model*, TCC 2019, [ePrint 2019/834](https://eprint.iacr.org/2019/834),
  January 14, 2020 revision: Lemma 6.5 (PDF p. 33), Lemma 6.10 (PDF p. 35).
* [CDHZ25] Alessandro Chiesa, Zijing Di, Zihan Hu, Yuxi Zheng, *How to Prove Post-Quantum
  Security for Succinct Non-Interactive Reductions*,
  [ePrint 2025/2166](https://eprint.iacr.org/2025/2166), March 2, 2026 revision:
  Lemma 8.6 (PDF p. 55).
-/

public section

namespace MerkleTreeExtractability

open ENNReal OracleSpec OracleComp BinaryTree InductiveMerkleTree

universe u

variable {Query Y : Type} {Address : Type u}

/-- The entries of the query log `log` are exactly the entries of `cache`: every logged pair is
cached, and every cached pair is logged. Order and repetitions are unrestricted. Such a log exists
only for a finite cache (`exists_logRepresentsCache_of_finite` gives the converse). -/
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

/-- Child lookup is independent of the log representing a collision-free cache. -/
private lemma children_eq_of_logRepresentsCache [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {log₁ log₂ : (Query →ₒ Y).QueryLog} {cache : (Query →ₒ Y).QueryCache}
    (h₁ : LogRepresentsCache log₁ cache) (h₂ : LogRepresentsCache log₂ cache)
    (hno : ¬CacheHasCollision cache) (address : Address) (root : Y) :
    MerkleTreeExtractor.children view log₁ address root =
      MerkleTreeExtractor.children view log₂ address root := by
  have hmem : ∀ entry, entry ∈ log₁ ↔ entry ∈ log₂ := by
    intro ⟨q, y⟩
    constructor
    · intro h
      obtain ⟨⟨q', y'⟩, h', rfl, rfl⟩ := h₂.2 q y (h₁.1 _ h)
      exact h'
    · intro h
      obtain ⟨⟨q', y'⟩, h', rfl, rfl⟩ := h₁.2 q y (h₂.1 _ h)
      exact h'
  cases hfind : log₁.find? (fun entry => view.address entry.1 == address && entry.2 == root) with
  | none =>
      have hfind₂ : log₂.find?
          (fun entry => view.address entry.1 == address && entry.2 == root) = none := by
        apply List.find?_eq_none.mpr
        intro entry hentry
        exact List.find?_eq_none.mp hfind entry ((hmem entry).mpr hentry)
      simp [MerkleTreeExtractor.children, hfind, hfind₂]
  | some entry =>
      have hpred := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hpred
      have hentry := (hmem entry).mp (List.mem_of_find?_eq_some hfind)
      have hchildren := MerkleTreeExtractor.children_eq_some_of_mem_of_responseInjectiveOn
        view log₂ address root entry.1 hpred.1
        (by simpa only [← hpred.2] using hentry)
        (responseInjectiveOn_of_cache_noCollision log₂ cache h₂.1 hno)
      simp only [MerkleTreeExtractor.children, hfind]
      exact hchildren.symm

/-- Logs representing the same collision-free cache extract the same partial labelled tree,
regardless of their order or repeated entries. -/
theorem tree_eq_of_logRepresentsCache [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {log₁ log₂ : (Query →ₒ Y).QueryLog} {cache : (Query →ₒ Y).QueryCache}
    (h₁ : LogRepresentsCache log₁ cache) (h₂ : LogRepresentsCache log₂ cache)
    (hno : ¬CacheHasCollision cache) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address) (root : Y) :
    MerkleTreeExtractor.tree view s addressKey log₁ root =
      MerkleTreeExtractor.tree view s addressKey log₂ root := by
  induction s generalizing root with
  | leaf => rfl
  | internal left right ihLeft ihRight =>
      simp only [MerkleTreeExtractor.tree, MerkleTreeExtractor.treeAt, MerkleTreeExtractor.treeWith]
      rw [children_eq_of_logRepresentsCache view h₁ h₂ hno]
      cases MerkleTreeExtractor.children view log₂ (addressKey .ofInternal) root with
      | none => rfl
      | some pair =>
          obtain ⟨leftRoot, rightRoot⟩ := pair
          exact congrArg₂ (FullData.internal (some root))
            (ihLeft _ leftRoot) (ihRight _ rightRoot)

section extraction

variable [DecidableEq Address] [DecidableEq Y] (model : NodeQueryModel Query Address Y)
  {s : Skeleton} (addressKey : SkeletonInternalIndex s → Address)

/-- The fixed opening `(leaf, proof)` disagrees with the partial tree extracted from `log` at
`root`: either its leaf is not `some leaf`, or its sibling path is not `proof.map some`.

Extracted labels lie in `Option Y`. A missing leaf or sibling therefore counts as disagreement,
as does a different known label. `openingDisagrees_iff_of_logRepresentsCache` makes this predicate
independent of the representing log when the cache is collision-free. -/
@[expose] def OpeningDisagrees (log : (Query →ₒ Y).QueryLog) (leaf root : Y)
    (idx : SkeletonLeafIndex s) (proof : List.Vector Y idx.depth) : Prop :=
  some leaf ≠ (MerkleTreeExtractor.tree model.view s addressKey log root).get idx.toNodeIndex ∨
    proof.toList.map some ≠
      (generateProof (MerkleTreeExtractor.tree model.view s addressKey log root) idx).toList

/-- The caches containing the complete authentication chain for the fixed opening
`(leaf, proof)` at `idx` and `root`, using `model` and `addressKey`.

Every hash response needed by this chain is already stored in the cache. This is the predicate
`ChainInCache`, not an execution that samples additional answers. Collision-freedom and
finiteness of the whole cache are not required. -/
@[expose] def acceptingCaches (leaf root : Y) (idx : SkeletonLeafIndex s)
    (proof : List.Vector Y idx.depth) : Set (Query →ₒ Y).QueryCache :=
  {cache | ChainInCache model addressKey cache leaf root idx proof}

/-- The finite collision-free caches that have a representing log whose extracted tree, at the
fixed `root` and position `idx`, does not open to `(leaf, proof)`. A missing leaf or sibling in the
extracted tree counts as disagreement. The log is an existential witness; extraction from a
collision-free cache is independent of the representing log
(`tree_eq_of_logRepresentsCache`). -/
@[expose] def nonExtractingCaches (leaf root : Y) (idx : SkeletonLeafIndex s)
    (proof : List.Vector Y idx.depth) : Set (Query →ₒ Y).QueryCache :=
  {cache | ¬CacheHasCollision cache ∧
    ∃ log, LogRepresentsCache log cache ∧ OpeningDisagrees model addressKey log leaf root idx proof}

variable {model addressKey} {log : (Query →ₒ Y).QueryLog} {cache : (Query →ₒ Y).QueryCache}
  {leaf root : Y} {idx : SkeletonLeafIndex s} {proof : List.Vector Y idx.depth}

/-- Opening disagreement is independent of the log representing a collision-free cache. -/
theorem openingDisagrees_iff_of_logRepresentsCache {log' : (Query →ₒ Y).QueryLog}
    (hlog : LogRepresentsCache log cache) (hlog' : LogRepresentsCache log' cache)
    (hno : ¬CacheHasCollision cache) :
    OpeningDisagrees model addressKey log leaf root idx proof ↔
      OpeningDisagrees model addressKey log' leaf root idx proof := by
  unfold OpeningDisagrees
  rw [tree_eq_of_logRepresentsCache model.view hlog hlog' hno]

/-- Any representing log can witness failure to extract from a collision-free cache. -/
theorem mem_nonExtractingCaches_iff_of_logRepresentsCache
    (hlog : LogRepresentsCache log cache) :
    cache ∈ nonExtractingCaches model addressKey leaf root idx proof ↔
      ¬CacheHasCollision cache ∧ OpeningDisagrees model addressKey log leaf root idx proof := by
  constructor
  · rintro ⟨hno, log', hlog', hdisagree⟩
    exact ⟨hno, (openingDisagrees_iff_of_logRepresentsCache hlog' hlog hno).mp hdisagree⟩
  · rintro ⟨hno, hdisagree⟩
    exact ⟨hno, log, hlog, hdisagree⟩

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
theorem updateProb_acceptingCaches_le (hlog : LogRepresentsCache log cache)
    (hno : ¬CacheHasCollision cache)
    (hdisagree : OpeningDisagrees model addressKey log leaf root idx proof)
    {x : Query} (hx : cache x = none) :
    cache.updateProb x (acceptingCaches model addressKey leaf root idx proof) ≤
      ((2 * s.leafCount - 1 : ℕ) : ℝ≥0∞) / Fintype.card Y := by
  classical
  rw [QueryCache.updateProb_eq_card_div]
  refine ENNReal.div_le_div_right ?_ _
  have hsub : (Finset.univ.filter fun u : Y =>
      cache.cacheQuery x u ∈ acceptingCaches model addressKey leaf root idx proof) ⊆
      (extractedTargets model s addressKey log root).toFinset := fun u hu =>
    List.mem_toFinset.mpr (answer_mem_extractedTargets_of_chainInCache_cacheQuery hlog hno
      hdisagree hx (Finset.mem_filter.mp hu).2)
  exact_mod_cast (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans
    (MerkleTreeExtractor.targets_length_le model.view s addressKey log root))

/-- Fix the skeleton, the root, the position and the opening `(leaf, proof)`. With uniform answers
in the finite type `Y`, the flip probability from `nonExtractingCaches` to `acceptingCaches` is at
most `(2 * s.leafCount - 1) / |Y|`, for every query bound `t`.

A fresh answer completes the authentication chain only if it equals one of the at most
`2 * s.leafCount - 1` labels that extraction reaches from the root before the update. The extended
cache need not be collision-free. This is a bound for one fixed opening, not for a change of the
extracted tree; see the module's Scope section. -/
theorem flip_nonExtractingCaches_acceptingCaches_le (t : ℕ) :
    QueryCache.flip (nonExtractingCaches model addressKey leaf root idx proof)
        (acceptingCaches model addressKey leaf root idx proof) t ≤
      ((2 * s.leafCount - 1 : ℕ) : ℝ≥0∞) / Fintype.card Y :=
  QueryCache.flip_le_iff.mpr fun _ ⟨hno, _, hlog, hdisagree⟩ _ _ hx =>
    updateProb_acceptingCaches_le hlog hno hdisagree hx

end extraction

end MerkleTreeExtractability
