/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.QueryBound
public import VCVio.OracleComp.QueryTracking.Unpredictability
public import ToMathlib.Data.IndexedBinaryTree.Lemmas

/-!
# Inductive Merkle Tree Extractability

This file develops the deterministic extraction kernel for the inductive Merkle tree
commitment scheme and its random-oracle experiment. The extractor reconstructs a partial
tree from the committing adversary's query log and the opened root. The experiment runs
the committing, opening, and verification phases against one shared lazy random function.

## Main definitions

We make several definitions to set up and analyze the extractability game
under namespace `InductiveMerkleTree`:

* `Adversary`: a two-phase Merkle tree adversary, bundling an auxiliary state type, a
  committing phase producing a claimed root and state, and an opening phase producing a
  (leaf index, leaf value, authentication path) triple from that state.
* `extractor`: builds a `FullData (Option α) s` from a query log, root, and skeleton by
  walking down from the root and pulling each node's children from the unique log entry
  whose response matches.
* `extractabilityInner`: the oracle syntax running an `Adversary` against the extractor
  and verifier, before choosing random-oracle semantics.
* `extractabilityGame`: the random-oracle experiment obtained by interpreting
  `extractabilityInner` through one shared `cachingOracle` from the empty cache.
* `ChainInLog`: structural predicate witnessing that a query log contains the hash chain
  from `root` down to `leaf` along the path determined by `idx`.

## Current proof boundary

This file proves the deterministic extraction and collision lemmas and a total-query bound
for the shared-cache experiment. It deliberately does not state a probabilistic extractability
bound yet. Such a theorem must separately bound fresh post-commit oracle answers that hit one
of the non-dummy labels in the commit-time partial tree; treating the verifier's last hash as
an independent fresh query is invalid under shared random-function semantics.

## TODO

- The lemmas here all specialize to `(m := OracleComp (spec α))` because the proofs rely
  on `OracleComp`-specific machinery — `withQueryLog`, `simulateQ` support lemmas, and the
  `ChainInLog log` predicate over a concrete `QueryLog`. Generalizing them to an arbitrary
  monad `m` (so they apply to e.g. `SimulateQ` without re-proving) would first require a
  generic "computation-with-query-log" interface at the framework level,
  but might be good at some point.

## References

* [Building Cryptographic Proofs from Hash Functions by Chiesa and Yogev](https://snargsbook.org/), Lemma 18.5.1.

-/

@[expose] public section

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type}

/-! ## Adversary -/

section Adversary

/-- An adversary in the Merkle tree extractability game, packaged as a single
two-phase object: a committing phase that produces a claimed root together with
auxiliary state, and an opening phase that consumes the auxiliary state to
produce a (leaf index, leaf value, authentication path) triple. -/
structure Adversary (α : Type) (s : Skeleton) where
  /-- Auxiliary state carried from the committing phase to the opening phase. -/
  AuxState : Type
  /-- Committing phase: produce a claimed root and auxiliary state. -/
  commit : OracleComp (spec α) (α × AuxState)
  /-- Opening phase: given the auxiliary state, produce a leaf index, claimed
  leaf value, and authentication path. -/
  opening : AuxState → OracleComp (spec α)
      ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth)

/-- The combined two-phase execution of `𝒜` has total query bound `qb`. -/
def Adversary.IsTwoPhaseTotalQueryBound {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ) : Prop :=
  IsTotalQueryBound
    (do
      let (_root, aux) ← 𝒜.commit
      let ⟨_idx, _leaf, _proof⟩ ← 𝒜.opening aux
      pure ())
    qb

end Adversary

/-! ## Extractability game -/

section ExtractabilityGame

variable [DecidableEq α]

/--
The child-decomposition function used by the Merkle-tree `extractor`. Given a `cache`
and a node value `a`, look up the first query in `cache` whose response is `a` and return
its input pair; if no such entry exists, return `none`.
-/
def extractorChildren (cache : (spec α).QueryLog) (a : α) : Option (α × α) :=
  match cache.find? (fun ⟨_, r⟩ => r == a) with
  | none => none
  | some ⟨(x, y), _⟩ => some (x, y)

/--
The extraction algorithm for Merkle trees: from a query log `cache`, a `root`, and a
skeleton `s`, build a partial tree of type `FullData (Option α) s` by walking down from
`root`. A node with value `some a` looks up the unique log entry whose response is `a`
and uses its input pair as the children's values; in every other case (no matching entry,
or the parent is already `none`) both children are `none`. Implemented as
`optionPopulateDown` driven by `extractorChildren`.
-/
def extractor (s : Skeleton) (cache : (spec α).QueryLog) (root : α) : FullData (Option α) s :=
  optionPopulateDown s (extractorChildren cache) root

/-- Values fixed by the commit transcript that can occur as non-dummy labels in the
extracted tree: the claimed root and both inputs of every commit-phase hash query.
Duplicates are retained so that the size bound is definitionally tied to the query log. -/
private def commitTargets (root : α) (log : (spec α).QueryLog) : List α :=
  root :: log.flatMap fun entry => [entry.1.1, entry.1.2]

omit [DecidableEq α] in
@[simp]
private lemma commitTargets_length (root : α) (log : (spec α).QueryLog) :
    (commitTargets root log).length = 2 * log.length + 1 := by
  simp [commitTargets, Nat.mul_comm]

omit [DecidableEq α] in
private lemma commitTargets_mono_root {root root' : α} {log : (spec α).QueryLog}
    (hroot' : root' ∈ log.flatMap fun entry => [entry.1.1, entry.1.2]) :
    ∀ {target : α}, target ∈ commitTargets root' log → target ∈ commitTargets root log := by
  intro target htarget
  simp only [commitTargets, List.mem_cons] at htarget ⊢
  exact htarget.elim (fun h => Or.inr (h ▸ hroot')) Or.inr

/--
The oracle syntax underlying the extractability experiment. It runs the committing
adversary, snapshots that phase's query log for the extractor, runs the opening adversary,
and finally verifies the opening. Random-function consistency is supplied separately by
`extractabilityGame`.
-/
def extractabilityInner {s : Skeleton} (𝒜 : Adversary α s) :
    OracleComp (spec α) (α × 𝒜.AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) :=
  do
    let ((root, aux), queryLog) ← 𝒜.commit.withQueryLog
    let extractedTree := extractor s queryLog root
    let ⟨idx, leaf, proof⟩ ← 𝒜.opening aux
    let extractedProof := generateProof extractedTree idx
    let verified ← verifyProof idx leaf root proof
    return (root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩)

/-- The opening-and-verification suffix after fixing a logged commit outcome. This is the
actual cached continuation used in the ROM proof; it does not resample or reset the oracle. -/
private def extractabilityRest {s : Skeleton} (𝒜 : Adversary α s)
    (root : α) (aux : 𝒜.AuxState) (queryLog : (spec α).QueryLog) :
    OracleComp (spec α) (α × 𝒜.AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) :=
  do
    let extractedTree := extractor s queryLog root
    let ⟨idx, leaf, proof⟩ ← 𝒜.opening aux
    let extractedProof := generateProof extractedTree idx
    let verified ← verifyProof idx leaf root proof
    return (root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩)

private lemma extractabilityInner_eq_commit_bind_rest {s : Skeleton} (𝒜 : Adversary α s) :
    extractabilityInner 𝒜 =
      𝒜.commit.withQueryLog >>= fun x => extractabilityRest 𝒜 x.1.1 x.1.2 x.2 := by
  simp [extractabilityInner, extractabilityRest]

/--
The extraction-failure event on an `extractabilityInner` transcript: verification passes
but the extracted leaf or authentication proof does not match the adversary's opening. This
is the single-leaf specialization of Merkle extractability, and compares the full authentication
path at that leaf.
-/
def AdversaryWinsExtractabilityInner {s : Skeleton} {AuxState : Type} :
    α × AuxState ×
      ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
       FullData (Option α) s × List.Vector (Option α) idx.depth × Bool) → Prop
  | (_, _, ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩) =>
    verified = true ∧
      (some leaf ≠ extractedTree.get idx.toNodeIndex ∨
        proof.toList.map some ≠ extractedProof.toList)

/-- The Merkle-tree extractability experiment in the random-oracle model. All queries made
by the committing adversary, opening adversary, and verifier are interpreted through one
shared cache, so repeated equal inputs receive the same answer. -/
def extractabilityGame {s : Skeleton} (𝒜 : Adversary α s) :
    OracleComp (spec α) (α × 𝒜.AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) :=
  (spec α).withCacheOverlay ∅ (extractabilityInner 𝒜)

/-- The extraction-failure event for `extractabilityGame`. -/
def AdversaryWinsExtractabilityGame {s : Skeleton} {AuxState : Type} :
    α × AuxState ×
      ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
       FullData (Option α) s × List.Vector (Option α) idx.depth × Bool) → Prop :=
  AdversaryWinsExtractabilityInner

/-- If the query log's first entry with response `root` is the pair `⟨(x, y), root⟩`,
then the extractor at an internal skeleton unfolds to that node's two children using
`x` and `y` as the new "ancestor" values for the left and right subtrees. -/
private lemma extractor_internal_eq_of_find?_eq
    (sl sr : Skeleton) (log : (spec α).QueryLog) (root x y : α)
    (h_find : log.find? (fun ⟨_, r⟩ => r == root) = some ⟨(x, y), root⟩) :
    extractor (Skeleton.internal sl sr) log root =
      FullData.internal (some root) (extractor sl log x) (extractor sr log y) := by
  simp only [extractor, optionPopulateDown_internal, extractorChildren, h_find]
  rfl

/--
Unfold `extractabilityInner` into a nested `bind` whose outer prefix logs the committing
adversary's queries alongside the opening adversary's output, and whose continuation runs
`verifyProof` and assembles the transcript. This is the definitional rearrangement used to
expose the prefix as a target for query-bound reasoning.
-/
private lemma extractabilityInner_eq_bind_verifyProof
    {s : Skeleton} (𝒜 : Adversary α s) :
    extractabilityInner 𝒜 =
      (𝒜.commit.withQueryLog >>= fun ((root, aux), queryLog) =>
        𝒜.opening aux >>= fun q => pure (((root, aux), queryLog), q)) >>=
      fun (⟨⟨root, aux⟩, queryLog⟩, ⟨idx, leaf, proof⟩) =>
        verifyProof idx leaf root proof >>= fun verified =>
          pure (root, aux,
                ⟨idx, leaf, proof,
                 extractor s queryLog root,
                 generateProof (extractor s queryLog root) idx,
                 verified⟩) := by
  simp only [extractabilityInner, bind_assoc, pure_bind]

omit [DecidableEq α] in
/--
Project the logged-prefix of `extractabilityInner` onto `Unit`: discarding both the
committed root/aux and the query log of the committing adversary recovers the plain
measurement used to express the combined query bound.
-/
private lemma extractabilityInner_logged_prefix_map_unit_eq
    {s : Skeleton} (𝒜 : Adversary α s) :
    (fun _ => ()) <$>
        (𝒜.commit.withQueryLog >>= fun ((root, aux), queryLog) =>
          𝒜.opening aux >>= fun q => pure (((root, aux), queryLog), q)) =
      (do let (_root, aux) ← 𝒜.commit
          let ⟨_idx, _leaf, _proof⟩ ← 𝒜.opening aux
          pure ()) := by
  change ((fun _ => ()) <$> ((simulateQ loggingOracle 𝒜.commit).run >>= fun x =>
    𝒜.opening x.1.2 >>= fun q => pure ((x.1, x.2), q))) = _
  simpa [map_bind, map_pure] using
    loggingOracle.run_simulateQ_bind_fst 𝒜.commit
    (fun (_, aux) => 𝒜.opening aux >>= fun _ => pure ())

/--
If the adversary `𝒜` has two-phase total query bound `qb`, then the full extractability
game has total query bound `qb + s.depth`.

The extra `s.depth` accounts for the `verifyProof` step, which traverses the path from the
queried leaf to the root, making at most `s.depth` oracle queries.
-/
theorem extractabilityInner_isTotalQueryBound {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    IsTotalQueryBound (extractabilityInner 𝒜) (qb + s.depth) := by
  rw [extractabilityInner_eq_bind_verifyProof]
  exact isTotalQueryBound_bind (n₁ := qb) (n₂ := s.depth)
    ((isQueryBound_iff_of_map_eq (extractabilityInner_logged_prefix_map_unit_eq 𝒜)
      (fun _ b => 0 < b) (fun _ b => b - 1)).mpr h)
    fun (⟨⟨root, _aux⟩, _queryLog⟩, ⟨idx, leaf, proof⟩) =>
      isTotalQueryBound_bind (n₁ := s.depth) (n₂ := 0)
        (verifyProof_isTotalQueryBound_skeleton_depth idx leaf root proof) fun _ => trivial

/-- The shared-cache random-oracle experiment makes at most as many underlying fresh
queries as `extractabilityInner`. Cache hits skip the underlying query, so the implication
is intentionally one-way. -/
theorem extractabilityGame_isTotalQueryBound [IsUniformSpec (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    IsTotalQueryBound (extractabilityGame 𝒜) (qb + s.depth) := by
  apply (isQueryBound_map_iff _ _ (qb + s.depth) _ _).mpr
  exact IsTotalQueryBound.simulateQ_run_withCaching _
    (extractabilityInner_isTotalQueryBound 𝒜 qb h)
    (fun t => (isQueryBound_query_iff t 1 _ _).mpr Nat.one_pos) ∅

private lemma extractorChildren_eq_none_of_find?_eq_none
    {log_c : (spec α).QueryLog} {a : α} (hf : log_c.find? (fun ⟨_, r⟩ => r == a) = none) :
    extractorChildren log_c a = none := by
  simp only [extractorChildren, hf]

/--
If a particular transcript is in the support of the extractability game with the query log,
then the log has subsets `log_c` (containing the committing adversary's queries)
and `log_v` (containing the verifier's queries),
such that the proof verification step passes emitting `log_v`,
and the extractor and proof generation steps `log_c`
yield the same extracted tree and proof as the transcript.
-/
private lemma extractabilityInner_support_decompose
    {s : Skeleton} (𝒜 : Adversary α s) {root : α} {aux : 𝒜.AuxState} {idx : SkeletonLeafIndex s}
    {leaf : α} {proof : List.Vector α idx.depth} {extractedTree : FullData (Option α) s}
    {extractedProof : List.Vector (Option α) idx.depth} {log : (spec α).QueryLog}
    (hsup : ((root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, true⟩),
                  log) ∈
      support (extractabilityInner 𝒜).withQueryLog) :
    ∃ log_c log_v : (spec α).QueryLog,
      (true, log_v) ∈ support
          (verifyProof (m := OracleComp (spec α)) idx leaf root proof).withQueryLog ∧
      (∀ q, q ∈ log_v → q ∈ log) ∧
      (∀ q, q ∈ log_c → q ∈ log) ∧
      extractedTree = extractor s log_c root ∧
      extractedProof = generateProof (extractor s log_c root) idx := by
  unfold extractabilityInner at hsup
  simp only [OracleComp.withQueryLog_bind, mem_support_bind_iff, support_map,
    Set.mem_image] at hsup
  obtain ⟨⟨⟨root_c, aux_c⟩, log_c⟩, h_c, ⟨_, _⟩,
    ⟨⟨⟨idx_o, leaf_o, proof_o⟩, _⟩, _, ⟨_, _⟩,
      ⟨⟨_, log_v⟩, h_vp, ⟨_, _⟩, h_p, h_eq_p⟩, h_eq_v⟩, h_eq_co⟩ := hsup
  rw [OracleComp.withQueryLog_pure, mem_support_pure_iff, Prod.mk.injEq] at h_p
  obtain ⟨h_p1, rfl⟩ := h_p
  simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h_eq_co h_eq_v h_eq_p
  obtain ⟨h_eq_co1, h_eq_co2⟩ := h_eq_co
  obtain ⟨h_eq_v1, h_eq_v2⟩ := h_eq_v
  obtain ⟨h_eq_p1, h_eq_p2⟩ := h_eq_p
  rw [← h_eq_v1, ← h_eq_p1, h_p1] at h_eq_co1
  simp only [Prod.mk.injEq] at h_eq_co1
  obtain ⟨rfl, rfl, h_sigma_eq⟩ := h_eq_co1
  obtain ⟨rfl, h_rest_eq⟩ := Sigma.mk.inj h_sigma_eq
  simp only [heq_eq_eq, Prod.mk.injEq] at h_rest_eq
  obtain ⟨rfl, rfl, h_tree_eq, h_proof_ext_eq, rfl⟩ := h_rest_eq
  rw [OracleComp.withQueryLog_self_log_eq 𝒜.commit h_c] at h_tree_eq h_proof_ext_eq
  refine ⟨log_c, log_v, h_vp, fun q hq => ?_, fun q hq => ?_,
    h_tree_eq.symm, h_proof_ext_eq.symm⟩ <;>
    rw [← h_eq_co2, ← h_eq_v2, ← h_eq_p2] <;>
    grind [List.mem_append_right, List.mem_append_left]

/--
If `root` is not the response of any query in `log`,
then the extractor at an internal skeleton is `none`.
-/
private lemma extractor_internal_get_eq_none_of_find?_eq_none
    (sl sr : Skeleton) (log : (spec α).QueryLog) (root : α)
    (idx : SkeletonNodeIndex sl ⊕ SkeletonNodeIndex sr)
    (hf : log.find? (fun ⟨_, r⟩ => r == root) = none) :
    (extractor (Skeleton.internal sl sr) log root).get
        (idx.elim SkeletonNodeIndex.ofLeft SkeletonNodeIndex.ofRight) = none := by
  simp only [extractor, optionPopulateDown_internal, extractorChildren_eq_none_of_find?_eq_none hf]
  cases idx <;>
    exact populateDown_none_get_eq_none (Option.bindPair (extractorChildren log)) rfl _

end ExtractabilityGame

private lemma singleHash_withQueryLog (a b : α) :
    (singleHash (m := OracleComp (spec α)) a b).withQueryLog =
      (liftM ((spec α).query (a, b)) : OracleComp (spec α) α) >>=
        fun u => pure (u, ([⟨(a, b), u⟩] : (spec α).QueryLog)) := by
  simp [singleHash, OracleComp.withQueryLog_query]

private lemma getPutativeRoot_step_withQueryLog_decompose
    (prog : OracleComp (spec α) α) (mkPair : α → α × α)
    (r : α) (log_v : (spec α).QueryLog)
    (hmem : (r, log_v) ∈ support
      (prog >>= fun a => let (l, r') := mkPair a; singleHash l r').withQueryLog) :
    ∃ a log_a, (a, log_a) ∈ support prog.withQueryLog
      ∧ log_v = log_a ++ [⟨mkPair a, r⟩] := by
  simp only [OracleComp.withQueryLog_bind, singleHash_withQueryLog] at hmem
  grind

/--
Predicate stating that `log` contains a hash chain from `leaf` (combined with the
sibling values in `proof`) up to `root` along the path determined by `idx`.
-/
def ChainInLog {s : Skeleton} (log : (spec α).QueryLog) (leaf root : α) :
    (idx : SkeletonLeafIndex s) → List.Vector α idx.depth → Prop
  | .ofLeaf, _ => leaf = root
  | .ofLeft idxLeft, proof =>
      ∃ ancestor : α,
        (⟨(ancestor, proof.head), root⟩ : (_i : (α × α)) × α) ∈ log ∧
        ChainInLog log leaf ancestor idxLeft proof.tail
  | .ofRight idxRight, proof =>
      ∃ ancestor : α,
        (⟨(proof.head, ancestor), root⟩ : (_i : (α × α)) × α) ∈ log ∧
        ChainInLog log leaf ancestor idxRight proof.tail

/-- A hash chain interpreted in a shared random-oracle cache. Unlike `ChainInLog`,
this predicate records only the final function graph and therefore identifies cache hits
and cache misses with the same response. -/
private def ChainInCache {s : Skeleton} (cache : (spec α).QueryCache) (leaf root : α) :
    (idx : SkeletonLeafIndex s) → List.Vector α idx.depth → Prop
  | .ofLeaf, _ => leaf = root
  | .ofLeft idxLeft, proof =>
      ∃ ancestor : α,
        cache (ancestor, proof.head) = some root ∧
        ChainInCache cache leaf ancestor idxLeft proof.tail
  | .ofRight idxRight, proof =>
      ∃ ancestor : α,
        cache (proof.head, ancestor) = some root ∧
        ChainInCache cache leaf ancestor idxRight proof.tail

/-- The later phase added a previously uncached query whose answer is `target`. -/
private def CacheAddsValue (cache₀ cache₁ : (spec α).QueryCache) (target : α) : Prop :=
  ∃ input : α × α, cache₁ input = some target ∧ cache₀ input = none

private lemma chainInCache_mono {s : Skeleton} (idx : SkeletonLeafIndex s)
    {cache₁ cache₂ : (spec α).QueryCache} {root leaf : α}
    {proof : List.Vector α idx.depth}
    (hle : cache₁ ≤ cache₂) (hchain : ChainInCache cache₁ leaf root idx proof) :
    ChainInCache cache₂ leaf root idx proof := by
  induction idx generalizing root with
  | ofLeaf => exact hchain
  | @ofLeft sl sr idxLeft ih | @ofRight sl sr idxRight ih =>
    obtain ⟨ancestor, hentry, hrec⟩ := hchain
    exact ⟨ancestor, hle hentry, ih hrec⟩

private lemma chainInCache_of_mem_support_getPutativeRoot
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf : α) (proof : List.Vector α idx.depth) (root : α)
    (cache₀ cache₁ : (spec α).QueryCache)
    (hmem : (root, cache₁) ∈ support
      ((simulateQ (spec α).cachingOracle
        (getPutativeRoot (m := OracleComp (spec α)) idx leaf proof)).run cache₀)) :
    ChainInCache cache₁ leaf root idx proof := by
  induction idx generalizing root cache₀ cache₁ with
  | ofLeaf =>
    simp only [getPutativeRoot, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff, Prod.mk.injEq] at hmem
    exact hmem.1.symm
  | @ofLeft sl sr idxLeft ih =>
    rw [show getPutativeRoot (m := OracleComp (spec α)) (.ofLeft idxLeft) leaf proof =
      getPutativeRoot idxLeft leaf proof.tail >>= fun ancestor =>
        singleHash ancestor proof.head from rfl,
      simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ancestor, cacheMid⟩, hrec, hhash⟩ := hmem
    have hentry : cache₁ (ancestor, proof.head) = some root := by
      exact cachingOracle_query_caches (ancestor, proof.head) cacheMid root cache₁ (by
        simpa only [singleHash, HasQuery.instOfMonadLift_query,
          cachingOracle.simulateQ_query] using hhash)
    have hmono : cacheMid ≤ cache₁ :=
      simulateQ_cachingOracle_cache_le (singleHash ancestor proof.head) cacheMid _ hhash
    exact ⟨ancestor, hentry, chainInCache_mono idxLeft hmono
      (ih proof.tail ancestor cache₀ cacheMid hrec)⟩
  | @ofRight sl sr idxRight ih =>
    rw [show getPutativeRoot (m := OracleComp (spec α)) (.ofRight idxRight) leaf proof =
      getPutativeRoot idxRight leaf proof.tail >>= fun ancestor =>
        singleHash proof.head ancestor from rfl,
      simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ancestor, cacheMid⟩, hrec, hhash⟩ := hmem
    have hentry : cache₁ (proof.head, ancestor) = some root := by
      exact cachingOracle_query_caches (proof.head, ancestor) cacheMid root cache₁ (by
        simpa only [singleHash, HasQuery.instOfMonadLift_query,
          cachingOracle.simulateQ_query] using hhash)
    have hmono : cacheMid ≤ cache₁ :=
      simulateQ_cachingOracle_cache_le (singleHash proof.head ancestor) cacheMid _ hhash
    exact ⟨ancestor, hentry, chainInCache_mono idxRight hmono
      (ih proof.tail ancestor cache₀ cacheMid hrec)⟩

private lemma chainInCache_of_mem_support_verifyProof
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf root : α) (proof : List.Vector α idx.depth)
    (cache₀ cache₁ : (spec α).QueryCache)
    (hmem : (true, cache₁) ∈ support
      ((simulateQ (spec α).cachingOracle
        (verifyProof (m := OracleComp (spec α)) idx leaf root proof)).run cache₀)) :
    ChainInCache cache₁ leaf root idx proof := by
  unfold verifyProof at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨putativeRoot, cacheMid⟩, hroot, hfinal⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq] at hfinal
  obtain ⟨hroot_eq, rfl⟩ := hfinal
  have hputative : putativeRoot = root := by
    simpa only [beq_iff_eq] using hroot_eq.symm
  subst root
  exact chainInCache_of_mem_support_getPutativeRoot
    idx leaf proof putativeRoot cache₀ cache₁ hroot

private lemma fresh_commitTarget_of_extractor_disagreement
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (log : (spec α).QueryLog) (cacheCommit cacheFinal : (spec α).QueryCache)
    (root leaf : α) (proof : List.Vector α idx.depth)
    (hlogCache : ∀ entry ∈ log, cacheCommit entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cacheCommit input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hno : ¬ CacheHasCollision cacheCommit)
    (hmono : cacheCommit ≤ cacheFinal)
    (hchain : ChainInCache cacheFinal leaf root idx proof)
    (hdisagree :
      some leaf ≠ (extractor s log root).get idx.toNodeIndex ∨
      proof.toList.map some ≠ (generateProof (extractor s log root) idx).toList) :
    ∃ target ∈ commitTargets root log,
      CacheAddsValue cacheCommit cacheFinal target := by
  induction idx generalizing root with
  | ofLeaf =>
    simp only [ChainInCache] at hchain
    subst root
    have hleaf :
        some leaf ≠ (extractor .leaf log leaf).get SkeletonLeafIndex.ofLeaf.toNodeIndex :=
      hdisagree.resolve_right (by simp [generateProof])
    exact (hleaf rfl).elim
  | @ofLeft sl sr idxLeft ih =>
    obtain ⟨ancestor, hquery, hchainTail⟩ := hchain
    cases hfind : log.find? (fun ⟨_, response⟩ => response == root) with
    | none =>
        have hfresh : cacheCommit (ancestor, proof.head) = none := by
          by_contra hne
          obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hne
          have hvalueFinal := hmono hvalue
          rw [hquery] at hvalueFinal
          obtain rfl := Option.some.inj hvalueFinal
          obtain ⟨entry, hentry, _, hresponse⟩ :=
            hcacheLog (ancestor, proof.head) root hvalue
          have hsome :
              (log.find? (fun ⟨_, response⟩ => response == root)).isSome = true := by
            rw [List.find?_isSome]
            exact ⟨entry, hentry, by simp [hresponse]⟩
          simp [hfind] at hsome
        exact ⟨root, by simp [commitTargets], ⟨(ancestor, proof.head), hquery, hfresh⟩⟩
    | some entry =>
        obtain ⟨⟨left, right⟩, response⟩ := entry
        have hresponse : response = root := by
          have := List.find?_some hfind
          simpa only [beq_iff_eq] using this
        subst response
        have hentry : (⟨(left, right), root⟩ : (_ : α × α) × α) ∈ log :=
          List.mem_of_find?_eq_some hfind
        have hcached : cacheCommit (left, right) = some root := hlogCache _ hentry
        cases hqueryCommit : cacheCommit (ancestor, proof.head) with
        | none =>
            exact ⟨root, by simp [commitTargets],
              ⟨(ancestor, proof.head), hquery, hqueryCommit⟩⟩
        | some value =>
            have hvalueFinal := hmono hqueryCommit
            rw [hquery] at hvalueFinal
            obtain rfl := Option.some.inj hvalueFinal
            have hinputs : (left, right) = (ancestor, proof.head) :=
              cache_lookup_eq_of_noCollision hno hcached
                ⟨root, hqueryCommit, HEq.rfl⟩
            have hleft : left = ancestor := congrArg Prod.fst hinputs
            have hright : right = proof.head := congrArg Prod.snd hinputs
            subst left
            subst right
            have hchildDisagree :
                some leaf ≠ (extractor sl log ancestor).get idxLeft.toNodeIndex ∨
                proof.tail.toList.map some ≠
                  (generateProof (extractor sl log ancestor) idxLeft).toList := by
              rw [extractor_internal_eq_of_find?_eq sl sr log root ancestor proof.head hfind]
                at hdisagree
              rcases hdisagree with hleaf | hproof
              · exact Or.inl (by
                  simpa [SkeletonLeafIndex.toNodeIndex, FullData.get] using hleaf)
              · refine Or.inr fun htail => hproof ?_
                have hsibling : (extractor sr log proof.head).getRootValue = some proof.head :=
                  optionPopulateDown_getRootValue _ _
                have hproofList : proof.toList = proof.head :: proof.tail.toList := by
                  rw [← proof.cons_head_tail]
                  rfl
                rw [hproofList, List.map_cons]
                change some proof.head :: proof.tail.toList.map some =
                  (extractor sr log proof.head).getRootValue ::
                    (generateProof (extractor sl log ancestor) idxLeft).toList
                rw [hsibling, htail]
            obtain ⟨target, htarget, hfresh⟩ :=
              ih ancestor proof.tail hchainTail hchildDisagree
            have hancestor : ancestor ∈
                log.flatMap fun entry => [entry.1.1, entry.1.2] := by
              simp only [List.mem_flatMap]
              exact ⟨⟨(ancestor, proof.head), root⟩, hentry, by simp⟩
            exact ⟨target, commitTargets_mono_root hancestor htarget, hfresh⟩
  | @ofRight sl sr idxRight ih =>
    obtain ⟨ancestor, hquery, hchainTail⟩ := hchain
    cases hfind : log.find? (fun ⟨_, response⟩ => response == root) with
    | none =>
        have hfresh : cacheCommit (proof.head, ancestor) = none := by
          by_contra hne
          obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hne
          have hvalueFinal := hmono hvalue
          rw [hquery] at hvalueFinal
          obtain rfl := Option.some.inj hvalueFinal
          obtain ⟨entry, hentry, _, hresponse⟩ :=
            hcacheLog (proof.head, ancestor) root hvalue
          have hsome :
              (log.find? (fun ⟨_, response⟩ => response == root)).isSome = true := by
            rw [List.find?_isSome]
            exact ⟨entry, hentry, by simp [hresponse]⟩
          simp [hfind] at hsome
        exact ⟨root, by simp [commitTargets], ⟨(proof.head, ancestor), hquery, hfresh⟩⟩
    | some entry =>
        obtain ⟨⟨left, right⟩, response⟩ := entry
        have hresponse : response = root := by
          have := List.find?_some hfind
          simpa only [beq_iff_eq] using this
        subst response
        have hentry : (⟨(left, right), root⟩ : (_ : α × α) × α) ∈ log :=
          List.mem_of_find?_eq_some hfind
        have hcached : cacheCommit (left, right) = some root := hlogCache _ hentry
        cases hqueryCommit : cacheCommit (proof.head, ancestor) with
        | none =>
            exact ⟨root, by simp [commitTargets],
              ⟨(proof.head, ancestor), hquery, hqueryCommit⟩⟩
        | some value =>
            have hvalueFinal := hmono hqueryCommit
            rw [hquery] at hvalueFinal
            obtain rfl := Option.some.inj hvalueFinal
            have hinputs : (left, right) = (proof.head, ancestor) :=
              cache_lookup_eq_of_noCollision hno hcached
                ⟨root, hqueryCommit, HEq.rfl⟩
            have hleft : left = proof.head := congrArg Prod.fst hinputs
            have hright : right = ancestor := congrArg Prod.snd hinputs
            subst left
            subst right
            have hchildDisagree :
                some leaf ≠ (extractor sr log ancestor).get idxRight.toNodeIndex ∨
                proof.tail.toList.map some ≠
                  (generateProof (extractor sr log ancestor) idxRight).toList := by
              rw [extractor_internal_eq_of_find?_eq sl sr log root proof.head ancestor hfind]
                at hdisagree
              rcases hdisagree with hleaf | hproof
              · exact Or.inl (by
                  simpa [SkeletonLeafIndex.toNodeIndex, FullData.get] using hleaf)
              · refine Or.inr fun htail => hproof ?_
                have hsibling : (extractor sl log proof.head).getRootValue = some proof.head :=
                  optionPopulateDown_getRootValue _ _
                have hproofList : proof.toList = proof.head :: proof.tail.toList := by
                  rw [← proof.cons_head_tail]
                  rfl
                rw [hproofList, List.map_cons]
                change some proof.head :: proof.tail.toList.map some =
                  (extractor sl log proof.head).getRootValue ::
                    (generateProof (extractor sr log ancestor) idxRight).toList
                rw [hsibling, htail]
            obtain ⟨target, htarget, hfresh⟩ :=
              ih ancestor proof.tail hchainTail hchildDisagree
            have hancestor : ancestor ∈
                log.flatMap fun entry => [entry.1.1, entry.1.2] := by
              simp only [List.mem_flatMap]
              exact ⟨⟨(proof.head, ancestor), root⟩, hentry, by simp⟩
            exact ⟨target, commitTargets_mono_root hancestor htarget, hfresh⟩

private lemma chainInLog_mono {s : Skeleton} (idx : SkeletonLeafIndex s)
    {log1 log2 : (spec α).QueryLog} {root leaf : α}
    {proof : List.Vector α idx.depth}
    (h_sub : ∀ q, q ∈ log1 → q ∈ log2)
    (h_chain : ChainInLog log1 leaf root idx proof) :
    ChainInLog log2 leaf root idx proof := by
  induction idx generalizing root with
  | ofLeaf => exact h_chain
  | @ofLeft sl sr idxLeft ih | @ofRight sl sr idxRight ih =>
    obtain ⟨ancestor, h_mem, h_rec⟩ := h_chain
    exact ⟨ancestor, h_sub _ h_mem, ih h_rec⟩

private lemma chainInLog_of_mem_support_getPutativeRoot
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf : α) (proof : List.Vector α idx.depth) (r : α)
    (log_v : (spec α).QueryLog)
    (hmem : (r, log_v) ∈ support
        (getPutativeRoot (m := OracleComp (spec α)) idx leaf proof).withQueryLog) :
    ChainInLog log_v leaf r idx proof := by
  induction idx generalizing r log_v with
  | ofLeaf =>
    rw [show (getPutativeRoot (m := OracleComp (spec α))
        SkeletonLeafIndex.ofLeaf leaf proof) = pure leaf from rfl,
      OracleComp.withQueryLog_pure, mem_support_pure_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    rfl
  | @ofLeft sl sr idxLeft ih =>
    obtain ⟨a, log_a, h_rec, rfl⟩ :=
      getPutativeRoot_step_withQueryLog_decompose
        (getPutativeRoot (m := OracleComp (spec α)) idxLeft leaf proof.tail)
        (fun a => (a, proof.head)) r log_v hmem
    exact ⟨a, by simp, chainInLog_mono _ (fun _ => List.mem_append_left _)
      (ih proof.tail a log_a h_rec)⟩
  | @ofRight sl sr idxRight ih =>
    obtain ⟨a, log_a, h_rec, rfl⟩ :=
      getPutativeRoot_step_withQueryLog_decompose
        (getPutativeRoot (m := OracleComp (spec α)) idxRight leaf proof.tail)
        (fun a => (proof.head, a)) r log_v hmem
    exact ⟨a, by simp, chainInLog_mono _ (fun _ => List.mem_append_left _)
      (ih proof.tail a log_a h_rec)⟩

/--
If a particular transcript is in the support of a successful `verifyProof` computation
with the query log,
then that log contains a hash chain from `root` down to `leaf`.
-/
private lemma chainInLog_of_mem_support_verifyProof
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf root : α) (proof : List.Vector α idx.depth)
    (log_v : (spec α).QueryLog)
    (hmem : (true, log_v) ∈ support
        (verifyProof (m := OracleComp (spec α)) idx leaf root proof).withQueryLog) :
    ChainInLog log_v leaf root idx proof := by
  grind [ChainInLog, OracleComp.withQueryLog_bind, chainInLog_of_mem_support_getPutativeRoot]

/-- **Log-level binding (Collision Lemma at the log level).** Log-formalized
analog of `getPutativeRootWithHash_binding_collision`: two distinct openings
`(x, proof₁) ≠ (y, proof₂)` of the same `root` at the same index, both
witnessed by hash chains `ChainInLog` in the same `log`, force `log` to
contain a hash collision (two log entries with equal responses but distinct
inputs). -/
theorem logHasCollision_of_chainInLog_of_ne
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (log : (spec α).QueryLog) (root x y : α)
    (proof₁ proof₂ : List.Vector α idx.depth)
    (hne : (x, proof₁) ≠ (y, proof₂))
    (hc₁ : ChainInLog log x root idx proof₁)
    (hc₂ : ChainInLog log y root idx proof₂) :
    LogHasCollision log := by
  induction idx generalizing root x y with
  | ofLeaf =>
    exact absurd (Prod.ext (hc₁.trans hc₂.symm) (List.Vector.ext (fun i => i.elim0))) hne
  | @ofLeft sl sr idxLeft ih =>
    obtain ⟨a₁, h₁_mem, hc₁⟩ := hc₁
    obtain ⟨a₂, h₂_mem, hc₂⟩ := hc₂
    by_cases hpair : (a₁, proof₁.head) = (a₂, proof₂.head)
    · obtain ⟨rfl, hhead⟩ := Prod.mk.inj hpair
      refine ih _ _ _ _ _ (fun heq => hne ?_) hc₁ hc₂
      obtain ⟨rfl, htail⟩ := Prod.mk.inj heq
      exact Prod.ext rfl (((List.Vector.eq_cons_iff _ _ _).mpr
        ⟨hhead, htail⟩).trans proof₂.cons_head_tail)
    · exact LogHasCollision.of_mem (fun h => hpair (congrArg Sigma.fst h))
        h₁_mem h₂_mem (heq_of_eq rfl)
  | @ofRight sl sr idxRight ih =>
    obtain ⟨a₁, h₁_mem, hc₁⟩ := hc₁
    obtain ⟨a₂, h₂_mem, hc₂⟩ := hc₂
    by_cases hpair : (proof₁.head, a₁) = (proof₂.head, a₂)
    · obtain ⟨hhead, rfl⟩ := Prod.mk.inj hpair
      refine ih _ _ _ _ _ (fun heq => hne ?_) hc₁ hc₂
      obtain ⟨rfl, htail⟩ := Prod.mk.inj heq
      exact Prod.ext rfl (((List.Vector.eq_cons_iff _ _ _).mpr
        ⟨hhead, htail⟩).trans proof₂.cons_head_tail)
    · exact LogHasCollision.of_mem (fun h => hpair (congrArg Sigma.fst h))
        h₁_mem h₂_mem (heq_of_eq rfl)

/-- Post-IH assembly for the `ofLeft` case of `chainInLog_of_extractor_get_ne_none`.
Given a recursive witness on the left subtree (with ancestor `x`), repackage it
into the witness for the full internal node, using the log entry `⟨(x, y), root⟩`
and consing the sibling `y` onto the extracted proof. -/
private lemma chainInLog_of_extractor_internal_step_left
    [DecidableEq α]
    {sl sr : Skeleton} (idxLeft : SkeletonLeafIndex sl)
    (log : (spec α).QueryLog) (root x y : α)
    (hf : log.find? (fun ⟨_, r⟩ => r == root) = some ⟨(x, y), root⟩)
    (h_rec : ∃ extLeaf : α, ∃ extProof : List.Vector α idxLeft.depth,
        (extractor sl log x).get idxLeft.toNodeIndex = some extLeaf ∧
        (generateProof (extractor sl log x) idxLeft).toList = extProof.toList.map some ∧
        ChainInLog log extLeaf x idxLeft extProof) :
    ∃ extLeaf : α, ∃ extProof : List.Vector α
        (SkeletonLeafIndex.ofLeft (right := sr) idxLeft).depth,
      (extractor (Skeleton.internal sl sr) log root).get
          (SkeletonLeafIndex.ofLeft (right := sr) idxLeft).toNodeIndex = some extLeaf ∧
      (generateProof (extractor (Skeleton.internal sl sr) log root)
          (SkeletonLeafIndex.ofLeft (right := sr) idxLeft)).toList = extProof.toList.map some ∧
      ChainInLog log extLeaf root (SkeletonLeafIndex.ofLeft (right := sr) idxLeft) extProof := by
  obtain ⟨extLeaf, extProof, h_extLeaf, h_extProof, h_chain⟩ := h_rec
  rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]
  refine ⟨extLeaf, y ::ᵥ extProof, h_extLeaf, ?_, x, List.mem_of_find?_eq_some hf, h_chain⟩
  have h_root_value : (extractor sr log y).getRootValue = some y :=
    optionPopulateDown_getRootValue _ _
  grind [Nat.succ_eq_add_one, List.Vector.toList_cons, SkeletonLeafIndex.depth]

/-- Post-IH assembly for the `ofRight` case of `chainInLog_of_extractor_get_ne_none`.
Symmetric to `chainInLog_of_extractor_internal_step_left`: the recursive witness
lives on the right subtree (ancestor `y`) and the sibling `x` is consed onto the
extracted proof. -/
private lemma chainInLog_of_extractor_internal_step_right
    [DecidableEq α]
    {sl sr : Skeleton} (idxRight : SkeletonLeafIndex sr)
    (log : (spec α).QueryLog) (root x y : α)
    (hf : log.find? (fun ⟨_, r⟩ => r == root) = some ⟨(x, y), root⟩)
    (h_rec : ∃ extLeaf : α, ∃ extProof : List.Vector α idxRight.depth,
        (extractor sr log y).get idxRight.toNodeIndex = some extLeaf ∧
        (generateProof (extractor sr log y) idxRight).toList = extProof.toList.map some ∧
        ChainInLog log extLeaf y idxRight extProof) :
    ∃ extLeaf : α, ∃ extProof : List.Vector α
        (SkeletonLeafIndex.ofRight (left := sl) idxRight).depth,
      (extractor (Skeleton.internal sl sr) log root).get
          (SkeletonLeafIndex.ofRight (left := sl) idxRight).toNodeIndex = some extLeaf ∧
      (generateProof (extractor (Skeleton.internal sl sr) log root)
          (SkeletonLeafIndex.ofRight (left := sl) idxRight)).toList = extProof.toList.map some ∧
      ChainInLog log extLeaf root (SkeletonLeafIndex.ofRight (left := sl) idxRight) extProof := by
  obtain ⟨extLeaf, extProof, h_extLeaf, h_extProof, h_chain⟩ := h_rec
  rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]
  refine ⟨extLeaf, x ::ᵥ extProof, h_extLeaf, ?_, y, List.mem_of_find?_eq_some hf, h_chain⟩
  have h_root_value : (extractor sl log x).getRootValue = some x :=
    optionPopulateDown_getRootValue _ _
  grind [Nat.succ_eq_add_one, List.Vector.toList_cons, SkeletonLeafIndex.depth]

/-- **Extractor recovery to a log chain.** When the extractor's path at `idx`
is intact (the value there is `≠ none`), the extracted leaf value and proof
form a hash chain `ChainInLog` in the log. The conclusion bundles three
facts: the extracted leaf (`extLeaf`), the recovered authentication path
(`extProof`), and a chain witness in `log` connecting them to `root`. -/
theorem chainInLog_of_extractor_get_ne_none
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (log : (spec α).QueryLog) (root : α)
    (h_ne_none : (extractor s log root).get idx.toNodeIndex ≠ none) :
    ∃ extLeaf : α, ∃ extProof : List.Vector α idx.depth,
      (extractor s log root).get idx.toNodeIndex = some extLeaf ∧
      (generateProof (extractor s log root) idx).toList = extProof.toList.map some ∧
      ChainInLog log extLeaf root idx extProof := by
  induction idx generalizing root with
  | ofLeaf => exact ⟨root, ⟨[], rfl⟩, rfl, rfl, rfl⟩
  | @ofLeft sl sr idxLeft ih =>
    rcases hf : log.find? (fun ⟨_, r⟩ => r == root) with _ | ⟨⟨x, y⟩, r⟩
    · exact absurd (extractor_internal_get_eq_none_of_find?_eq_none
        sl sr log root (Sum.inl idxLeft.toNodeIndex) hf) h_ne_none
    rw [show r = root by grind [find?_eq_some_iff_getElem]] at hf
    exact chainInLog_of_extractor_internal_step_left idxLeft log root x y hf
      (ih x (fun he =>
        h_ne_none (by rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]; exact he)))
  | @ofRight sl sr idxRight ih =>
    rcases hf : log.find? (fun ⟨_, r⟩ => r == root) with _ | ⟨⟨x, y⟩, r⟩
    · exact absurd (extractor_internal_get_eq_none_of_find?_eq_none
        sl sr log root (Sum.inr idxRight.toNodeIndex) hf) h_ne_none
    rw [show r = root by grind [find?_eq_some_iff_getElem]] at hf
    exact chainInLog_of_extractor_internal_step_right idxRight log root x y hf
      (ih y (fun he =>
        h_ne_none (by rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]; exact he)))

private theorem extractabilityInner_not_logHasCollision_match
    [DecidableEq α]
    {s : Skeleton} (𝒜 : Adversary α s)
    {root : α} {aux : 𝒜.AuxState} {idx : SkeletonLeafIndex s} {leaf : α}
    {proof : List.Vector α idx.depth}
    {extractedTree : FullData (Option α) s}
    {extractedProof : List.Vector (Option α) idx.depth}
    {log : (spec α).QueryLog}
    (h_not_logHasCollision : ¬ LogHasCollision log)
    (h_ne_none : extractedTree.get idx.toNodeIndex ≠ none)
    (hsupport : ((root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, true⟩),
                  log) ∈
      support (extractabilityInner 𝒜).withQueryLog) :
    extractedTree.get idx.toNodeIndex = some leaf ∧
      proof.toList.map some = extractedProof.toList := by
  obtain ⟨log_c, log_v, h_vp, h_sub_v, h_sub_c, h_tree_eq, h_proof_ext_eq⟩ :=
    extractabilityInner_support_decompose 𝒜 hsupport
  obtain ⟨extLeaf, extProof, h_extLeaf_eq, h_extProof_eq, h_extChain_lc⟩ :=
    chainInLog_of_extractor_get_ne_none idx log_c root (h_tree_eq ▸ h_ne_none)
  by_cases hpair : (extLeaf, extProof) = (leaf, proof)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    exact ⟨h_tree_eq.symm ▸ h_extLeaf_eq, by rw [h_proof_ext_eq, h_extProof_eq]⟩
  · exact absurd (logHasCollision_of_chainInLog_of_ne idx log root extLeaf leaf
      extProof proof hpair (chainInLog_mono idx h_sub_c h_extChain_lc)
      (chainInLog_mono idx h_sub_v
        (chainInLog_of_mem_support_verifyProof idx leaf root proof log_v h_vp)))
      h_not_logHasCollision

end InductiveMerkleTree
