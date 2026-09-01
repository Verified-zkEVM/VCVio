/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Extractor
public import VCVio.CryptoFoundations.MerkleTree.Addressed.QueryBound
public import VCVio.OracleComp.QueryTracking.Collision
public import ToMathlib.Data.IndexedBinaryTree.Lemmas
import VCVio.OracleComp.QueryTracking.AdaptivePrefix
import VCVio.OracleComp.QueryTracking.Unpredictability

/-!
# Query-parametric Merkle tree extractability

This is the single probabilistic owner for single-opening Merkle extractability over a homogeneous
random oracle `Query →ₒ Y`. A `NodeQueryModel` supplies both the complete query constructed by
verification and the address/children view consumed by the transcript extractor. Cache collisions
are therefore collisions of complete queries; the position-to-address map need not be injective.

The experiment runs commit, opening, and verification against one shared lazy random function.
The extractor follows response links in the commit log. The proof combines a deterministic
cache-chain disagreement lemma with an adaptive-prefix stopping argument. For `m` remaining
adversary queries, `k` cached inputs, `c` future fresh commit inputs, and `T = 2·leafCount - 1`,
the branch energy is

`c·k + choose(c,2) + min(T, 2(k+c)+1)·(m-c+depth)`.

Tracking `c` in the still-running computation avoids conditioning a birthday estimate on an
adaptively chosen commit stopping time.

## Comparison with Chiesa–Yogev, Version 1.2

Lemma 18.5.1 considers a perfect tree with `L` leaves, depth `d`, range size `N`, and `q`
adversary queries. Its displayed bound is

`choose(q,2)/N + 2L(d+1)/N`,

then `q²/(2N)` under `q ≥ 4L(d+1)`. The proof first obtains

`max(2L(q+d+1), choose(q,2)+2L(d+1))/N`

and discards the first branch using `q ≥ 4L+1`. Version 1.1 states that hypothesis; Version 1.2's
displayed lemma omits it while retaining the proof step. Its fixed-realized-prefix argument also
needs a stopping-time justification when the commit phase stops adaptively. The finite-maximum
theorem here supplies that justification and keeps the two-endpoint maximum unconditionally.

For this raw-leaf model, under `q ≥ 2T+1 = 4L-1`, the coarse bound is

`choose(q,2)/|Y| + T·d/|Y|`.

This is no weaker than the source after aligning models: the source hashes salted leaves and counts
`d+1` checker calls, while this verifier makes `d` internal-node calls. The quadratic corollary also
assumes `2T·d ≤ q`; the source condition `q ≥ 4L(d+1)` implies both hypotheses.

The theorem supports arbitrary full binary skeletons but only one opening and deterministic
`OracleComp` adversaries. Batch extraction, randomized adversaries, total-extractor/runtime claims,
and heterogeneous-super-oracle projection are separate work.

`Query` and `Y` remain in `Type` because the inherited birthday primitive is stated for
`OracleSpec.{0,0}`. Pure `Address` is universe-polymorphic; any concrete address embedded into the
complete Type-0 `Query` inherits that boundary. This is a framework limitation, not a mathematical
one.

## References

* [Chiesa–Yogev, *Building Cryptographic Proofs from Hash Functions*, Version 1.2,
  Lemma 18.5.1](https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L13186-L13211)
  and its [proof](https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L13264-L13455).
* [Version 1.1 statement carrying the `q ≥ 4L+1`
  hypothesis](https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/92deb71d65d4c75a34c98d2280d513c959b0ea35/snargs-book.tex#L11763-L11787).
-/

@[expose] public section

namespace MerkleTreeExtractability

open List OracleSpec OracleComp BinaryTree InductiveMerkleTree

universe u

variable {Query Y : Type} {Address : Type u}

/-- Complete interface between typed Merkle positions and the homogeneous random-oracle query
type.  The extractor consumes `view`; verification issues `mkQuery`.  Only the two projection
laws are required, so the adversary may also issue arbitrary queries outside the constructor's
image. -/
structure NodeQueryModel (Query : Type) (Address : Type u) (Y : Type) where
  /-- Project complete oracle queries to the address and ordered children used by extraction. -/
  view : MerkleTreeExtractor.QueryView Query Address Y
  /-- Construct the complete oracle query for one addressed pair of children. -/
  mkQuery : Address → Y × Y → Query
  /-- Constructed queries retain their address exactly. -/
  address_mkQuery : ∀ address input, view.address (mkQuery address input) = address
  /-- Constructed queries retain their ordered child pair exactly. -/
  input_mkQuery : ∀ address input, view.input (mkQuery address input) = input

/-! ## Adversary -/

section Adversary

/-- An adversary in the Merkle tree extractability game, packaged as a single
two-phase object: a committing phase that produces a claimed root together with
auxiliary state, and an opening phase that consumes the auxiliary state to
produce a (leaf index, leaf value, authentication path) triple. -/
structure Adversary (Query Y : Type) (s : Skeleton) where
  /-- Auxiliary state carried from the committing phase to the opening phase. -/
  AuxState : Type
  /-- Committing phase: produce a claimed root and auxiliary state. -/
  commit : OracleComp (Query →ₒ Y) (Y × AuxState)
  /-- Opening phase: given the auxiliary state, produce a leaf index, claimed
  leaf value, and authentication path. -/
  opening : AuxState → OracleComp (Query →ₒ Y)
      ((idx : SkeletonLeafIndex s) × Y × List.Vector Y idx.depth)

/-- The combined two-phase execution of `𝒜` has total query bound `qb`. -/
def Adversary.IsTwoPhaseTotalQueryBound {s : Skeleton}
    (𝒜 : Adversary Query Y s) (qb : ℕ) : Prop :=
  IsTotalQueryBound
    (do
      let (_root, aux) ← 𝒜.commit
      let ⟨_idx, _leaf, _proof⟩ ← 𝒜.opening aux
      pure ())
    qb

end Adversary

/-! ## Extractability game -/

section ExtractabilityGame

variable [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]

/-- The labels of the non-dummy nodes that the extractor actually reconstructs. Unlike
the full query log, this list follows only response links reachable from the claimed root. -/
private abbrev extractedTargets (model : NodeQueryModel Query Address Y) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (log : (Query →ₒ Y).QueryLog) (root : Y) : List Y :=
  MerkleTreeExtractor.targets model.view s addressKey log root

omit [DecidableEq Query] in
/-- A full binary skeleton with `L` leaves has `2L - 1` nodes, so the extractor can
reconstruct at most that many non-dummy labels, independently of the query-log length. -/
private lemma extractedTargets_length_le (model : NodeQueryModel Query Address Y) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (log : (Query →ₒ Y).QueryLog) (root : Y) :
    (extractedTargets model s addressKey log root).length ≤ 2 * s.leafCount - 1 :=
  MerkleTreeExtractor.targets_length_le model.view s addressKey log root

omit [DecidableEq Query] in
/-- Every extracted label is either the claimed root or one component of a logged hash
input. The statement tracks reachability, while forgetting the particular ancestor chain. -/
private lemma mem_extractedTargets_root_or_log_input
    (model : NodeQueryModel Query Address Y) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (log : (Query →ₒ Y).QueryLog) (root : Y) {target : Y}
    (htarget : target ∈ extractedTargets model s addressKey log root) :
    target = root ∨ ∃ entry ∈ log,
      target = (model.view.input entry.1).1 ∨ target = (model.view.input entry.1).2 :=
  MerkleTreeExtractor.mem_targets_root_or_log_input
    model.view s addressKey log root htarget

omit [DecidableEq Query] in
/-- If all logged inputs are populated in a finite key set, the distinct extracted labels
fit in the root plus the two coordinate images of that key set. -/
private lemma extractedTargets_toFinset_card_le_cacheKeys
    (model : NodeQueryModel Query Address Y) (s : Skeleton)
    (addressKey : SkeletonInternalIndex s → Address)
    (log : (Query →ₒ Y).QueryLog) (root : Y)
    {cache : (Query →ₒ Y).QueryCache} (keys : Finset Query)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hkeys : ∀ input, cache input ≠ none → input ∈ keys) :
    (extractedTargets model s addressKey log root).toFinset.card ≤ 2 * keys.card + 1 := by
  let candidates : Finset Y :=
    insert root
      (keys.image (fun query => (model.view.input query).1) ∪
        keys.image (fun query => (model.view.input query).2))
  have hsubset : (extractedTargets model s addressKey log root).toFinset ⊆ candidates := by
    intro target htarget
    have htarget' : target ∈ extractedTargets model s addressKey log root := by
      simpa using htarget
    rcases mem_extractedTargets_root_or_log_input model s addressKey log root htarget' with
      rfl | hinput
    · exact Finset.mem_insert_self _ _
    · obtain ⟨entry, hentry, hside⟩ := hinput
      have hkey : entry.1 ∈ keys := hkeys entry.1 (by
        rw [hlogCache entry hentry]
        exact Option.some_ne_none _)
      rcases hside with hleft | hright
      · subst target
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨entry.1, hkey, rfl⟩))
      · subst target
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨entry.1, hkey, rfl⟩))
  calc
    (extractedTargets model s addressKey log root).toFinset.card ≤ candidates.card :=
      Finset.card_le_card hsubset
    _ ≤ (keys.image (fun query => (model.view.input query).1) ∪
          keys.image (fun query => (model.view.input query).2)).card + 1 := by
      simpa only [candidates, Nat.add_comm] using
        Finset.card_insert_le root
          (keys.image (fun query => (model.view.input query).1) ∪
            keys.image (fun query => (model.view.input query).2))
    _ ≤ (keys.image (fun query => (model.view.input query).1)).card +
          (keys.image (fun query => (model.view.input query).2)).card + 1 := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ 2 * keys.card + 1 := by
      have hfst := Finset.card_image_le (s := keys)
        (f := fun query => (model.view.input query).1)
      have hsnd := Finset.card_image_le (s := keys)
        (f := fun query => (model.view.input query).2)
      omega

/-- Verify an opening by issuing the model's complete node query at each typed position. -/
def verifyOpening (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (idx : SkeletonLeafIndex s) (leaf root : Y) (proof : List.Vector Y idx.depth) :
    OracleComp (Query →ₒ Y) Bool := do
  let putativeRoot ← AddressedMerkleTree.getPutativeRootAddressedM
    (fun position left right =>
      liftM ((Query →ₒ Y).query (model.mkQuery (addressKey position) (left, right))))
    idx leaf proof
  return putativeRoot == root

/--
The oracle syntax underlying the extractability experiment. It runs the committing
adversary, snapshots that phase's query log for the extractor, runs the opening adversary,
and finally verifies the opening. Random-function consistency is supplied separately by
`extractabilityGame`.
-/
def extractabilityInner (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (𝒜 : Adversary Query Y s) :
    OracleComp (Query →ₒ Y) (Y × 𝒜.AuxState ×
        ((idx : SkeletonLeafIndex s) × Y × List.Vector Y idx.depth ×
         FullData (Option Y) s × List.Vector (Option Y) idx.depth × Bool)) :=
  do
    let ((root, aux), queryLog) ← 𝒜.commit.withQueryLog
    let extractedTree := MerkleTreeExtractor.tree model.view s addressKey queryLog root
    let ⟨idx, leaf, proof⟩ ← 𝒜.opening aux
    let extractedOpening := MerkleTreeExtractor.opening extractedTree idx
    let verified ← verifyOpening model addressKey idx leaf root proof
    return (root, aux, ⟨idx, leaf, proof, extractedTree, extractedOpening.proof, verified⟩)

/-- The opening-and-verification suffix after fixing a logged commit outcome. This is the
actual cached continuation used in the ROM proof; it does not resample or reset the oracle. -/
private def extractabilityRest (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (𝒜 : Adversary Query Y s)
    (root : Y) (aux : 𝒜.AuxState) (queryLog : (Query →ₒ Y).QueryLog) :
    OracleComp (Query →ₒ Y) (Y × 𝒜.AuxState ×
        ((idx : SkeletonLeafIndex s) × Y × List.Vector Y idx.depth ×
         FullData (Option Y) s × List.Vector (Option Y) idx.depth × Bool)) :=
  do
    let extractedTree := MerkleTreeExtractor.tree model.view s addressKey queryLog root
    let ⟨idx, leaf, proof⟩ ← 𝒜.opening aux
    let extractedOpening := MerkleTreeExtractor.opening extractedTree idx
    let verified ← verifyOpening model addressKey idx leaf root proof
    return (root, aux, ⟨idx, leaf, proof, extractedTree, extractedOpening.proof, verified⟩)

/-- Execute a still-running commit computation with a combined cache/log state, then run the
opening-and-verification suffix from the resulting state. This is the induction object for the
stopping-time proof: its query budget decreases structurally, without conditioning on a
realized commit length. -/
private def extractabilityRunFrom (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (𝒜 : Adversary Query Y s)
    (commit : OracleComp (Query →ₒ Y) (Y × 𝒜.AuxState))
    (cache : (Query →ₒ Y).QueryCache) (log : (Query →ₒ Y).QueryLog) :=
  adaptivePrefixRunFrom
    (fun x queryLog => extractabilityRest model addressKey 𝒜 x.1 x.2 queryLog)
      commit cache log

/-- Exact stopping-time contribution after `commitMisses` further fresh commit inputs:
collision hazard against the `cached` previous keys, birthday collisions among the new cache
entries, and the remaining opening/verifier fresh-target hazard. Cache hits consume the
remaining total-query budget without increasing `commitMisses`. -/
private def extractabilityEnergy (treeTargetCount depth remaining cached commitMisses : ℕ) : ℕ :=
  adaptivePrefixEnergy (fun keyCount => min treeTargetCount (2 * keyCount + 1))
    depth remaining cached commitMisses

/-- Finite maximum over every possible number of further fresh commit inputs/cache misses. -/
private def extractabilityExactPotential
  (treeTargetCount depth remaining cached : ℕ) : ℕ :=
  adaptivePrefixPotential (fun keyCount => min treeTargetCount (2 * keyCount + 1))
    depth remaining cached

omit [DecidableEq Query] in
private lemma extractabilityInner_eq_commit_bind_rest
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (𝒜 : Adversary Query Y s) :
    extractabilityInner model addressKey 𝒜 =
      𝒜.commit.withQueryLog >>= fun x =>
        extractabilityRest model addressKey 𝒜 x.1.1 x.1.2 x.2 := by
  simp [extractabilityInner, extractabilityRest]

/--
The extraction-failure event on an `extractabilityInner` transcript: verification passes
but the extracted leaf or authentication proof does not match the adversary's opening. This
is the single-leaf specialization of Merkle extractability, and compares the full authentication
path at that leaf.
-/
def AdversaryWinsExtractabilityInner {s : Skeleton} {AuxState : Type} :
    Y × AuxState ×
      ((idx : SkeletonLeafIndex s) × Y × List.Vector Y idx.depth ×
       FullData (Option Y) s × List.Vector (Option Y) idx.depth × Bool) → Prop
  | (_, _, ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩) =>
    verified = true ∧
      (some leaf ≠ extractedTree.get idx.toNodeIndex ∨
        proof.toList.map some ≠ extractedProof.toList)

/-- The Merkle-tree extractability experiment in the random-oracle model. All queries made
by the committing adversary, opening adversary, and verifier are interpreted through one
shared cache, so repeated equal inputs receive the same answer. -/
def extractabilityGame (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (𝒜 : Adversary Query Y s) :
    OracleComp (Query →ₒ Y) (Y × 𝒜.AuxState ×
        ((idx : SkeletonLeafIndex s) × Y × List.Vector Y idx.depth ×
         FullData (Option Y) s × List.Vector (Option Y) idx.depth × Bool)) :=
  (Query →ₒ Y).withCacheOverlay ∅ (extractabilityInner model addressKey 𝒜)

/-- The extraction-failure event for `extractabilityGame`. -/
def AdversaryWinsExtractabilityGame {s : Skeleton} {AuxState : Type} :
    Y × AuxState ×
      ((idx : SkeletonLeafIndex s) × Y × List.Vector Y idx.depth ×
       FullData (Option Y) s × List.Vector (Option Y) idx.depth × Bool) → Prop :=
  AdversaryWinsExtractabilityInner

omit [DecidableEq Query] in
/--
Unfold `extractabilityInner` into a nested `bind` whose outer prefix logs the committing
adversary's queries alongside the opening adversary's output, and whose continuation runs
`verifyProof` and assembles the transcript. This is the definitional rearrangement used to
expose the prefix as a target for query-bound reasoning.
-/
private lemma extractabilityInner_eq_bind_verifyOpening
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (𝒜 : Adversary Query Y s) :
    extractabilityInner model addressKey 𝒜 =
      (𝒜.commit.withQueryLog >>= fun ((root, aux), queryLog) =>
        𝒜.opening aux >>= fun q => pure (((root, aux), queryLog), q)) >>=
      fun (⟨⟨root, aux⟩, queryLog⟩, ⟨idx, leaf, proof⟩) =>
        verifyOpening model addressKey idx leaf root proof >>= fun verified =>
          pure (root, aux,
                ⟨idx, leaf, proof,
                 MerkleTreeExtractor.tree model.view s addressKey queryLog root,
                 generateProof
                   (MerkleTreeExtractor.tree model.view s addressKey queryLog root) idx,
                 verified⟩) := by
  simp only [extractabilityInner, MerkleTreeExtractor.opening_proof, bind_assoc, pure_bind]

omit [DecidableEq Query] [DecidableEq Y] in
/--
Project the logged-prefix of `extractabilityInner` onto `Unit`: discarding both the
committed root/aux and the query log of the committing adversary recovers the plain
measurement used to express the combined query bound.
-/
private lemma extractabilityInner_logged_prefix_map_unit_eq
    {s : Skeleton} (𝒜 : Adversary Query Y s) :
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

omit [DecidableEq Query] [DecidableEq Address] in
private lemma verifyOpening_isTotalQueryBound_skeleton_depth
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (idx : SkeletonLeafIndex s) (leaf root : Y) (proof : List.Vector Y idx.depth) :
    IsTotalQueryBound (verifyOpening model addressKey idx leaf root proof) s.depth := by
  unfold verifyOpening
  exact isTotalQueryBound_bind (n₁ := s.depth) (n₂ := 0)
    (AddressedMerkleTree.isTotalQueryBound_getPutativeRootAddressedM_skeleton_depth
      (fun position left right =>
        liftM ((Query →ₒ Y).query (model.mkQuery (addressKey position) (left, right))))
      idx leaf proof (fun _ _ _ => ⟨Nat.zero_lt_one, fun _ => trivial⟩))
    fun _ => trivial

omit [DecidableEq Query] in
/--
If the adversary `𝒜` has two-phase total query bound `qb`, then the full extractability
game has total query bound `qb + s.depth`.

The extra `s.depth` accounts for the `verifyProof` step, which traverses the path from the
queried leaf to the root, making at most `s.depth` oracle queries.
-/
theorem extractabilityInner_isTotalQueryBound
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : Adversary Query Y s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    IsTotalQueryBound (extractabilityInner model addressKey 𝒜) (qb + s.depth) := by
  rw [extractabilityInner_eq_bind_verifyOpening]
  exact isTotalQueryBound_bind (n₁ := qb) (n₂ := s.depth)
    ((isQueryBound_iff_of_map_eq (extractabilityInner_logged_prefix_map_unit_eq 𝒜)
      (fun _ b => 0 < b) (fun _ b => b - 1)).mpr h)
    fun (⟨⟨root, _aux⟩, _queryLog⟩, ⟨idx, leaf, proof⟩) =>
      isTotalQueryBound_bind (n₁ := s.depth) (n₂ := 0)
        (verifyOpening_isTotalQueryBound_skeleton_depth model addressKey idx leaf root proof)
        fun _ => trivial

/-- The shared-cache random-oracle experiment makes at most as many underlying fresh
queries as `extractabilityInner`. Cache hits skip the underlying query, so the implication
is intentionally one-way. -/
theorem extractabilityGame_isTotalQueryBound [IsUniformSpec (Query →ₒ Y)]
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : Adversary Query Y s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    IsTotalQueryBound (extractabilityGame model addressKey 𝒜) (qb + s.depth) := by
  apply (isQueryBound_map_iff _ _ (qb + s.depth) _ _).mpr
  exact IsTotalQueryBound.simulateQ_run_withCaching _
    (extractabilityInner_isTotalQueryBound model addressKey 𝒜 qb h)
    (fun t => (isQueryBound_query_iff t 1 _ _).mpr Nat.one_pos) ∅

/-- A hash chain interpreted in a shared random-oracle cache. Unlike `ChainInLog`,
this predicate records only the final function graph and therefore identifies cache hits
and cache misses with the same response. -/
private def ChainInCache (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (cache : (Query →ₒ Y).QueryCache) (leaf root : Y) :
    (idx : SkeletonLeafIndex s) → List.Vector Y idx.depth → Prop
  | .ofLeaf, _ => leaf = root
  | .ofLeft idxLeft, proof =>
      ∃ ancestor : Y,
        cache (model.mkQuery (addressKey .ofInternal) (ancestor, proof.head)) = some root ∧
        ChainInCache model (fun position => addressKey (.ofLeft position))
          cache leaf ancestor idxLeft proof.tail
  | .ofRight idxRight, proof =>
      ∃ ancestor : Y,
        cache (model.mkQuery (addressKey .ofInternal) (proof.head, ancestor)) = some root ∧
        ChainInCache model (fun position => addressKey (.ofRight position))
          cache leaf ancestor idxRight proof.tail

/-- The later phase added a previously uncached query whose answer is `target`. -/
private def CacheAddsValue (cache₀ cache₁ : (Query →ₒ Y).QueryCache) (target : Y) : Prop :=
  ∃ input : Query, cache₁ input = some target ∧ cache₀ input = none

omit [DecidableEq Query] [DecidableEq Address] [DecidableEq Y] in
private lemma chainInCache_mono (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (idx : SkeletonLeafIndex s)
    {cache₁ cache₂ : (Query →ₒ Y).QueryCache} {root leaf : Y}
    {proof : List.Vector Y idx.depth}
    (hle : cache₁ ≤ cache₂)
    (hchain : ChainInCache model addressKey cache₁ leaf root idx proof) :
    ChainInCache model addressKey cache₂ leaf root idx proof := by
  induction idx generalizing root with
  | ofLeaf => exact hchain
  | @ofLeft sl sr idxLeft ih =>
    obtain ⟨ancestor, hentry, hrec⟩ := hchain
    exact ⟨ancestor, hle hentry,
      ih (fun position => addressKey (.ofLeft position)) hrec⟩
  | @ofRight sl sr idxRight ih =>
    obtain ⟨ancestor, hentry, hrec⟩ := hchain
    exact ⟨ancestor, hle hentry,
      ih (fun position => addressKey (.ofRight position)) hrec⟩

omit [DecidableEq Address] [DecidableEq Y] in
private lemma chainInCache_of_mem_support_getPutativeRoot
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (idx : SkeletonLeafIndex s)
    (leaf : Y) (proof : List.Vector Y idx.depth) (root : Y)
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (hmem : (root, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle
        (AddressedMerkleTree.getPutativeRootAddressedM
          (fun position left right =>
            liftM ((Query →ₒ Y).query
              (model.mkQuery (addressKey position) (left, right))))
          idx leaf proof)).run cache₀)) :
    ChainInCache model addressKey cache₁ leaf root idx proof := by
  induction idx generalizing root cache₀ cache₁ with
  | ofLeaf =>
    simp only [AddressedMerkleTree.getPutativeRootAddressedM,
      simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff, Prod.mk.injEq] at hmem
    exact hmem.1.symm
  | @ofLeft sl sr idxLeft ih =>
    rw [show AddressedMerkleTree.getPutativeRootAddressedM
        (fun position left right =>
          liftM ((Query →ₒ Y).query
            (model.mkQuery (addressKey position) (left, right))))
        (.ofLeft idxLeft) leaf proof =
      AddressedMerkleTree.getPutativeRootAddressedM
          (fun position left right =>
            liftM ((Query →ₒ Y).query
              (model.mkQuery (addressKey (.ofLeft position)) (left, right))))
          idxLeft leaf proof.tail >>= fun ancestor =>
        liftM ((Query →ₒ Y).query
          (model.mkQuery (addressKey .ofInternal) (ancestor, proof.head))) from rfl,
      simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ancestor, cacheMid⟩, hrec, hhash⟩ := hmem
    have hentry : cache₁
        (model.mkQuery (addressKey .ofInternal) (ancestor, proof.head)) = some root := by
      exact cachingOracle_query_caches
        (model.mkQuery (addressKey .ofInternal) (ancestor, proof.head))
        cacheMid root cache₁ (by
          simpa only [HasQuery.instOfMonadLift_query, cachingOracle.simulateQ_query] using hhash)
    have hmono : cacheMid ≤ cache₁ :=
      simulateQ_cachingOracle_cache_le
        (liftM ((Query →ₒ Y).query
          (model.mkQuery (addressKey .ofInternal) (ancestor, proof.head))))
        cacheMid _ hhash
    exact ⟨ancestor, hentry,
      chainInCache_mono model (fun position => addressKey (.ofLeft position)) idxLeft hmono
        (ih (fun position => addressKey (.ofLeft position)) proof.tail ancestor
          cache₀ cacheMid hrec)⟩
  | @ofRight sl sr idxRight ih =>
    rw [show AddressedMerkleTree.getPutativeRootAddressedM
        (fun position left right =>
          liftM ((Query →ₒ Y).query
            (model.mkQuery (addressKey position) (left, right))))
        (.ofRight idxRight) leaf proof =
      AddressedMerkleTree.getPutativeRootAddressedM
          (fun position left right =>
            liftM ((Query →ₒ Y).query
              (model.mkQuery (addressKey (.ofRight position)) (left, right))))
          idxRight leaf proof.tail >>= fun ancestor =>
        liftM ((Query →ₒ Y).query
          (model.mkQuery (addressKey .ofInternal) (proof.head, ancestor))) from rfl,
      simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ancestor, cacheMid⟩, hrec, hhash⟩ := hmem
    have hentry : cache₁
        (model.mkQuery (addressKey .ofInternal) (proof.head, ancestor)) = some root := by
      exact cachingOracle_query_caches
        (model.mkQuery (addressKey .ofInternal) (proof.head, ancestor))
        cacheMid root cache₁ (by
          simpa only [HasQuery.instOfMonadLift_query, cachingOracle.simulateQ_query] using hhash)
    have hmono : cacheMid ≤ cache₁ :=
      simulateQ_cachingOracle_cache_le
        (liftM ((Query →ₒ Y).query
          (model.mkQuery (addressKey .ofInternal) (proof.head, ancestor))))
        cacheMid _ hhash
    exact ⟨ancestor, hentry,
      chainInCache_mono model (fun position => addressKey (.ofRight position)) idxRight hmono
        (ih (fun position => addressKey (.ofRight position)) proof.tail ancestor
          cache₀ cacheMid hrec)⟩

omit [DecidableEq Address] in
private lemma chainInCache_of_mem_support_verifyOpening
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (idx : SkeletonLeafIndex s)
    (leaf root : Y) (proof : List.Vector Y idx.depth)
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (hmem : (true, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle
        (verifyOpening model addressKey idx leaf root proof)).run cache₀)) :
    ChainInCache model addressKey cache₁ leaf root idx proof := by
  unfold verifyOpening at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨putativeRoot, cacheMid⟩, hroot, hfinal⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq] at hfinal
  obtain ⟨hroot_eq, rfl⟩ := hfinal
  have hputative : putativeRoot = root := by
    simpa only [beq_iff_eq] using hroot_eq.symm
  subst root
  exact chainInCache_of_mem_support_getPutativeRoot model addressKey
    idx leaf proof putativeRoot cache₀ cache₁ hroot

omit [DecidableEq Query] [DecidableEq Y] in
private lemma responseInjectiveOn_of_cache_noCollision
    (log : (Query →ₒ Y).QueryLog) (cache : (Query →ₒ Y).QueryCache)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hno : ¬ CacheHasCollision cache) :
    MerkleTreeExtractor.ResponseInjectiveOn log := by
  intro entry₁ hentry₁ entry₂ hentry₂ hresponse
  exact cache_lookup_eq_of_noCollision hno (hlogCache entry₁ hentry₁)
    ⟨entry₂.2, hlogCache entry₂ hentry₂, heq_of_eq hresponse.symm⟩

omit [DecidableEq Query] in
private lemma extractor_tree_internal_of_children_eq_some
    (model : NodeQueryModel Query Address Y)
    (left right : Skeleton)
    (addressKey : SkeletonInternalIndex (.internal left right) → Address)
    (log : (Query →ₒ Y).QueryLog) (root leftRoot rightRoot : Y)
    (hchildren : MerkleTreeExtractor.children model.view log (addressKey .ofInternal) root =
      some (leftRoot, rightRoot)) :
    MerkleTreeExtractor.tree model.view (.internal left right) addressKey log root =
      FullData.internal (some root)
        (MerkleTreeExtractor.tree model.view left
          (fun position => addressKey (.ofLeft position)) log leftRoot)
        (MerkleTreeExtractor.tree model.view right
          (fun position => addressKey (.ofRight position)) log rightRoot) := by
  simp [MerkleTreeExtractor.tree, MerkleTreeExtractor.treeAt, hchildren]

omit [DecidableEq Query] in
private lemma fresh_extractedTarget_of_extractor_disagreement
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (idx : SkeletonLeafIndex s)
    (log : (Query →ₒ Y).QueryLog) (cacheCommit cacheFinal : (Query →ₒ Y).QueryCache)
    (root leaf : Y) (proof : List.Vector Y idx.depth)
    (hlogCache : ∀ entry ∈ log, cacheCommit entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cacheCommit input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hno : ¬ CacheHasCollision cacheCommit)
    (hmono : cacheCommit ≤ cacheFinal)
    (hchain : ChainInCache model addressKey cacheFinal leaf root idx proof)
    (hdisagree :
      some leaf ≠ (MerkleTreeExtractor.tree model.view s addressKey log root).get
        idx.toNodeIndex ∨
      proof.toList.map some ≠
        (generateProof (MerkleTreeExtractor.tree model.view s addressKey log root) idx).toList) :
    ∃ target ∈ extractedTargets model s addressKey log root,
      CacheAddsValue cacheCommit cacheFinal target := by
  induction idx generalizing root with
  | ofLeaf =>
      simp only [ChainInCache] at hchain
      subst root
      have hleaf :
          some leaf ≠
            (MerkleTreeExtractor.tree model.view .leaf addressKey log leaf).get
              SkeletonLeafIndex.ofLeaf.toNodeIndex :=
        hdisagree.resolve_right (by simp [generateProof])
      exact (hleaf rfl).elim
  | @ofLeft sl sr idxLeft ih =>
      obtain ⟨ancestor, hquery, hchainTail⟩ := hchain
      let query := model.mkQuery (addressKey .ofInternal) (ancestor, proof.head)
      cases hqueryCommit : cacheCommit query with
      | none =>
          exact ⟨root,
            MerkleTreeExtractor.root_mem_targets model.view (.internal sl sr)
              addressKey log root,
            query, hquery, hqueryCommit⟩
      | some value =>
          have hvalueFinal := hmono hqueryCommit
          rw [hquery] at hvalueFinal
          obtain rfl := Option.some.inj hvalueFinal
          obtain ⟨entry, hentry, hinput, houtput⟩ :=
            hcacheLog query root hqueryCommit
          have hentry' : (⟨entry.1, root⟩ : (_query : Query) × Y) ∈ log := by
            convert hentry using 1
            exact Sigma.ext rfl (heq_of_eq houtput.symm)
          have haddress : model.view.address entry.1 = addressKey .ofInternal := by
            rw [hinput, model.address_mkQuery]
          have hviewInput : model.view.input entry.1 = (ancestor, proof.head) := by
            rw [hinput, model.input_mkQuery]
          have hchildren :
              MerkleTreeExtractor.children model.view log (addressKey .ofInternal) root =
                some (ancestor, proof.head) := by
            rw [← hviewInput]
            exact MerkleTreeExtractor.children_eq_some_of_mem_of_responseInjectiveOn
              model.view log (addressKey .ofInternal) root entry.1 haddress hentry'
                (responseInjectiveOn_of_cache_noCollision log cacheCommit hlogCache hno)
          have hchildDisagree :
              some leaf ≠
                  (MerkleTreeExtractor.tree model.view sl
                    (fun position => addressKey (.ofLeft position)) log ancestor).get
                    idxLeft.toNodeIndex ∨
                proof.tail.toList.map some ≠
                  (generateProof
                    (MerkleTreeExtractor.tree model.view sl
                      (fun position => addressKey (.ofLeft position)) log ancestor)
                    idxLeft).toList := by
            rw [extractor_tree_internal_of_children_eq_some model sl sr
              addressKey log root ancestor proof.head hchildren] at hdisagree
            rcases hdisagree with hleaf | hproof
            · exact Or.inl (by
                simpa [SkeletonLeafIndex.toNodeIndex, FullData.get] using hleaf)
            · refine Or.inr fun htail => hproof ?_
              have hsibling :
                  (MerkleTreeExtractor.tree model.view sr
                    (fun position => addressKey (.ofRight position)) log proof.head).getRootValue =
                    some proof.head :=
                MerkleTreeExtractor.treeAt_getRootValue model.view sr
                  (fun position => addressKey (.ofRight position)) log proof.head
              have hproofList : proof.toList = proof.head :: proof.tail.toList := by
                rw [← proof.cons_head_tail]
                rfl
              rw [hproofList, List.map_cons]
              change some proof.head :: proof.tail.toList.map some =
                (MerkleTreeExtractor.tree model.view sr
                  (fun position => addressKey (.ofRight position)) log proof.head).getRootValue ::
                  (generateProof
                    (MerkleTreeExtractor.tree model.view sl
                      (fun position => addressKey (.ofLeft position)) log ancestor)
                    idxLeft).toList
              rw [hsibling, htail]
          obtain ⟨target, htarget, hfresh⟩ :=
            ih (fun position => addressKey (.ofLeft position)) ancestor proof.tail
              hchainTail hchildDisagree
          refine ⟨target, ?_, hfresh⟩
          change target ∈ MerkleTreeExtractor.targets model.view (.internal sl sr)
            addressKey log root
          rw [MerkleTreeExtractor.targets_internal_of_children_eq_some model.view sl sr
            addressKey log root ancestor proof.head hchildren]
          simp [htarget]
  | @ofRight sl sr idxRight ih =>
      obtain ⟨ancestor, hquery, hchainTail⟩ := hchain
      let query := model.mkQuery (addressKey .ofInternal) (proof.head, ancestor)
      cases hqueryCommit : cacheCommit query with
      | none =>
          exact ⟨root,
            MerkleTreeExtractor.root_mem_targets model.view (.internal sl sr)
              addressKey log root,
            query, hquery, hqueryCommit⟩
      | some value =>
          have hvalueFinal := hmono hqueryCommit
          rw [hquery] at hvalueFinal
          obtain rfl := Option.some.inj hvalueFinal
          obtain ⟨entry, hentry, hinput, houtput⟩ :=
            hcacheLog query root hqueryCommit
          have hentry' : (⟨entry.1, root⟩ : (_query : Query) × Y) ∈ log := by
            convert hentry using 1
            exact Sigma.ext rfl (heq_of_eq houtput.symm)
          have haddress : model.view.address entry.1 = addressKey .ofInternal := by
            rw [hinput, model.address_mkQuery]
          have hviewInput : model.view.input entry.1 = (proof.head, ancestor) := by
            rw [hinput, model.input_mkQuery]
          have hchildren :
              MerkleTreeExtractor.children model.view log (addressKey .ofInternal) root =
                some (proof.head, ancestor) := by
            rw [← hviewInput]
            exact MerkleTreeExtractor.children_eq_some_of_mem_of_responseInjectiveOn
              model.view log (addressKey .ofInternal) root entry.1 haddress hentry'
                (responseInjectiveOn_of_cache_noCollision log cacheCommit hlogCache hno)
          have hchildDisagree :
              some leaf ≠
                  (MerkleTreeExtractor.tree model.view sr
                    (fun position => addressKey (.ofRight position)) log ancestor).get
                    idxRight.toNodeIndex ∨
                proof.tail.toList.map some ≠
                  (generateProof
                    (MerkleTreeExtractor.tree model.view sr
                      (fun position => addressKey (.ofRight position)) log ancestor)
                    idxRight).toList := by
            rw [extractor_tree_internal_of_children_eq_some model sl sr
              addressKey log root proof.head ancestor hchildren] at hdisagree
            rcases hdisagree with hleaf | hproof
            · exact Or.inl (by
                simpa [SkeletonLeafIndex.toNodeIndex, FullData.get] using hleaf)
            · refine Or.inr fun htail => hproof ?_
              have hsibling :
                  (MerkleTreeExtractor.tree model.view sl
                    (fun position => addressKey (.ofLeft position)) log proof.head).getRootValue =
                    some proof.head :=
                MerkleTreeExtractor.treeAt_getRootValue model.view sl
                  (fun position => addressKey (.ofLeft position)) log proof.head
              have hproofList : proof.toList = proof.head :: proof.tail.toList := by
                rw [← proof.cons_head_tail]
                rfl
              rw [hproofList, List.map_cons]
              change some proof.head :: proof.tail.toList.map some =
                (MerkleTreeExtractor.tree model.view sl
                  (fun position => addressKey (.ofLeft position)) log proof.head).getRootValue ::
                  (generateProof
                    (MerkleTreeExtractor.tree model.view sr
                      (fun position => addressKey (.ofRight position)) log ancestor)
                    idxRight).toList
              rw [hsibling, htail]
          obtain ⟨target, htarget, hfresh⟩ :=
            ih (fun position => addressKey (.ofRight position)) ancestor proof.tail
              hchainTail hchildDisagree
          refine ⟨target, ?_, hfresh⟩
          change target ∈ MerkleTreeExtractor.targets model.view (.internal sl sr)
            addressKey log root
          rw [MerkleTreeExtractor.targets_internal_of_children_eq_some model.view sl sr
            addressKey log root proof.head ancestor hchildren]
          simp [htarget]

/-- Pointwise deterministic reduction for the cached suffix: once the commit cache is
collision-free, a winning opening must add a fresh cache entry whose answer is one of the
labels fixed by the logged commit. -/
private lemma extractability_rest_win_implies_fresh_target_of_invariants
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (𝒜 : Adversary Query Y s)
    {root : Y} {aux : 𝒜.AuxState} {log : (Query →ₒ Y).QueryLog}
    {cacheCommit : (Query →ₒ Y).QueryCache}
    (hlogCache : ∀ entry ∈ log, cacheCommit entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cacheCommit input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hno : ¬ CacheHasCollision cacheCommit) :
    ∀ z ∈ support ((simulateQ (Query →ₒ Y).cachingOracle
        (extractabilityRest model addressKey 𝒜 root aux log)).run cacheCommit),
      AdversaryWinsExtractabilityGame z.1 →
      ∃ target ∈ extractedTargets model s addressKey log root,
        CacheAddsValue cacheCommit z.2 target := by
  intro z hz hwin
  have hmono : cacheCommit ≤ z.2 :=
    simulateQ_cachingOracle_cache_le (extractabilityRest model addressKey 𝒜 root aux log)
      cacheCommit z hz
  unfold extractabilityRest at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨idx, leaf, proof⟩, cacheOpen⟩, hopen, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨verified, cacheFinal⟩, hverify, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  have hcacheFinal : z.2 = cacheFinal := congrArg Prod.snd hz
  rw [hz] at hwin
  simp only [AdversaryWinsExtractabilityGame, AdversaryWinsExtractabilityInner] at hwin
  obtain ⟨hverified, hdisagree⟩ := hwin
  subst verified
  have hchain : ChainInCache model addressKey cacheFinal leaf root idx proof :=
    chainInCache_of_mem_support_verifyOpening model addressKey
      idx leaf root proof cacheOpen cacheFinal hverify
  rw [hcacheFinal] at hmono
  rw [hcacheFinal]
  exact fresh_extractedTarget_of_extractor_disagreement model addressKey idx log
    cacheCommit cacheFinal root leaf proof hlogCache hcacheLog hno hmono hchain hdisagree

/-- Pointwise suffix bound in terms of the actual extracted-tree size and the residual
opening budget. Its hypotheses are precisely the log/cache invariants maintained by the
combined caching-and-logging interpreter used in the stopping-time proof below. -/
private lemma extractability_rest_noCollision_le_of_opening_bound
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : Adversary Query Y s) (openingBound targetBound : ℕ)
    {root : Y} {aux : 𝒜.AuxState} {log : (Query →ₒ Y).QueryLog}
    {cacheCommit : (Query →ₒ Y).QueryCache}
    (hopening : IsTotalQueryBound (𝒜.opening aux) openingBound)
    (hlogCache : ∀ entry ∈ log, cacheCommit entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cacheCommit input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (htargets : (extractedTargets model s addressKey log root).toFinset.card ≤ targetBound)
    (hno : ¬ CacheHasCollision cacheCommit) :
    Pr[fun z => AdversaryWinsExtractabilityGame z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (extractabilityRest model addressKey 𝒜 root aux log)).run cacheCommit] ≤
      ((targetBound * (openingBound + s.depth) : ℕ) : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
  let targets := (extractedTargets model s addressKey log root).toFinset
  have hrest : IsTotalQueryBound
      (extractabilityRest model addressKey 𝒜 root aux log) (openingBound + s.depth) := by
    unfold extractabilityRest
    exact isTotalQueryBound_bind (n₁ := openingBound) (n₂ := s.depth)
      hopening fun ⟨idx, leaf, proof⟩ =>
        isTotalQueryBound_bind (n₁ := s.depth) (n₂ := 0)
          (verifyOpening_isTotalQueryBound_skeleton_depth model addressKey idx leaf root proof)
          fun _ => trivial
  calc
    Pr[fun z => AdversaryWinsExtractabilityGame z.1 |
        (simulateQ (Query →ₒ Y).cachingOracle
          (extractabilityRest model addressKey 𝒜 root aux log)).run cacheCommit]
      ≤ Pr[fun z => ∃ target ∈ targets, ∃ input : Query, ∃ value : Y,
            z.2 input = some value ∧ cacheCommit input = none ∧ value = target |
          (simulateQ (Query →ₒ Y).cachingOracle
            (extractabilityRest model addressKey 𝒜 root aux log)).run cacheCommit] := by
        apply probEvent_mono
        intro z hz hwin
        obtain ⟨target, htarget, input, hfinal, hinitial⟩ :=
          extractability_rest_win_implies_fresh_target_of_invariants
            model addressKey 𝒜 hlogCache hcacheLog hno z hz hwin
        exact ⟨target, by simpa [targets] using htarget,
          input, target, hfinal, hinitial, rfl⟩
    _ ≤ ((targets.card * (openingBound + s.depth) : ℕ) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
        exact OracleComp.probEvent_cache_hits_targets_le_of_noCollision_homogeneous
          (extractabilityRest model addressKey 𝒜 root aux log)
          (openingBound + s.depth) hrest targets cacheCommit hno
    _ ≤ ((targetBound * (openingBound + s.depth) : ℕ) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
        gcongr

/-- Stopping-time induction for the shared ROM experiment. The induction follows the syntax
of the still-running commit computation. A cache hit consumes one unit of the remaining
combined adversary budget; a miss additionally pays for the at most `cached` responses that
would create a collision. When the commit stops, the suffix theorem pays for at most
`targetCount * (remaining + depth)` fresh-target opportunities. -/
private lemma extractabilityRunFrom_le_potential
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (𝒜 : Adversary Query Y s)
    (commit : OracleComp (Query →ₒ Y) (Y × 𝒜.AuxState))
    (remaining cached : ℕ)
    (hbound : IsTotalQueryBound
      (commit >>= fun x => 𝒜.opening x.2 >>= fun _ => pure ()) remaining)
    (cache : (Query →ₒ Y).QueryCache) (log : (Query →ₒ Y).QueryLog)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset Query, keys.card ≤ cached ∧
      ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value) :
    Pr[fun z => AdversaryWinsExtractabilityGame z.1 |
      extractabilityRunFrom model addressKey 𝒜 commit cache log] ≤
      (extractabilityExactPotential (2 * s.leafCount - 1) s.depth remaining cached : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
  let targetCount := fun keyCount => min (2 * s.leafCount - 1) (2 * keyCount + 1)
  have hgeneric := probEvent_adaptivePrefixRunFrom_le
    (suffix := fun x queryLog =>
      extractabilityRest model addressKey 𝒜 x.1 x.2 queryLog)
    (continuation := fun x => 𝒜.opening x.2 >>= fun _ => pure ())
    (win := AdversaryWinsExtractabilityGame) (targetCount := targetCount)
    (overhead := s.depth) commit remaining cached hbound cache log hno hcacheBound
    hlogCache hcacheLog
    (fun x terminalRemaining terminalCached terminalCache terminalLog hopening hno'
      hcacheBound' hlogCache' hcacheLog' => by
        have hopening' : IsTotalQueryBound (𝒜.opening x.2) terminalRemaining := by
          have hmapped : IsTotalQueryBound
              ((fun _ => ()) <$> 𝒜.opening x.2) terminalRemaining := by
            simpa using hopening
          exact (isQueryBound_map_iff (𝒜.opening x.2) (fun _ => ())
            terminalRemaining _ _).mp hmapped
        have htargets :
            (extractedTargets model s addressKey terminalLog x.1).toFinset.card ≤
              targetCount terminalCached := by
          obtain ⟨keys, hkeysCard, hkeysMem⟩ := hcacheBound'
          have htree :
              (extractedTargets model s addressKey terminalLog x.1).toFinset.card ≤
              2 * s.leafCount - 1 := by
            calc
              (extractedTargets model s addressKey terminalLog x.1).toFinset.card ≤
                  (extractedTargets model s addressKey terminalLog x.1).length :=
                    List.toFinset_card_le _
              _ ≤ 2 * s.leafCount - 1 :=
                extractedTargets_length_le model s addressKey terminalLog x.1
          have hcache :
              (extractedTargets model s addressKey terminalLog x.1).toFinset.card ≤
              2 * terminalCached + 1 :=
            (extractedTargets_toFinset_card_le_cacheKeys model s addressKey terminalLog
              x.1 keys hlogCache' hkeysMem).trans (by omega)
          exact le_min htree hcache
        exact extractability_rest_noCollision_le_of_opening_bound
          model addressKey 𝒜 terminalRemaining (targetCount terminalCached)
          (root := x.1) (aux := x.2)
          hopening' hlogCache' hcacheLog' htargets hno')
  simpa only [extractabilityRunFrom, extractabilityExactPotential, targetCount]
    using hgeneric

/-- Initialize the stopping-time induction at the empty cache and empty log, then transport
the combined caching/logging semantics back to `extractabilityGame`. -/
private lemma extractability_win_le_stopping_bound
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : Adversary Query Y s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    Pr[AdversaryWinsExtractabilityGame | extractabilityGame model addressKey 𝒜] ≤
      (extractabilityExactPotential (2 * s.leafCount - 1) s.depth qb 0 : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
  have hmain : Pr[fun z => AdversaryWinsExtractabilityGame z.1 |
      extractabilityRunFrom model addressKey 𝒜 𝒜.commit ∅ []] ≤
      (extractabilityExactPotential (2 * s.leafCount - 1) s.depth qb 0 : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
    apply extractabilityRunFrom_le_potential model addressKey 𝒜 𝒜.commit qb 0 h ∅ []
    · intro hcollision
      obtain ⟨_, _, _, _, _, hcached, _, _⟩ := hcollision
      simp at hcached
    · exact ⟨∅, by simp, fun input hinput => absurd (by simp : (∅ :
        (Query →ₒ Y).QueryCache) input = none) hinput⟩
    · simp
    · simp
  rw [extractabilityRunFrom, adaptivePrefixRunFrom,
    cachingLoggingOracle.run_simulateQ_eq_map_run_simulateQ_withQueryLog] at hmain
  simp only [List.nil_append] at hmain
  rw [extractabilityGame, OracleSpec.withCacheOverlay, StateT.run'_eq,
    extractabilityInner_eq_commit_bind_rest model addressKey, simulateQ_bind, StateT.run_bind,
    probEvent_map]
  simpa [Function.comp_def] using hmain

/-- Unrelaxed stopping-time error numerator for Merkle extractability in the shared ROM.
The finite maximum ranges over the number `commitMisses` of fresh, distinct commit inputs.
Repeated commit queries consume the total budget but do not increase `commitMisses` or the
cache size. -/
def extractabilityROMErrorNumerator (s : Skeleton) (qb : ℕ) : ℕ :=
  (Finset.range (qb + 1)).sup fun commitMisses =>
    commitMisses.choose 2 +
      min (2 * s.leafCount - 1) (2 * commitMisses + 1) *
        (qb - commitMisses + s.depth)

/-- **Unrelaxed finite-maximum ROM extractability bound for inductive Merkle trees.**

For a two-phase adversary with structural total query bound `qb`, extraction failure in the
single shared lazy random function is at most `extractabilityROMErrorNumerator s qb / |Y|`.
The finite maximum tracks fresh commit inputs rather than conditioning on a realized phase
length. The proof is therefore valid when the adversary adaptively decides when to stop its
commit phase and when it repeats cached queries. -/
theorem extractability_rom_bound
    [Fintype Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : Adversary Query Y s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    Pr[AdversaryWinsExtractabilityGame | extractabilityGame model addressKey 𝒜] ≤
      (extractabilityROMErrorNumerator s qb : ENNReal) *
        (Fintype.card Y : ENNReal)⁻¹ := by
  have hbound := extractability_win_le_stopping_bound model addressKey 𝒜 qb h
  have hcard : Nat.card Y = Fintype.card Y := Nat.card_eq_fintype_card
  simpa only [extractabilityExactPotential, extractabilityEnergy,
    adaptivePrefixPotential, adaptivePrefixEnergy,
    extractabilityROMErrorNumerator, Nat.mul_zero, Nat.zero_add, hcard] using hbound

private lemma target_mul_sub_add_choose_le_choose
    (targetCount qb commitMisses : ℕ)
    (hqb : 2 * targetCount + 1 ≤ qb) (hmisses : commitMisses ≤ qb) :
    targetCount * (qb - commitMisses) + commitMisses.choose 2 ≤ qb.choose 2 := by
  rw [Nat.choose_two_right qb, Nat.le_div_iff_mul_le (by omega : 0 < 2)]
  have hchoose : 2 * commitMisses.choose 2 ≤ commitMisses * (commitMisses - 1) := by
    rw [Nat.choose_two_right]
    simpa [mul_comm] using
      Nat.div_mul_le_self (commitMisses * (commitMisses - 1)) 2
  have hqbPred : qb - 1 + 1 = qb := by omega
  have hqbMisses : qb - commitMisses + commitMisses = qb := by omega
  by_cases hzero : commitMisses = 0
  · subst commitMisses
    norm_num
    nlinarith
  have hmissesPred : commitMisses - 1 + 1 = commitMisses := by omega
  have hpoly : 2 * targetCount * (qb - commitMisses) +
      commitMisses * (commitMisses - 1) ≤ qb * (qb - 1) := by
    nlinarith
  nlinarith

private lemma choose_le_target_mul
    (targetCount commitMisses : ℕ) (hmisses : commitMisses ≤ 2 * targetCount + 1) :
    commitMisses.choose 2 ≤ targetCount * commitMisses := by
  rw [Nat.choose_two_right]
  apply Nat.div_le_of_le_mul
  have hpred : commitMisses - 1 ≤ 2 * targetCount := by omega
  have hmul := Nat.mul_le_mul_left commitMisses hpred
  nlinarith

private lemma extractabilityROMErrorNumerator_le_coarse (s : Skeleton) (qb : ℕ) :
    extractabilityROMErrorNumerator s qb ≤
      max ((2 * s.leafCount - 1) * qb) (qb.choose 2) +
        (2 * s.leafCount - 1) * s.depth := by
  let targetCount := 2 * s.leafCount - 1
  unfold extractabilityROMErrorNumerator
  apply Finset.sup_le
  intro commitMisses hcommitMisses
  have hmisses : commitMisses ≤ qb := by
    simp only [Finset.mem_range] at hcommitMisses
    omega
  by_cases hlarge : 2 * targetCount + 1 ≤ qb
  · have hcap : min targetCount (2 * commitMisses + 1) ≤ targetCount := min_le_left _ _
    calc
      commitMisses.choose 2 + min targetCount (2 * commitMisses + 1) *
            (qb - commitMisses + s.depth)
        ≤ commitMisses.choose 2 + targetCount * (qb - commitMisses + s.depth) := by
          gcongr
      _ = (targetCount * (qb - commitMisses) + commitMisses.choose 2) +
            targetCount * s.depth := by ring
      _ ≤ qb.choose 2 + targetCount * s.depth :=
        Nat.add_le_add_right
          (target_mul_sub_add_choose_le_choose targetCount qb commitMisses hlarge hmisses) _
      _ ≤ max (targetCount * qb) (qb.choose 2) + targetCount * s.depth :=
        Nat.add_le_add_right (le_max_right _ _) _
  · have hcap : min targetCount (2 * commitMisses + 1) ≤ targetCount := min_le_left _ _
    have hchoose : commitMisses.choose 2 ≤ targetCount * commitMisses :=
      choose_le_target_mul targetCount commitMisses (by omega)
    calc
      commitMisses.choose 2 + min targetCount (2 * commitMisses + 1) *
            (qb - commitMisses + s.depth)
        ≤ targetCount * commitMisses + targetCount * (qb - commitMisses + s.depth) :=
          Nat.add_le_add hchoose (by gcongr)
      _ = targetCount * (qb + s.depth) := by
        rw [Nat.mul_add, Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_add]
        congr 2
        omega
      _ = targetCount * qb + targetCount * s.depth := by rw [Nat.mul_add]
      _ ≤ max (targetCount * qb) (qb.choose 2) + targetCount * s.depth :=
        Nat.add_le_add_right (le_max_left _ _) _

/-- Unconditional two-endpoint relaxation of the unrelaxed finite maximum. This is the direct
counterpart of the maximum appearing before the final case split in the source proof. -/
theorem extractability_rom_bound_coarse
    [Fintype Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : Adversary Query Y s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    Pr[AdversaryWinsExtractabilityGame | extractabilityGame model addressKey 𝒜] ≤
      ((max ((2 * s.leafCount - 1) * qb) (qb.choose 2) +
        (2 * s.leafCount - 1) * s.depth : ℕ) : ENNReal) *
        (Fintype.card Y : ENNReal)⁻¹ := by
  refine (extractability_rom_bound model addressKey 𝒜 qb h).trans ?_
  gcongr
  exact_mod_cast extractabilityROMErrorNumerator_le_coarse s qb

/-- Once `qb ≥ 2T + 1`, the birthday endpoint dominates the other coarse endpoint. -/
theorem extractability_rom_bound_birthday_dominates
    [Fintype Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : Adversary Query Y s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb)
    (hqb : 2 * (2 * s.leafCount - 1) + 1 ≤ qb) :
    Pr[AdversaryWinsExtractabilityGame | extractabilityGame model addressKey 𝒜] ≤
      ((qb.choose 2 + (2 * s.leafCount - 1) * s.depth : ℕ) : ENNReal) *
        (Fintype.card Y : ENNReal)⁻¹ := by
  let targetCount := 2 * s.leafCount - 1
  have htwice : 2 * targetCount ≤ qb - 1 := by omega
  have hmul : qb * (2 * targetCount) ≤ qb * (qb - 1) :=
    Nat.mul_le_mul_left qb htwice
  have hdominates : targetCount * qb ≤ qb.choose 2 := by
    rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by omega : 0 < 2)]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
  simpa only [targetCount, max_eq_right hdominates] using
    extractability_rom_bound_coarse model addressKey 𝒜 qb h

/-- Textbook-shaped quadratic corollary. Besides birthday dominance, it suffices that
`2·T·depth ≤ qb`; these two explicit conditions are weaker than the convenient single
condition used in the Chiesa–Yogev presentation. -/
theorem extractability_rom_bound_quadratic
    [Fintype Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (𝒜 : Adversary Query Y s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb)
    (hdominance : 2 * (2 * s.leafCount - 1) + 1 ≤ qb)
    (hdepth : 2 * (2 * s.leafCount - 1) * s.depth ≤ qb) :
    Pr[AdversaryWinsExtractabilityGame | extractabilityGame model addressKey 𝒜] ≤
      (qb : ENNReal) ^ 2 / (2 * Fintype.card Y) := by
  let targetCount := 2 * s.leafCount - 1
  let numerator := qb.choose 2 + targetCount * s.depth
  have hchoose : 2 * qb.choose 2 ≤ qb * (qb - 1) := by
    rw [Nat.choose_two_right]
    simpa only [mul_comm] using Nat.div_mul_le_self (qb * (qb - 1)) 2
  have hqbpos : 0 < qb := by omega
  have hnat : 2 * numerator ≤ qb ^ 2 := by
    calc
      2 * numerator = 2 * qb.choose 2 + 2 * targetCount * s.depth := by
        simp only [numerator]
        ring
      _ ≤ qb * (qb - 1) + qb := Nat.add_le_add hchoose (by
        simpa only [targetCount] using hdepth)
      _ = qb * ((qb - 1) + 1) := by ring
      _ = qb ^ 2 := by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hqbpos.ne')]; ring
  have hbase := extractability_rom_bound_birthday_dominates
    model addressKey 𝒜 qb h hdominance
  refine hbase.trans ?_
  change (numerator : ENNReal) * (Fintype.card Y : ENNReal)⁻¹ ≤
    (qb : ENNReal) ^ 2 / (2 * Fintype.card Y)
  calc
    (numerator : ENNReal) * (Fintype.card Y : ENNReal)⁻¹ =
        (numerator : ENNReal) / Fintype.card Y := by
      rw [ENNReal.div_eq_inv_mul, mul_comm]
    _ = ((2 : ENNReal) * numerator) / (2 * Fintype.card Y) := by
      symm
      exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)
    _ ≤ (qb : ENNReal) ^ 2 / (2 * Fintype.card Y) := by
      apply ENNReal.div_le_div_right
      exact_mod_cast hnat

end ExtractabilityGame

end MerkleTreeExtractability
