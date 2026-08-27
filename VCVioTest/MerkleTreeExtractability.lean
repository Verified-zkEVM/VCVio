/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.Extractability

/-!
# Inductive Merkle Extractability Canaries

These examples pin the semantic boundary between raw `OracleComp` syntax, where repeated
queries sample independently, and `extractabilityGame`, where the full experiment is run
through one shared cache.
-/

@[expose] public section

open OracleComp OracleSpec

namespace VCVioTest.MerkleTreeExtractability

noncomputable local instance : IsUniformSpec (InductiveMerkleTree.spec Bool) :=
  IsUniformSpec.ofFintypeInhabited (InductiveMerkleTree.spec Bool)

def repeatedQuery : OracleComp (InductiveMerkleTree.spec Bool) (Bool × Bool) := do
  let first ← ((InductiveMerkleTree.spec Bool).query (false, false) :
    OracleComp (InductiveMerkleTree.spec Bool) Bool)
  let second ← ((InductiveMerkleTree.spec Bool).query (false, false) :
    OracleComp (InductiveMerkleTree.spec Bool) Bool)
  return (first, second)

/-- Raw `OracleComp` semantics permit two different answers to the same input. -/
example : (false, true) ∈ support repeatedQuery := by
  simp [repeatedQuery]

/-- The shared cache makes the same repeated input return the same answer. -/
example : ∀ result ∈ support
    (Prod.fst <$> (simulateQ (InductiveMerkleTree.spec Bool).cachingOracle repeatedQuery).run ∅),
    result.1 = result.2 := by
  intro result hresult
  have hcases : (false, false) = result ∨ (true, true) = result := by
    simpa [repeatedQuery] using hresult
  rcases hcases with rfl | rfl <;> rfl

/-- `extractabilityGame` is exactly the cached interpretation of its oracle syntax, with
the final implementation cache hidden from consumers. -/
example {s : BinaryTree.Skeleton} (adversary : InductiveMerkleTree.Adversary Bool s) :
    InductiveMerkleTree.extractabilityGame adversary =
      (InductiveMerkleTree.spec Bool).withCacheOverlay ∅
        (InductiveMerkleTree.extractabilityInner adversary) := rfl

def depthOneSkeleton : BinaryTree.Skeleton :=
  .internal .leaf .leaf

def leftIndex : BinaryTree.SkeletonLeafIndex depthOneSkeleton :=
  .ofLeft .ofLeaf

def leftProof : List.Vector Bool leftIndex.depth :=
  ⟨[true], rfl⟩

@[simp] private lemma leftProof_head : leftProof.head = true := rfl

def rightIndex : BinaryTree.SkeletonLeafIndex depthOneSkeleton :=
  .ofRight .ofLeaf

def rightProof : List.Vector Bool rightIndex.depth :=
  ⟨[false], rfl⟩

@[simp] private lemma rightProof_head : rightProof.head = false := rfl

abbrev depthOneAdversary : InductiveMerkleTree.Adversary Bool depthOneSkeleton where
  AuxState := Unit
  commit := do
    let root ← ((InductiveMerkleTree.spec Bool).query (false, true) :
      OracleComp (InductiveMerkleTree.spec Bool) Bool)
    return (root, ())
  opening _ := do
    let answer ← ((InductiveMerkleTree.spec Bool).query (false, true) :
      OracleComp (InductiveMerkleTree.spec Bool) Bool)
    if answer then
      return ⟨rightIndex, true, rightProof⟩
    else
      return ⟨leftIndex, false, leftProof⟩

private lemma depthOneCommit_withQueryLog_eq :
    depthOneAdversary.commit.withQueryLog =
      (((InductiveMerkleTree.spec Bool).query (false, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun root =>
        pure ((root, ()), [⟨(false, true), root⟩])) := by
  change OracleComp.withQueryLog (((fun root => (root, ())) <$>
      ((InductiveMerkleTree.spec Bool).query (false, true) :
        OracleComp (InductiveMerkleTree.spec Bool) Bool))) = _
  rw [map_eq_bind_pure_comp, OracleComp.withQueryLog_bind,
    OracleComp.withQueryLog_query]
  simp

private lemma depthOneCommit_cached_eq :
    (simulateQ (InductiveMerkleTree.spec Bool).cachingOracle
      depthOneAdversary.commit.withQueryLog).run ∅ =
      (((InductiveMerkleTree.spec Bool).query (false, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun root =>
        pure (((root, ()), [⟨(false, true), root⟩]),
          (∅ : (InductiveMerkleTree.spec Bool).QueryCache).cacheQuery
            (false, true) root)) := by
  rw [depthOneCommit_withQueryLog_eq]
  change (simulateQ (InductiveMerkleTree.spec Bool).cachingOracle
      (((InductiveMerkleTree.spec Bool).query (false, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun root =>
        pure ((root, ()),
          ([⟨(false, true), root⟩] : (InductiveMerkleTree.spec Bool).QueryLog)))).run ∅ = _
  rw [simulateQ_bind, StateT.run_bind, cachingOracle.simulateQ_query,
    cachingOracle.run_none (by rfl)]
  simp

/-- The commit prefix records the hash input once for the extractor, with the answer installed
in the shared cache before the same input is repeated during opening and verification. -/
example (z : ((Bool × Unit) × (InductiveMerkleTree.spec Bool).QueryLog) ×
    (InductiveMerkleTree.spec Bool).QueryCache)
    (hz : z ∈ support ((simulateQ (InductiveMerkleTree.spec Bool).cachingOracle
      depthOneAdversary.commit.withQueryLog).run ∅)) :
    z.1.2 = [⟨(false, true), z.1.1.1⟩] ∧
      z.2 (false, true) = some z.1.1.1 := by
  rw [depthOneCommit_cached_eq] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨root, _, hz⟩ := hz
  rw [mem_support_pure_iff] at hz
  subst z
  constructor
  · rfl
  · change ((∅ : (InductiveMerkleTree.spec Bool).QueryCache).cacheQuery
      (false, true) root) (false, true) = some root
    exact QueryCache.cacheQuery_self _ _ _

def expectedTree (root : Bool) :
    BinaryTree.FullData (Option Bool) depthOneSkeleton :=
  .internal (some root) (.leaf (some false)) (.leaf (some true))

def expectedLeftProof : List.Vector (Option Bool) leftIndex.depth :=
  some true ::ᵥ List.Vector.nil

def expectedRightProof : List.Vector (Option Bool) rightIndex.depth :=
  some false ::ᵥ List.Vector.nil

private lemma depthOneGame_eq :
    InductiveMerkleTree.extractabilityGame depthOneAdversary =
      (((InductiveMerkleTree.spec Bool).query (false, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun root =>
        if root then
          pure (root, (), ⟨rightIndex, true, rightProof,
            expectedTree root, expectedRightProof, true⟩)
        else
          pure (root, (), ⟨leftIndex, false, leftProof,
            expectedTree root, expectedLeftProof, true⟩)) := by
  rw [show InductiveMerkleTree.extractabilityGame depthOneAdversary =
      (InductiveMerkleTree.spec Bool).withCacheOverlay ∅
        (InductiveMerkleTree.extractabilityInner depthOneAdversary) from rfl]
  rw [show InductiveMerkleTree.extractabilityInner depthOneAdversary =
      depthOneAdversary.commit.withQueryLog >>= fun ((root, aux), queryLog) => do
        let extractedTree := InductiveMerkleTree.extractor depthOneSkeleton queryLog root
        let ⟨idx, leaf, proof⟩ ← depthOneAdversary.opening aux
        let extractedProof := InductiveMerkleTree.generateProof extractedTree idx
        let verified ← InductiveMerkleTree.verifyProof idx leaf root proof
        return (root, aux,
          ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩) from rfl]
  rw [withCacheOverlay_bind, depthOneCommit_cached_eq]
  simp only [bind_assoc, pure_bind]
  refine bind_congr (m := OracleComp (InductiveMerkleTree.spec Bool)) fun root => ?_
  cases root <;>
    simp [OracleSpec.withCacheOverlay,
      InductiveMerkleTree.extractor, InductiveMerkleTree.extractorChildren,
      depthOneSkeleton, leftIndex, rightIndex, expectedTree,
      expectedLeftProof, expectedRightProof]

/-- If the shared answer is `false`, the adversary opens the left branch. -/
example : (false, (), ⟨leftIndex, false, leftProof,
    expectedTree false, expectedLeftProof, true⟩) ∈
    support (InductiveMerkleTree.extractabilityGame depthOneAdversary) := by
  rw [depthOneGame_eq]
  simp

/-- If the shared answer is `true`, the adversary opens the right branch. -/
example : (true, (), ⟨rightIndex, true, rightProof,
    expectedTree true, expectedRightProof, true⟩) ∈
    support (InductiveMerkleTree.extractabilityGame depthOneAdversary) := by
  rw [depthOneGame_eq]
  simp

/-- Commit, opening, and verification all query `(false, true)`. The shared oracle returns
one answer throughout, so the commit-prefix extractor recovers the opened leaf and full path. -/
example (transcript : Bool × Unit ×
    ((idx : BinaryTree.SkeletonLeafIndex depthOneSkeleton) × Bool ×
      List.Vector Bool idx.depth × BinaryTree.FullData (Option Bool) depthOneSkeleton ×
      List.Vector (Option Bool) idx.depth × Bool))
    (htranscript : transcript ∈ support
      (InductiveMerkleTree.extractabilityGame depthOneAdversary)) :
    ¬ InductiveMerkleTree.AdversaryWinsExtractabilityGame transcript := by
  rw [depthOneGame_eq] at htranscript
  rw [mem_support_bind_iff] at htranscript
  obtain ⟨root, _, htranscript⟩ := htranscript
  cases root <;> simp at htranscript
  all_goals subst transcript
  all_goals simp [InductiveMerkleTree.AdversaryWinsExtractabilityGame,
    InductiveMerkleTree.AdversaryWinsExtractabilityInner,
    expectedTree, expectedLeftProof, expectedRightProof, depthOneSkeleton,
    leftIndex, rightIndex, leftProof, rightProof]
  all_goals rfl

/-! ## ROM-bound producer canaries -/

abbrev depthZeroAdversary :
    InductiveMerkleTree.Adversary Bool BinaryTree.Skeleton.leaf where
  AuxState := Unit
  commit := pure (false, ())
  opening _ := pure ⟨.ofLeaf, false, List.Vector.nil⟩

private lemma depthZeroAdversary_totalBound :
    depthZeroAdversary.IsTwoPhaseTotalQueryBound 0 := by
  trivial

/-- At depth zero, a query-free two-phase adversary has zero extraction-failure probability.
This pins the fact that the verifier hashes internal nodes only; it does not hash a raw leaf. -/
example :
    Pr[InductiveMerkleTree.AdversaryWinsExtractabilityGame |
      InductiveMerkleTree.extractabilityGame depthZeroAdversary] = 0 := by
  apply le_antisymm
  · simpa using InductiveMerkleTree.extractability_rom_bound
      depthZeroAdversary 0 depthZeroAdversary_totalBound
  · exact zero_le

/-- A commit with no hash queries followed by a depth-one opening. Verification's one fresh
hash can hit the commit-time root target, so the fresh-hit term in the ROM theorem is necessary. -/
abbrev freshHitAdversary : InductiveMerkleTree.Adversary Bool depthOneSkeleton where
  AuxState := Unit
  commit := pure (false, ())
  opening _ := pure ⟨leftIndex, false, leftProof⟩

def freshHitExtractedTree : BinaryTree.FullData (Option Bool) depthOneSkeleton :=
  .internal (some false) (.leaf none) (.leaf none)

def freshHitExtractedProof : List.Vector (Option Bool) leftIndex.depth :=
  none ::ᵥ List.Vector.nil

private lemma freshHitGame_eq :
    InductiveMerkleTree.extractabilityGame freshHitAdversary =
      (((InductiveMerkleTree.spec Bool).query (false, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun answer =>
        pure (false, (), ⟨leftIndex, false, leftProof,
          freshHitExtractedTree, freshHitExtractedProof, answer == false⟩)) := by
  simp [InductiveMerkleTree.extractabilityGame,
    InductiveMerkleTree.extractabilityInner, OracleSpec.withCacheOverlay,
    freshHitAdversary, freshHitExtractedTree, freshHitExtractedProof,
    InductiveMerkleTree.extractor, InductiveMerkleTree.extractorChildren,
    InductiveMerkleTree.verifyProof, InductiveMerkleTree.getPutativeRoot,
    InductiveMerkleTree.singleHash, depthOneSkeleton, leftIndex, leftProof_head]

def freshHitTranscript : Bool × Unit ×
    ((idx : BinaryTree.SkeletonLeafIndex depthOneSkeleton) × Bool ×
      List.Vector Bool idx.depth × BinaryTree.FullData (Option Bool) depthOneSkeleton ×
      List.Vector (Option Bool) idx.depth × Bool) :=
  (false, (), ⟨leftIndex, false, leftProof,
    freshHitExtractedTree, freshHitExtractedProof, true⟩)

/-- The fresh verifier answer `false` produces a supported extraction failure. -/
example : freshHitTranscript ∈
    support (InductiveMerkleTree.extractabilityGame freshHitAdversary) := by
  rw [freshHitGame_eq]
  simp [freshHitTranscript]

example : InductiveMerkleTree.AdversaryWinsExtractabilityGame freshHitTranscript := by
  simp [freshHitTranscript, InductiveMerkleTree.AdversaryWinsExtractabilityGame,
    InductiveMerkleTree.AdversaryWinsExtractabilityInner, freshHitExtractedTree,
    freshHitExtractedProof, depthOneSkeleton, leftIndex]

def twoDistinctQueries : OracleComp (InductiveMerkleTree.spec Bool) Unit := do
  let _ ← ((InductiveMerkleTree.spec Bool).query (false, false) :
    OracleComp (InductiveMerkleTree.spec Bool) Bool)
  let _ ← ((InductiveMerkleTree.spec Bool).query (false, true) :
    OracleComp (InductiveMerkleTree.spec Bool) Bool)
  return ()

def collidingCache : (InductiveMerkleTree.spec Bool).QueryCache :=
  ((∅ : (InductiveMerkleTree.spec Bool).QueryCache).cacheQuery (false, false) false).cacheQuery
    (false, true) false

/-- Two distinct fresh inputs can receive the same answer and produce a cache collision. This
pins the birthday branch of the ROM proof separately from the fresh-target branch. -/
example : CacheHasCollision collidingCache := by
  refine ⟨(false, false), (false, true), false, false, by decide, ?_, ?_, HEq.rfl⟩
  · simp [collidingCache, QueryCache.cacheQuery_of_ne]
  · simp [collidingCache]

example : ((), collidingCache) ∈ support
    ((simulateQ (InductiveMerkleTree.spec Bool).cachingOracle twoDistinctQueries).run ∅) := by
  simp [twoDistinctQueries, collidingCache, QueryCache.cacheQuery_of_ne]

end VCVioTest.MerkleTreeExtractability
