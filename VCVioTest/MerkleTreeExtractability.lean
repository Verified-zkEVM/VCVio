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

abbrev depthOneAdversary : InductiveMerkleTree.Adversary Bool depthOneSkeleton where
  AuxState := Unit
  commit := do
    let root ← ((InductiveMerkleTree.spec Bool).query (false, true) :
      OracleComp (InductiveMerkleTree.spec Bool) Bool)
    return (root, ())
  opening _ := do
    let _ ← ((InductiveMerkleTree.spec Bool).query (false, true) :
      OracleComp (InductiveMerkleTree.spec Bool) Bool)
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

def expectedProof : List.Vector (Option Bool) leftIndex.depth :=
  some true ::ᵥ List.Vector.nil

private lemma depthOneGame_eq :
    InductiveMerkleTree.extractabilityGame depthOneAdversary =
      (((InductiveMerkleTree.spec Bool).query (false, true) :
          OracleComp (InductiveMerkleTree.spec Bool) Bool) >>= fun root =>
        pure (root, (), ⟨leftIndex, false, leftProof,
          expectedTree root, expectedProof, true⟩)) := by
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
  simp [OracleSpec.withCacheOverlay, depthOneAdversary,
    InductiveMerkleTree.extractor, InductiveMerkleTree.extractorChildren,
    depthOneSkeleton, leftIndex, leftProof_head, expectedTree, expectedProof]

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
  rw [mem_support_pure_iff] at htranscript
  subst transcript
  simp [InductiveMerkleTree.AdversaryWinsExtractabilityGame,
    InductiveMerkleTree.AdversaryWinsExtractabilityInner,
    expectedTree, expectedProof, depthOneSkeleton, leftIndex, leftProof]
  rfl

end VCVioTest.MerkleTreeExtractability
