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
      (Prod.fst <$> (simulateQ (InductiveMerkleTree.spec Bool).cachingOracle
        (InductiveMerkleTree.extractabilityInner adversary)).run ∅) := rfl

end VCVioTest.MerkleTreeExtractability
