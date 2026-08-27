/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Perfect
public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Deterministic Interpretations of Perfect Merkle Trees

This module proves that interpreting callback-parametric perfect-Merkle computations with an
arbitrary deterministic oracle answer function yields the corresponding pure tree. The answer
function is fixed for the whole computation; no claim is made about raw, independently sampled
oracle queries.

The final theorem, `simulateQ_honest_reconstruct`, is functional completeness at this boundary:
after fixing any deterministic answer function, an honestly generated leaf and sized path
reconstruct the root computed with the same interpreted callbacks.
-/

@[expose] public section

namespace PerfectMerkleTree

open OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {Y : Type v}

/-- A deterministic handler commutes with subtree-root production. -/
@[simp]
theorem simulateQ_treeHashM (impl : QueryImpl spec Id)
    (leaf : ℕ → OracleComp spec Y) (nodeHash : Address → Y → Y → OracleComp spec Y)
    (height index : ℕ) :
    simulateQ impl (treeHashM leaf nodeHash height index) =
      treeHash (fun i => simulateQ impl (leaf i))
        (fun address left right => simulateQ impl (nodeHash address left right)) height index := by
  induction height generalizing index with
  | zero => rfl
  | succ height ih =>
      simp only [treeHashM, simulateQ_bind, treeHash, ih]
      rfl

/-- A deterministic handler commutes with root production. -/
@[simp]
theorem simulateQ_rootM (impl : QueryImpl spec Id)
    (leaf : ℕ → OracleComp spec Y) (nodeHash : Address → Y → Y → OracleComp spec Y)
    (height : ℕ) :
    simulateQ impl (rootM leaf nodeHash height) =
      root (fun i => simulateQ impl (leaf i))
        (fun address left right => simulateQ impl (nodeHash address left right)) height := by
  simp [rootM, root]

/-- A deterministic handler commutes with sized authentication-path production. -/
@[simp]
theorem simulateQ_authenticationPathM (impl : QueryImpl spec Id)
    (leaf : ℕ → OracleComp spec Y) (nodeHash : Address → Y → Y → OracleComp spec Y)
    (base index depth : ℕ) :
    simulateQ impl (authenticationPathM leaf nodeHash base index depth) =
      authenticationPath (fun i => simulateQ impl (leaf i))
        (fun address left right => simulateQ impl (nodeHash address left right))
        base index depth := by
  induction depth generalizing base index with
  | zero => rfl
  | succ depth ih =>
      simp only [authenticationPathM, simulateQ_bind, authenticationPath,
        simulateQ_treeHashM, ih]
      rfl

/-- A deterministic handler commutes with folding a sized authentication path. -/
@[simp]
theorem simulateQ_climbM (impl : QueryImpl spec Id)
    (nodeHash : Address → Y → Y → OracleComp spec Y) (base index depth : ℕ)
    (node : Y) (path : AuthenticationPath Y depth) :
    simulateQ impl (climbM nodeHash base index depth node path) =
      climb (fun address left right => simulateQ impl (nodeHash address left right))
        base index depth node path := by
  induction depth generalizing base index node with
  | zero => rfl
  | succ depth ih =>
      by_cases h : index % 2 = 0 <;>
        simp [climbM, climb, h, simulateQ_bind, ih] <;> rfl

/-- A deterministic handler commutes with root-level path production. -/
@[simp]
theorem simulateQ_rootAuthenticationPathM (impl : QueryImpl spec Id)
    (leaf : ℕ → OracleComp spec Y) (nodeHash : Address → Y → Y → OracleComp spec Y)
    {height : ℕ} (index : LeafIndex height) :
    simulateQ impl (rootAuthenticationPathM leaf nodeHash index) =
      rootAuthenticationPath (fun i => simulateQ impl (leaf i))
        (fun address left right => simulateQ impl (nodeHash address left right)) index := by
  simp [rootAuthenticationPathM, rootAuthenticationPath]

/-- A deterministic handler commutes with root reconstruction. -/
@[simp]
theorem simulateQ_reconstructRootM (impl : QueryImpl spec Id)
    (nodeHash : Address → Y → Y → OracleComp spec Y) {height : ℕ}
    (index : LeafIndex height) (leafValue : Y) (path : AuthenticationPath Y height) :
    simulateQ impl (reconstructRootM nodeHash index leafValue path) =
      reconstructRoot (fun address left right => simulateQ impl (nodeHash address left right))
        index leafValue path := by
  simp [reconstructRootM, reconstructRoot]

/-- Functional completeness after fixing an arbitrary deterministic oracle answer function.

The statement deliberately interprets the entire honest opening computation with one `impl`.
It does not assert completeness for raw `OracleComp` semantics, where repeated identical queries
are sampled independently. -/
theorem simulateQ_honest_reconstruct (impl : QueryImpl spec Id)
    (leaf : ℕ → OracleComp spec Y) (nodeHash : Address → Y → Y → OracleComp spec Y)
    {height : ℕ} (index : LeafIndex height) :
    simulateQ impl (do
      let leafValue ← leaf index.val
      let path ← rootAuthenticationPathM leaf nodeHash index
      reconstructRootM nodeHash index leafValue path) =
      simulateQ impl (rootM leaf nodeHash height) := by
  simp only [simulateQ_bind, simulateQ_rootAuthenticationPathM, simulateQ_reconstructRootM,
    simulateQ_rootM]
  exact reconstructRoot_authenticationPath
    (fun i => simulateQ impl (leaf i))
    (fun address left right => simulateQ impl (nodeHash address left right)) index

end PerfectMerkleTree
