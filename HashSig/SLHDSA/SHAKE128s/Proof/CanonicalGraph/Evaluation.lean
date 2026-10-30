/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Input
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Wots

/-!
# Faithful fixed-hash evaluation

Every cell below is an existing concrete algorithm output under a fixed hash function:
`structuralValue` assigns to each structural node the WOTS+, Merkle or FORS value the algorithms
compute for it, and `value` extends it by the secret seed. The recurrence theorem
`value_equation` connects these actual computations to the canonical DAG: each node's value is the
hash of its canonical input. `value_unique` shows that the evaluation is the only cell assignment
satisfying these equations. Nothing here posits component security.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.CanonicalGraph

variable [HasQuery HashSpec Id]

/-- The value the SLH-DSA algorithms compute at a structural node, for fixed seeds and a fixed
hash function. -/
@[expose] def structuralValue (secretSeed publicSeed : Digest) : StructuralNode → Digest
  | .wotsPrf key chain => Hashing.derive (m := Id) publicSeed secretSeed
      (Wots.secretAddress key.address chain)
  | .wotsHash key chain step =>
      Wots.chain (m := Id) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chain.val }
        0 (step.val + 1)
        (Hashing.derive (m := Id) publicSeed secretSeed (Wots.secretAddress key.address chain))
  | .wotsPk key => Wots.publicKey (m := Id) secretSeed publicSeed key.address
  | .tree location height index =>
      Merkle.node (m := Id) secretSeed publicSeed location.address (height.val + 1) index.val
  | .forsPrf key index => Fors.secret (m := Id) secretSeed publicSeed key.address index.val
  | .forsTree key height index =>
      Fors.node (m := Id) secretSeed publicSeed key.address height.val index.val
  | .forsRoots key =>
      Hashing.tweakable (m := Id) publicSeed
        { key.address.setTypeAndClear .forsRoots with keyPair := key.address.keyPair }
        (digestArrayBytes fun i : Fin forsTrees =>
          Fors.node (m := Id) secretSeed publicSeed key.address forsHeight i.val)

/-- The actual evaluation of the canonical graph: the secret seed at its node and the computed
value at every structural node. -/
@[expose] def value (secretSeed publicSeed : Digest) : Cells
  | .secretSeed => secretSeed
  | .structural node => structuralValue secretSeed publicSeed node

omit [HasQuery HashSpec Id] in
/-- The child encoding of a list of children given by a function is the corresponding digest
array encoding. -/
theorem childBytes_ofFn {size : Nat} (cells : Cells) (children : Fin size → Node) :
    childBytes cells (List.ofFn children) = digestArrayBytes (fun i => cells (children i)) := by
  simp only [childBytes, List.map_ofFn, digestArrayBytes, Function.comp_def]

/-- The value at a Merkle node is the Merkle algorithm's node value. -/
theorem value_merkleNode (secretSeed publicSeed : Digest) (tree : Tree)
    (height : Nat) (hheight : height ≤ subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - height))) :
    value secretSeed publicSeed (.structural (merkleNode tree height hheight index)) =
      Merkle.node (m := Id) secretSeed publicSeed tree.address height index.val := by
  unfold merkleNode
  split
  · rename_i hzero
    subst height
    rfl
  · rename_i hzero
    simp only [value, structuralValue]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ height)]

/-- The value at a Merkle child is the Merkle algorithm's value at the child position. -/
theorem value_merkleChild (secretSeed publicSeed : Digest) (tree : Tree)
    (height : Fin subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - (height.val + 1)))) (side : Fin 2) :
    value secretSeed publicSeed (.structural (merkleChild tree height index side)) =
      Merkle.node (m := Id) secretSeed publicSeed tree.address height.val
        (2 * index.val + side.val) :=
  value_merkleNode _ _ _ _ _ _

/-- Each structural value is the hash of the node's canonical input under the evaluation. -/
theorem structuralValue_equation (secretSeed publicSeed : Digest) (parent : StructuralNode) :
    structuralValue secretSeed publicSeed parent =
      Hashing.shortHash (m := Id)
        (canonicalInput publicSeed (value secretSeed publicSeed) parent) := by
  change @Eq (Id Digest) (structuralValue secretSeed publicSeed parent)
    (Hashing.shortHash (m := Id) (canonicalInput publicSeed (value secretSeed publicSeed) parent))
  cases parent with
  | wotsPrf key chain | forsPrf key index => rfl
  | wotsHash key chain step =>
      rcases step with ⟨step, hstep⟩
      cases step with
      | zero =>
          simp [structuralValue, Wots.chain_succ, canonicalInput, StructuralNode.address,
            StructuralNode.children, childBytes, value, Hashing.tweakable]
      | succ step =>
          have hchain := Correctness.Wots.chain_add publicSeed
            { key.address with chainOrHeight := BitVec.ofNat 32 chain.val }
            0 (step + 1) 1
            (Hashing.derive (m := Id) publicSeed secretSeed (Wots.secretAddress key.address chain))
          simpa only [structuralValue, canonicalInput, StructuralNode.address,
            StructuralNode.children, Nat.succ_ne_zero, ↓reduceDIte,
            childBytes, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
            List.append_nil, value, Nat.add_sub_cancel, Nat.zero_add,
            Wots.chain_zero, Wots.chain_succ, bind, pure, Hashing.tweakable] using hchain
  | wotsPk key =>
      simp only [structuralValue, Wots.publicKey_eq, Correctness.sequenceFin_id, bind,
        canonicalInput, StructuralNode.children, childBytes_ofFn, value,
        StructuralNode.address, Hashing.tweakable]
      rfl
  | tree tree height index =>
      simp only [structuralValue, Merkle.node_succ, bind, canonicalInput,
        StructuralNode.children, childBytes, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil, value_merkleChild,
        StructuralNode.address, Hashing.tweakable]
      rfl
  | forsTree key height index =>
      rcases height with ⟨height, hheight⟩
      cases height with
      | zero => rfl
      | succ height =>
          simp only [structuralValue, Fors.node_succ, bind, canonicalInput,
            StructuralNode.children, Nat.succ_ne_zero, ↓reduceDIte, childBytes,
            List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
            List.append_nil, value, forsChild, Nat.add_sub_cancel,
            StructuralNode.address, Hashing.tweakable]
          rfl
  | forsRoots key =>
      simp only [structuralValue, canonicalInput, StructuralNode.children,
        childBytes_ofFn, value, StructuralNode.address, Hashing.tweakable]

/-- The evaluation at each structural node is the hash of its canonical input. -/
theorem value_equation (secretSeed publicSeed : Digest) (parent : StructuralNode) :
    value secretSeed publicSeed (.structural parent) =
      Hashing.shortHash (m := Id)
        (canonicalInput publicSeed (value secretSeed publicSeed) parent) :=
  structuralValue_equation _ _ _

/-- A cell table satisfying these concrete hash equations is the actual algorithm evaluation. -/
theorem value_unique (secretSeed publicSeed : Digest) (cells : Cells)
    (hseed : cells .secretSeed = secretSeed)
    (hparents : ∀ parent, Hashing.shortHash (m := Id)
      (canonicalInput publicSeed cells parent) = cells (.structural parent)) :
    value secretSeed publicSeed = cells := by
  funext node
  induction node using (measure Node.rank).wf.induction with
  | h node ih =>
      cases node with
      | secretSeed => exact hseed.symm
      | structural parent =>
          rw [value_equation]
          have hinput := canonicalInput_congr publicSeed (value secretSeed publicSeed) cells parent
            (fun child hchild => ih child (parent.child_rank_lt child hchild))
          rw [hinput, hparents]

end SLHDSA.SHAKE128s.CanonicalGraph
