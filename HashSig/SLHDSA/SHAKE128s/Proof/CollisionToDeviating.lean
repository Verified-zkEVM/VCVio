/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalTarget
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.BinaryPath
public import HashSig.SLHDSA.SHAKE128s.Proof.StructuralTerm
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Evaluation

/-!
# Path collisions are deviating canonical-graph queries

Every authentication-path collision extracted from a forgery — Merkle in
`Extraction.Merkle`, FORS in `Extraction.Fors`, and the layer collisions of
`Extraction.Hypertree` — has the shape `BinaryPath.Collision`: at some height the supplied
child pair differs from the canonical one, yet hashing it under that node's address
reproduces the canonical parent value.

`StructuralTerm.DeviatingCollision` has exactly that shape in canonical-graph terms: a query
whose parsed child values deviate from the honest cells at some parent, whose cached answer
truncates to the parent's honest cell. This file supplies the byte-level bridge between the
two: a binary structural node has exactly two children, and the canonical graph's
`childBytes` encoding of a two-child node is literally `BinaryPath.pairBytes`.

With this, mapping a path collision to a deviating query is a matter of naming the parent
node and the candidate cells; the byte inputs already agree on the nose.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.CollisionToDeviating

open CanonicalGraph

/-- The canonical graph's child encoding of a two-child node is the binary-path pair
encoding. -/
theorem childBytes_pair (cells : Cells) (left right : Node) :
    childBytes cells [left, right] =
      Extraction.BinaryPath.pairBytes (cells left, cells right) := by
  simp [childBytes, Extraction.BinaryPath.pairBytes]

/-- A tree node's canonical query input is the tweakable input on its two children's pair
bytes, under its own address. -/
theorem canonicalInput_tree (publicSeed : Digest) (cells : Cells)
    (location : Tree) (height : Fin subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - (height.val + 1)))) :
    canonicalInput publicSeed cells (.tree location height index) =
      Hashing.tweakableInput publicSeed
        (StructuralNode.tree location height index).address
        (Extraction.BinaryPath.pairBytes
          (cells (.structural (merkleChild location height index 0)),
            cells (.structural (merkleChild location height index 1)))) := by
  unfold canonicalInput
  exact congrArg
    (Hashing.tweakableInput publicSeed
      (StructuralNode.tree location height index).address)
    (childBytes_pair cells _ _)

/-- The two children of a tree node, as a pair, determine candidate cells agreeing with the
supplied pair. Deviation of the pair is deviation of the cells at a child. -/
theorem exists_deviating_child (cells : Cells) (left right : Node)
    (actualLeft actualRight : Digest)
    (hne : (actualLeft, actualRight) ≠ (cells left, cells right))
    (hdistinct : left ≠ right) :
    ∃ candidates : Cells,
      candidates left = actualLeft ∧ candidates right = actualRight ∧
        ∃ child ∈ [left, right], candidates child ≠ cells child := by
  classical
  refine ⟨fun node => if node = left then actualLeft else
    if node = right then actualRight else cells node, ?_, ?_, ?_⟩
  · simp
  · simp [hdistinct.symm]
  · by_cases hleft : actualLeft = cells left
    · refine ⟨right, by simp, ?_⟩
      have hright : actualRight ≠ cells right := by
        intro hright
        exact hne (by rw [hleft, hright])
      simpa [hdistinct.symm] using hright
    · exact ⟨left, by simp, by simpa using hleft⟩

/-! ## From a Merkle-layer collision to a charged structural event

The extraction chain hands back a `LayerCollision`: the verifier recomputed a node and got the
honest value although the two children it hashed were not the honest pair. The charge, on the
other side, is stated about `StructuralTerm.DeviatingCollision` — a cache entry at the
canonical input of a *deviating* candidate assignment whose answer truncates to the honest
cell. The lemma below is the join.

Only one thing has to be supplied beyond what the collision already says, and it is the reason
this is a lemma rather than a rewrite: a cache entry. The collision is a statement about
values the verifier computed; the charge is a statement about what is in the oracle cache. The
bridge is that the verifier obtained the value by querying, so the entry is there — and that
query is one of the `q` charged calls, which is exactly why the event is affordable at the
structural rate. The hypothesis `hentry` is where a caller discharges that.
-/

/-- **A Merkle-layer collision is a charged structural event.** If the cache holds an answer at
the tree node's input formed from a pair of child values that is not the honest pair, and that
answer truncates to the node's honest cell, the run has produced a `DeviatingCollision`. -/
theorem deviatingCollision_of_tree_pair {α : Type} (publicSeed : Digest) (cells : Cells)
    (location : Tree) (height : Fin subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - (height.val + 1))))
    (actualLeft actualRight : Digest)
    (hchildren : (StructuralNode.tree location height index).children =
      [.structural (merkleChild location height index 0),
        .structural (merkleChild location height index 1)])
    (hdistinct : (Node.structural (merkleChild location height index 0)) ≠
      .structural (merkleChild location height index 1))
    (hne : (actualLeft, actualRight) ≠
      (cells (.structural (merkleChild location height index 0)),
        cells (.structural (merkleChild location height index 1))))
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hentry : result.2 (Hashing.tweakableInput publicSeed
        (StructuralNode.tree location height index).address
        (Extraction.BinaryPath.pairBytes (actualLeft, actualRight))) = some output)
    (hcollision : Hashing.truncate output =
      cells (.structural (.tree location height index))) :
    StructuralTerm.DeviatingCollision publicSeed cells result := by
  obtain ⟨candidates, hleft, hright, hdeviates⟩ :=
    exists_deviating_child cells _ _ actualLeft actualRight hne hdistinct
  refine ⟨candidates, .tree location height index, output, ?_, ?_, hcollision⟩
  · obtain ⟨child, hmember, hdiffers⟩ := hdeviates
    exact ⟨child, by rw [hchildren]; exact hmember, hdiffers⟩
  · rwa [canonicalInput_tree publicSeed candidates location height index, hleft, hright]

/-! ## The single-child case: FORS leaves

`Extraction.Fors.LeafCollision` has the same content as a Merkle-layer collision but at a node
with one child: the forged secret differs from the honest one, yet hashing it under the leaf's
address gives the same value. The join is the same, and simpler — one child means the
deviating assignment is just the honest cells with that child overwritten. -/

/-- The canonical graph's child encoding of a one-child node is the child's cell bytes. -/
theorem childBytes_single (cells : Cells) (child : Node) :
    childBytes cells [child] = bytesBE n (cells child) := by
  simp [childBytes]

/-- **A single-child collision is a charged structural event.** -/
theorem deviatingCollision_of_single_child {α : Type} (publicSeed : Digest) (cells : Cells)
    (parent : StructuralNode) (child : Node) (actual : Digest)
    (hchildren : parent.children = [child])
    (hne : actual ≠ cells child)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hentry : result.2 (Hashing.tweakableInput publicSeed parent.address
        (bytesBE n actual)) = some output)
    (hcollision : Hashing.truncate output = cells (.structural parent)) :
    StructuralTerm.DeviatingCollision publicSeed cells result := by
  classical
  refine ⟨Function.update cells child actual, parent, output, ⟨child, ?_, ?_⟩, ?_, hcollision⟩
  · rw [hchildren]; exact List.mem_singleton_self child
  · rw [Function.update_self]; exact hne
  · rw [canonicalInput, hchildren, childBytes_single, Function.update_self]
    exact hentry

/-! ## The array case: FORS root compression

`Extraction.Fors.CompressionCollision` sits at the node that compresses the fourteen FORS tree
roots, whose children are given by `List.ofFn` and whose payload is `digestArrayBytes` rather
than a flattened pair. The content is the same as the other two joins; only the byte-level
step differs, and `CanonicalGraph.Evaluation`'s `childBytes_ofFn` already supplies it. -/

/-- **An array-node collision is a charged structural event.** -/
theorem deviatingCollision_of_array {α : Type} {size : Nat} (publicSeed : Digest)
    (cells : Cells) (parent : StructuralNode) (children : Fin size → Node)
    (actual : Fin size → Digest)
    (hchildren : parent.children = List.ofFn children)
    (hinj : Function.Injective children)
    (hne : ∃ index, actual index ≠ cells (children index))
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hentry : result.2 (Hashing.tweakableInput publicSeed parent.address
        (digestArrayBytes actual)) = some output)
    (hcollision : Hashing.truncate output = cells (.structural parent)) :
    StructuralTerm.DeviatingCollision publicSeed cells result := by
  classical
  set candidates : Cells := fun node =>
    if h : ∃ index, children index = node then actual h.choose else cells node with hcand
  have hvalue : ∀ index, candidates (children index) = actual index := by
    intro index
    have hexists : ∃ probe, children probe = children index := ⟨index, rfl⟩
    simp only [hcand, dite_eq_left hexists]
    rw [hinj hexists.choose_spec]
  refine ⟨candidates, parent, output, ?_, ?_, hcollision⟩
  · obtain ⟨index, hindex⟩ := hne
    exact ⟨children index, by rw [hchildren]; exact List.mem_ofFn.mpr ⟨index, rfl⟩,
      by rw [hvalue index]; exact hindex⟩
  · rw [canonicalInput, hchildren, childBytes_ofFn,
      show (fun index => candidates (children index)) = actual from funext hvalue]
    exact hentry

end SLHDSA.SHAKE128s.CollisionToDeviating
