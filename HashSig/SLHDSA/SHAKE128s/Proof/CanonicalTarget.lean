/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Parsing
public import HashSig.SLHDSA.SHAKE128s.Proof.FreshHitBound

/-!
# The canonical target of a structural query

`FreshHitBound.Hit` is the event that a query's answer matches an optional target chosen for
each byte input. This file supplies the target that the structural extraction produces: a query
whose bytes parse as a canonical graph input at some parent node is charged against *that node's
own canonical cell value*, and only when the child values carried by the query deviate from
the honest ones.

The canonical/deviating split is decided by `CanonicalGraph.parseInput`, which reads only
the public seed and the query bytes. That matters twice:

* honest queries are free (`canonicalTarget_canonical`): the signer and key generator query
  exactly the canonical inputs, whose answers truncate to the canonical cell by definition,
  so a total target would make the honest cache violate `Clean` at once. Sending them to
  `none` keeps the honest cache clean (`clean_of_canonical_cache`);
* a deviating query is charged against one specific digest (`canonicalTarget_deviating`),
  so the charge stays linear in the query count rather than scaling with the number of
  honest cell values.

`hit_of_deviating_collision` is the bridge: exactly the equation an extracted structural
fault witness provides — a deviating input whose answer truncates to the canonical parent
cell — is an instance of `FreshHitBound.Hit`, hence charged at `2 ^ -128` per query.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.CanonicalTarget

open CanonicalGraph

/-- The query's child values agree with the honest cells at the parsed parent. -/
@[expose] def Honest (cells : Cells) (parsed : ParsedInput) : Prop :=
  ∀ child ∈ parsed.parent.children, parsed.candidates child = cells child

/-- Honesty of a parsed query is decided child by child. -/
instance (cells : Cells) (parsed : ParsedInput) : Decidable (Honest cells parsed) :=
  List.decidableBAll _ _

/-- Charge a deviating structural query against its own parent's canonical cell. -/
@[expose] noncomputable def canonicalTarget (publicSeed : Digest) (cells : Cells)
    (input : Bytes) : Option Digest :=
  match parseInput publicSeed input with
  | none => none
  | some parsed => if Honest cells parsed then none else some (cells (.structural parsed.parent))

/-- Honest queries are never charged: the canonical input at a node has no target. -/
theorem canonicalTarget_canonical (publicSeed : Digest) (cells : Cells)
    (parent : StructuralNode) :
    canonicalTarget publicSeed cells (canonicalInput publicSeed cells parent) = none := by
  obtain ⟨parsed, hparse, hparent, hvalues⟩ := parseInput_canonical publicSeed cells parent
  have hhonest : Honest cells parsed := by
    intro child hchild
    exact hvalues child (hparent ▸ hchild)
  simp only [canonicalTarget, hparse, ite_eq_left hhonest]

/-- A cache all of whose inputs are honest canonical queries is clean for this target. -/
theorem clean_of_canonical_cache (publicSeed : Digest) (cells : Cells)
    (cache : QueryCache HashSpec)
    (hcanonical : ∀ input, cache input ≠ none →
      ∃ parent : StructuralNode, input = canonicalInput publicSeed cells parent) :
    FreshHitBound.Clean (canonicalTarget publicSeed cells) cache := by
  intro input output hentry
  obtain ⟨parent, rfl⟩ := hcanonical input (by rw [hentry]; simp)
  rw [canonicalTarget_canonical]
  simp

/-- A query carrying child values that deviate from the honest cells is charged against the
canonical cell of its parent. -/
theorem canonicalTarget_deviating (publicSeed : Digest) (cells candidates : Cells)
    (parent : StructuralNode)
    (hdeviates : ∃ child ∈ parent.children, candidates child ≠ cells child) :
    canonicalTarget publicSeed cells (canonicalInput publicSeed candidates parent) =
      some (cells (.structural parent)) := by
  cases hparse : parseInput publicSeed (canonicalInput publicSeed candidates parent) with
  | none =>
    exact absurd ⟨⟨parent, candidates⟩, rfl⟩ ((parseInput_none_iff _ _).mp hparse)
  | some parsed =>
    obtain ⟨_, hparent, hvalues⟩ := canonicalInput_eq_iff.mp (parseInput_sound hparse)
    have hnotHonest : ¬ Honest cells parsed := by
      intro hhonest
      obtain ⟨child, hchild, hne⟩ := hdeviates
      have hchild' : child ∈ parsed.parent.children := by rw [hparent]; exact hchild
      refine hne ?_
      rw [← hvalues child hchild']
      exact hhonest child hchild'
    rw [canonicalTarget, hparse]
    simp only [ite_eq_right hnotHonest, hparent]

/-- The bridge from an extracted structural fault to a charged hit: a deviating query whose
answer truncates to the canonical parent cell is an instance of `FreshHitBound.Hit`. -/
theorem hit_of_deviating_collision {α : Type} (publicSeed : Digest) (cells candidates : Cells)
    (parent : StructuralNode) (result : α × QueryCache HashSpec) (output : HashOutput)
    (hdeviates : ∃ child ∈ parent.children, candidates child ≠ cells child)
    (hentry : result.2 (canonicalInput publicSeed candidates parent) = some output)
    (hcollision : Hashing.truncate output = cells (.structural parent)) :
    FreshHitBound.Hit (canonicalTarget publicSeed cells) result := by
  refine ⟨canonicalInput publicSeed candidates parent, output, hentry, ?_⟩
  rw [canonicalTarget_deviating publicSeed cells candidates parent hdeviates, hcollision]

end SLHDSA.SHAKE128s.CanonicalTarget
