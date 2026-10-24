/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Input

/-!
# Parsing canonical inputs

An input-only parser for the canonical graph. The parser uses only the public seed and
query bytes. Its candidate table is a witness reconstructed from those bytes, not the
secret table. Values at coordinates outside the parsed parent's children are irrelevant.
The parser is noncomputable because efficiency is immaterial for the query-count reduction.
-/

public section

namespace SlhDsaSecurity.CanonicalGraph

/-- A reading of a byte string as a canonical input: the structural node it is the input of, and
cells from which it is formed. -/
structure ParsedInput where
  /-- The structural node whose canonical input the bytes are. -/
  parent : StructuralNode
  /-- A cell assignment whose values at the parent's children form the input's payload. -/
  candidates : Cells

/-- The bytes are the canonical input of some structural node, under some cell assignment. -/
@[expose] def HasParse (publicSeed : Digest) (input : Bytes) : Prop :=
  ∃ parsed : ParsedInput, canonicalInput publicSeed parsed.candidates parsed.parent = input

/-- A chosen parse of the bytes as a canonical input under the given public seed, or `none` if
they are not one. -/
@[expose]
noncomputable def parseInput (publicSeed : Digest) (input : Bytes) : Option ParsedInput := by
  classical
  exact if h : HasParse publicSeed input then some h.choose else none

/-- A parse reproduces its input. -/
theorem parseInput_sound {publicSeed : Digest} {input : Bytes} {parsed : ParsedInput}
    (hparse : parseInput publicSeed input = some parsed) :
    canonicalInput publicSeed parsed.candidates parsed.parent = input := by
  classical
  unfold parseInput at hparse
  split at hparse
  · rename_i hexists
    have heq := Option.some.inj hparse
    subst parsed
    exact hexists.choose_spec
  · contradiction

/-- The parser fails exactly on bytes that are not a canonical input. -/
theorem parseInput_none_iff (publicSeed : Digest) (input : Bytes) :
    parseInput publicSeed input = none ↔ ¬ HasParse publicSeed input := by
  classical
  simp [parseInput]

/-- A canonical input parses to its own parent, with candidate cells agreeing with the original
cells on the parent's children. -/
theorem parseInput_canonical (publicSeed : Digest) (cells : Cells) (parent : StructuralNode) :
    ∃ parsed, parseInput publicSeed (canonicalInput publicSeed cells parent) = some parsed ∧
      parsed.parent = parent ∧
        ∀ child ∈ parent.children, parsed.candidates child = cells child := by
  classical
  have hexists : HasParse publicSeed (canonicalInput publicSeed cells parent) :=
    ⟨⟨parent, cells⟩, rfl⟩
  have hparse : parseInput publicSeed (canonicalInput publicSeed cells parent) =
      some hexists.choose := by simp [parseInput, hexists]
  have heq := canonicalInput_eq_iff.mp (parseInput_sound hparse)
  refine ⟨hexists.choose, hparse, heq.2.1, ?_⟩
  simpa only [heq.2.1] using heq.2.2

end SlhDsaSecurity.CanonicalGraph
