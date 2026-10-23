/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Input

/-!
An input-only parser for the canonical graph. The parser uses only the public seed and
query bytes. Its candidate table is a witness reconstructed from those bytes, not the
secret table. Values at coordinates outside the parsed parent's children are irrelevant.
The parser is noncomputable because efficiency is immaterial for the query-count reduction.
-/

@[expose] public section

namespace SlhDsaSecurity.CanonicalGraph

structure ParsedInput where
  parent : StructuralNode
  candidates : Cells

def HasParse (publicSeed : Digest) (input : Bytes) : Prop :=
  ∃ parsed : ParsedInput, canonicalInput publicSeed parsed.candidates parsed.parent = input

noncomputable def parseInput (publicSeed : Digest) (input : Bytes) : Option ParsedInput := by
  classical
  exact if h : HasParse publicSeed input then some h.choose else none

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

theorem parseInput_none_iff (publicSeed : Digest) (input : Bytes) :
    parseInput publicSeed input = none ↔ ¬ HasParse publicSeed input := by
  classical
  simp [parseInput]

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
