/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalTarget
public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthCharge

/-!
# Deviating structural collisions

`DeviatingCollision` is the event that a charged phase produced a child tuple deviating from
the honest cells at some parent node, whose cached answer nevertheless reproduces that node's
honest value. It is precisely the shape of every witness `Extraction.*` yields for a structural
fault of an accepted forgery.

`CanonicalTarget.hit_of_deviating_collision` recognises such a witness as a charged hit, and
`CanonicalTarget.clean_of_canonical_cache` certifies that a cache built only from honest
canonical queries starts clean, so the event is charged at `2 ^ -128` per query, linear in the
budget and independent of how many honest node values exist.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.StructuralTerm

open CanonicalGraph

/-- The phase produced a child tuple deviating from the honest cells at some parent node,
whose cached answer nevertheless reproduces that node's honest value. This is precisely the
shape of every witness the structural extraction yields. -/
@[expose] def DeviatingCollision {α : Type} (publicSeed : Digest) (cells : Cells) :
    α × QueryCache HashSpec → Prop := fun result =>
  ∃ (candidates : Cells) (parent : StructuralNode) (output : HashOutput),
    (∃ child ∈ parent.children, candidates child ≠ cells child) ∧
    result.2 (canonicalInput publicSeed candidates parent) = some output ∧
    Hashing.truncate output = cells (.structural parent)

end SLHDSA.SHAKE128s.StructuralTerm
