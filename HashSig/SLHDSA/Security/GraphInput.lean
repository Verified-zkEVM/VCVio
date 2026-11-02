/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Children
public import HashSig.SLHDSA.Graph.Encoding
public import HashSig.SLHDSA.Security.ByteModel
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal

/-!
# Canonical SHAKE inputs for parameterized structural nodes

Each input uses the canonical encoder, public seed, natural node address and ordered child cells.
Local address widths identify the seed, parent and child values from the encoded input, and
separate distinct structural nodes for all payload states. Cache freshness and separation from
other oracle roles require their own facts.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.Security.GraphInput

/-- The actual canonical SHAKE encoding of a structural node's ordered hash payload. -/
@[expose] def input (vp : ValidatedParams) (pk : Bytes vp.params.n)
    (node : Graph.StructuralNode vp.params) (cells : Graph.Node vp.params → Bytes vp.params.n) :
    List Byte :=
  encode vp (.inl (.thash pk ((shakeCore vp).adrsToKey node.address)
    ((node.children vp.valid).map cells)))

/-- Inputs depend only on the cells of the actual ordered children, without a width premise. -/
theorem input_congr (vp : ValidatedParams) (pk : Bytes vp.params.n)
    (node : Graph.StructuralNode vp.params) (left right : Graph.Node vp.params → Bytes vp.params.n)
    (same : ∀ child ∈ node.children vp.valid, left child = right child) :
    input vp pk node left = input vp pk node right :=
  congrArg (fun values =>
    encode vp (.inl (.thash pk ((shakeCore vp).adrsToKey node.address) values)))
    (List.map_congr_left same)

/-- Canonical inputs determine the seed, parent and the cells of all ordered children. -/
theorem input_eq_iff (vp : ValidatedParams) (widths : Graph.Widths vp.params)
    {pk pk' : Bytes vp.params.n} {left right : Graph.Node vp.params → Bytes vp.params.n}
    {parent parent' : Graph.StructuralNode vp.params} :
    input vp pk parent left = input vp pk' parent' right ↔
      pk = pk' ∧ parent = parent' ∧
        ∀ child ∈ parent.children vp.valid, left child = right child := by
  have encoded := @encode_thash_inj vp pk pk'
    ((shakeCore vp).adrsToKey parent.address) ((shakeCore vp).adrsToKey parent'.address)
    ((parent.children vp.valid).map left) ((parent'.children vp.valid).map right)
  refine encoded.trans ?_
  constructor
  · rintro ⟨seedSame, addressSame, childrenSame⟩
    have parentSame : parent = parent' :=
      Graph.StructuralNode.toVector_address_injective widths addressSame
    subst parent'
    exact ⟨seedSame, rfl, List.map_inj_left.mp childrenSame⟩
  · rintro ⟨rfl, rfl, childrenSame⟩
    exact ⟨rfl, rfl, List.map_congr_left childrenSame⟩

/-- Different structural nodes have different inputs for every pair of payload assignments. -/
theorem input_separated (vp : ValidatedParams) (widths : Graph.Widths vp.params)
    (pk : Bytes vp.params.n) :
    RandomOracleTraversal.Separated
      (fun (node : Graph.StructuralNode vp.params)
        (cells : Graph.Node vp.params → Bytes vp.params.n) => input vp pk node cells) := by
  intro left right different leftCells rightCells same
  exact different ((input_eq_iff vp widths).mp same).2.1

end SLHDSA.Security.GraphInput
