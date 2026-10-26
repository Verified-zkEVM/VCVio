/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.GraphInput
public import HashSig.SLHDSA.SHAKE128s.Bridge.GraphStructure
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Input

/-!
# Exact SHAKE-128s structural byte inputs

The parameterized canonical encoder has the original graph input for every public seed, node and
cell assignment, under the existing coordinate and digest equivalences.
-/

public section

namespace SLHDSA.SHAKE128s.Bridge.GraphInput

/-- The canonical encoder retains the original byte input at every structural node. -/
theorem input_eq_canonicalInput (pk : SLHDSA.Bytes FIPS205.params.params.n)
    (cells : Graph.Node FIPS205.params.params → SLHDSA.Bytes FIPS205.params.params.n)
    (node : Graph.StructuralNode FIPS205.params.params) :
    SLHDSA.Security.GraphInput.input FIPS205.params pk node cells =
      CanonicalGraph.canonicalInput (digestEquiv.symm pk)
        (fun old => digestEquiv.symm (cells (GraphStructure.nodeEquiv.symm old)))
        (GraphStructure.structuralEquiv node) := by
  have addressBytes : node.address.toBytes =
      (GraphStructure.structuralEquiv node).address.toBytes :=
    (congrArg Adrs.toBytes (GraphStructure.structuralEquiv_address node)).symm.trans
      (toBytes_toAdrs _)
  have layout : SLHDSA.Security.GraphInput.input FIPS205.params pk node cells =
      pk.toList ++ node.address.toBytes ++
        (((node.children FIPS205.params.valid).map cells).map Vector.toList).flatten := by
    change pk.toList ++ (FIPS205.core.adrsToKey node.address).toList ++
      (((node.children FIPS205.params.valid).map cells).map Vector.toList).flatten = _
    exact congrArg (fun bytes => pk.toList ++ bytes ++
      (((node.children FIPS205.params.valid).map cells).map Vector.toList).flatten)
      (toList_adrsToKey node.address)
  rw [layout]
  unfold CanonicalGraph.canonicalInput Hashing.tweakableInput CanonicalGraph.childBytes
  rw [addressBytes]
  rw [← GraphStructure.structuralEquiv_children node]
  simp only [List.map_map]
  have seedBytes : bytesBE n (digestEquiv.symm pk) = pk.toList :=
    bytesBE_digestEquiv_symm pk
  have childBytes (child : Graph.Node FIPS205.params.params) :
      bytesBE n (digestEquiv.symm
        (cells (GraphStructure.nodeEquiv.symm (GraphStructure.nodeEquiv child)))) =
        (cells child).toList :=
    (congrArg (fun current => bytesBE n (digestEquiv.symm (cells current)))
      (GraphStructure.nodeEquiv.symm_apply_apply child)).trans
        (bytesBE_digestEquiv_symm (cells child))
  have payloadSame :
      ((node.children FIPS205.params.valid).map (fun child => bytesBE n (digestEquiv.symm
        (cells (GraphStructure.nodeEquiv.symm (GraphStructure.nodeEquiv child)))))) =
      ((node.children FIPS205.params.valid).map (fun child => (cells child).toList)) :=
    List.map_congr_left (fun child _ => childBytes child)
  exact congrArg₂ (fun seedPart payload => seedPart ++
    (GraphStructure.structuralEquiv node).address.toBytes ++ payload.flatten)
    seedBytes.symm payloadSame.symm

end SLHDSA.SHAKE128s.Bridge.GraphInput
