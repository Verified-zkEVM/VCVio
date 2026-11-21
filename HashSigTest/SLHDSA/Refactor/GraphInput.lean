/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.GraphInput
public import HashSig.SLHDSA.SHAKE128s.Bridge.GraphInput
public import HashSigTest.SLHDSA.Refactor.GraphEncoding

/-!
# Canonical structural input clients

The actual 128s and 192f parameters instantiate exact input recovery and all-state node separation.
Literal 192f sibling payloads retain their order, while the original 128s input is recovered for
arbitrary seeds and cells. A populated cache still prevents the separate freshness condition.
-/

public section

open OracleComp OracleSpec SLHDSA.Security

namespace SLHDSA.Refactor.GraphInputTest

local notation "vp128" => FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams
local notation "vp192" => FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams

/-- Actual 128s inputs identify the seed, parent and every child cell. -/
theorem shake128s_input_eq_iff
    {pk pk' : Bytes (vp128).params.n}
    {left right : Graph.Node (vp128).params → Bytes (vp128).params.n}
    {parent parent' : Graph.StructuralNode (vp128).params} :
    GraphInput.input vp128 pk parent left = GraphInput.input vp128 pk' parent' right ↔
      pk = pk' ∧ parent = parent' ∧
        ∀ child ∈ parent.children (vp128).valid, left child = right child :=
  GraphInput.input_eq_iff vp128 GraphEncodingTest.shake128s_widths

/-- Actual 192f uses the same exact input-recovery theorem at its different dimensions. -/
theorem shake192f_input_eq_iff
    {pk pk' : Bytes (vp192).params.n}
    {left right : Graph.Node (vp192).params → Bytes (vp192).params.n}
    {parent parent' : Graph.StructuralNode (vp192).params} :
    GraphInput.input vp192 pk parent left = GraphInput.input vp192 pk' parent' right ↔
      pk = pk' ∧ parent = parent' ∧
        ∀ child ∈ parent.children (vp192).valid, left child = right child :=
  GraphInput.input_eq_iff vp192 GraphEncodingTest.shake192f_widths

/-- Actual 128s node namespaces remain disjoint over all payload assignments. -/
theorem shake128s_input_separated (pk : Bytes (vp128).params.n) :
    RandomOracleTraversal.Separated
      (fun (node : Graph.StructuralNode (vp128).params)
        (cells : Graph.Node (vp128).params → Bytes (vp128).params.n) =>
          GraphInput.input vp128 pk node cells) :=
  GraphInput.input_separated vp128 GraphEncodingTest.shake128s_widths pk

/-- Actual 192f node namespaces satisfy the same all-payload condition. -/
theorem shake192f_input_separated (pk : Bytes (vp192).params.n) :
    RandomOracleTraversal.Separated
      (fun (node : Graph.StructuralNode (vp192).params)
        (cells : Graph.Node (vp192).params → Bytes (vp192).params.n) =>
          GraphInput.input vp192 pk node cells) :=
  GraphInput.input_separated vp192 GraphEncodingTest.shake192f_widths pk

/-- The ordinary canonical input depends on its child values without encoding certificates. -/
theorem input_congr_all_params (vp : ValidatedParams) (pk : Bytes vp.params.n)
    (node : Graph.StructuralNode vp.params) (left right : Graph.Node vp.params → Bytes vp.params.n)
    (same : ∀ child ∈ node.children vp.valid, left child = right child) :
    GraphInput.input vp pk node left = GraphInput.input vp pk node right :=
  GraphInput.input_congr vp pk node left right same

/-- Exact old 128s inputs are obtained through the live coordinate and digest equivalences. -/
theorem shake128s_original_input (pk : Bytes (vp128).params.n)
    (cells : Graph.Node (vp128).params → Bytes (vp128).params.n)
    (node : Graph.StructuralNode (vp128).params) :
    GraphInput.input vp128 pk node cells =
      SHAKE128s.CanonicalGraph.canonicalInput (SHAKE128s.Bridge.digestEquiv.symm pk)
        (fun old => SHAKE128s.Bridge.digestEquiv.symm
          (cells (SHAKE128s.Bridge.GraphStructure.nodeEquiv.symm old)))
        (SHAKE128s.Bridge.GraphStructure.structuralEquiv node) :=
  SHAKE128s.Bridge.GraphInput.input_eq_canonicalInput pk cells node

example (key : Graph.ForsKey (vp192).params) (pk : Bytes (vp192).params.n)
    (cells : Graph.Node (vp192).params → Bytes (vp192).params.n) :
    GraphInput.input vp192 pk (.forsTree key (1 : Fin 9) (0 : Fin 4224)) cells =
      encode vp192 (.inl (.thash pk
        ((shakeCore vp192).adrsToKey ⟨0, key.tree, 3, key.leaf, 1, 0⟩)
        [cells (.structural (.forsTree key (0 : Fin 9) (0 : Fin 8448))),
          cells (.structural (.forsTree key (0 : Fin 9) (1 : Fin 8448)))])) := rfl

/-- A cached actual 192f input blocks freshness despite the disjoint structural namespaces. -/
theorem cached_input_not_fresh (pk : Bytes (vp192).params.n)
    (node : Graph.StructuralNode (vp192).params)
    (cells : Graph.Node (vp192).params → Bytes (vp192).params.n)
    (answer : Bytes (vp192).params.m) :
    ¬ RandomOracleTraversal.FreshFor
      (fun (parent : Graph.StructuralNode (vp192).params)
        (state : Graph.Node (vp192).params → Bytes (vp192).params.n) =>
          GraphInput.input vp192 pk parent state) [node]
      ((∅ : QueryCache (shakeSpec vp192)).cacheQuery
        (GraphInput.input vp192 pk node cells) answer) := by
  intro fresh
  have absent := fresh node (by simp) cells
  simp at absent

end SLHDSA.Refactor.GraphInputTest
