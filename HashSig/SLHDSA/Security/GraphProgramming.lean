/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal.Programming
public import HashSig.SLHDSA.Security.GraphInput
public import HashSig.SLHDSA.Graph.Input
public import HashSig.SLHDSA.Graph.Fors.Dependencies

/-!
# Programming the canonical FORS subtree and signing forest

The target overlays the scheduled structural cells with the canonical prefix of a supplied
full-answer table. Every unscheduled cell, including the independent seed, retains its initial
value. Actual child-prefix geometry supplies read-before-write for the existing traversal.
The laws preserve its complete final state and the cache written in the same call order.
No width, full-digest fit, freshness, sampling or resource assumption is imposed.
-/

public section

open OracleComp OracleSpec RandomOracleTraversal RandomOracleTraversal.Programming
open SLHDSA.Graph

namespace SLHDSA.Security.GraphProgramming

/-- Full-answer outputs overlay only scheduled structural cells. -/
@[expose] def tableTarget (vp : ValidatedParams)
    (nodes : List (Graph.StructuralNode vp.params))
    (initial : Graph.Node vp.params → Bytes vp.params.n)
    (outputs : Graph.StructuralNode vp.params → Bytes vp.params.m) :
    Graph.Node vp.params → Bytes vp.params.n
  | .secretSeed => initial .secretSeed
  | .structural parent =>
      if parent ∈ nodes then prefixBytes vp.params.n (outputs parent)
      else initial (.structural parent)

private theorem readBeforeWrite {p : Params} (valid : p.Valid)
    (nodes : List (StructuralNode p)) (unique : nodes.Nodup)
    (ready : ∀ (position : Fin nodes.length) (child : StructuralNode p),
      Node.structural child ∈ (nodes[position]).children valid → child ∈ nodes.take position.val) :
    ReadBeforeWrite (fun parent => Node.structural parent)
      (fun parent => parent.children valid) nodes := by
  intro position child member later occurs same
  subst child
  have earlier := ready position later member
  have disjoint : List.Disjoint (nodes.take position.val) (nodes.drop position.val) := by
    have full : (nodes.take position.val ++ nodes.drop position.val).Nodup := by
      simpa only [List.take_append_drop] using unique
    exact (List.nodup_append'.mp full).2.2
  exact List.disjoint_left.mp disjoint earlier occurs

private theorem initial_agrees (vp : ValidatedParams) (nodes : List (StructuralNode vp.params))
    (initial : Node vp.params → Bytes vp.params.n)
    (outputs : StructuralNode vp.params → Bytes vp.params.m) :
    AgreesOutside (fun parent => Node.structural parent) nodes initial
      (tableTarget vp nodes initial outputs) := by
  intro key outside
  cases key with
  | secretSeed => rfl
  | structural parent =>
      have absent : parent ∉ nodes := fun member => outside parent member rfl
      simp only [tableTarget, absent, ↓reduceIte]

private theorem consistent (vp : ValidatedParams) (nodes : List (StructuralNode vp.params))
    (initial : Node vp.params → Bytes vp.params.n)
    (outputs : StructuralNode vp.params → Bytes vp.params.m)
    (parent : StructuralNode vp.params) (member : parent ∈ nodes) :
    prefixBytes vp.params.n (outputs parent) =
      tableTarget vp nodes initial outputs (.structural parent) := by
  simp only [tableTarget, member, ↓reduceIte]

/-- Canonical subtree programming retains every boundary cell and every full cached answer. -/
theorem subtree_program (vp : ValidatedParams) (pk : Bytes vp.params.n)
    (key : Graph.ForsKey vp.params) (height : Nat) (bound : height ≤ vp.params.a)
    (index : Fin (vp.params.k * 2 ^ (vp.params.a - height)))
    (initial : Graph.Node vp.params → Bytes vp.params.n)
    (outputs : Graph.StructuralNode vp.params → Bytes vp.params.m)
    (cache : QueryCache (List Byte →ₒ Bytes vp.params.m)) :
    let nodes := Graph.ForsSchedule.subtree key height bound index
    let target := tableTarget vp nodes initial outputs
    RandomOracleTraversal.program (GraphInput.input vp pk)
      (fun parent cells answer => Graph.updateCell parent cells (prefixBytes vp.params.n answer))
      outputs nodes initial cache =
      (target, OracleComp.RandomOracleTraversal.Programming.cacheFrom
        (fun parent => GraphInput.input vp pk parent target) outputs nodes cache) := by
  exact program_eq_cacheFrom (fun parent => Node.structural parent)
    (fun parent => parent.children vp.valid) (GraphInput.input vp pk)
    (fun _ answer => prefixBytes vp.params.n answer) (GraphInput.input_congr vp pk)
    outputs (ForsSchedule.subtree key height bound index) initial
    (tableTarget vp _ initial outputs)
    (readBeforeWrite vp.valid _ (ForsSchedule.subtree_nodup key height bound index)
      (ForsSchedule.subtree_children_before vp.valid key height bound index))
    (initial_agrees vp _ initial outputs) (consistent vp _ initial outputs) cache

/-- Canonical signing-forest programming retains boundary cells and the full ordered cache. -/
theorem signing_program (vp : ValidatedParams) (pk : Bytes vp.params.n)
    (key : Graph.ForsKey vp.params) (md : List Byte)
    (initial : Graph.Node vp.params → Bytes vp.params.n)
    (outputs : Graph.StructuralNode vp.params → Bytes vp.params.m)
    (cache : QueryCache (List Byte →ₒ Bytes vp.params.m)) :
    let nodes := Graph.ForsSchedule.signing key md
    let target := tableTarget vp nodes initial outputs
    RandomOracleTraversal.program (GraphInput.input vp pk)
      (fun parent cells answer => Graph.updateCell parent cells (prefixBytes vp.params.n answer))
      outputs nodes initial cache =
      (target, OracleComp.RandomOracleTraversal.Programming.cacheFrom
        (fun parent => GraphInput.input vp pk parent target) outputs nodes cache) := by
  exact program_eq_cacheFrom (fun parent => Node.structural parent)
    (fun parent => parent.children vp.valid) (GraphInput.input vp pk)
    (fun _ answer => prefixBytes vp.params.n answer) (GraphInput.input_congr vp pk)
    outputs (ForsSchedule.signing key md) initial (tableTarget vp _ initial outputs)
    (readBeforeWrite vp.valid _ (ForsSchedule.signing_nodup key md)
      (ForsSchedule.signing_children_before vp.valid key md))
    (initial_agrees vp _ initial outputs) (consistent vp _ initial outputs) cache

end SLHDSA.Security.GraphProgramming
