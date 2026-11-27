/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Children
public import HashSig.SLHDSA.SHAKE128s.Bridge.GraphStructure

/-!
# Structural graph clients at two FIPS parameter sets

The same coordinate types and child-rank theorem apply to SHAKE-128s and SHAKE-192f. Literal
ordered-child checks cover their distinct WOTS and FORS dimensions and the positive-height
XMSS offset. The full rectangular tree domains remain available at every layer.
-/

public section

namespace SLHDSA.Refactor.GraphStructureTest

local notation "vp128" => FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams
local notation "vp192" => FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams
local notation "p128" => FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams.params
local notation "p192" => FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams.params

/-- Every actual SHAKE-128s dependency decreases the common structural rank. -/
theorem shake128s_child_rank (parent : Graph.StructuralNode p128) (child : Graph.Node p128)
    (member : child ∈ parent.children (vp128).valid) : child.rank < parent.rank :=
  Graph.StructuralNode.child_rank_lt (vp128).valid parent child member

/-- Every actual SHAKE-192f dependency decreases the same structural rank. -/
theorem shake192f_child_rank (parent : Graph.StructuralNode p192) (child : Graph.Node p192)
    (member : child ∈ parent.children (vp192).valid) : child.rank < parent.rank :=
  Graph.StructuralNode.child_rank_lt (vp192).valid parent child member

example : Finite (Graph.Node p128) := inferInstance
example : Finite (Graph.Node p192) := inferInstance

example : ((p128).len, (p128).m, (p128).hp, (p128).a, (p128).k) = (35, 30, 9, 12, 14) := rfl
example : ((p192).len, (p192).m, (p192).hp, (p192).a, (p192).k) = (51, 42, 3, 8, 33) := rfl

example (key : Graph.WotsKey p128) :
    (Graph.StructuralNode.wotsPk key).children (vp128).valid =
      List.ofFn (fun chain : Fin 35 =>
        Graph.Node.structural (.wotsHash key chain (14 : Fin 15))) := rfl

example (key : Graph.WotsKey p192) :
    (Graph.StructuralNode.wotsPk key).children (vp192).valid =
      List.ofFn (fun chain : Fin 51 =>
        Graph.Node.structural (.wotsHash key chain (14 : Fin 15))) := rfl

example (key : Graph.ForsKey p192) :
    (Graph.StructuralNode.forsTree key (8 : Fin 9) (32 : Fin 33)).children (vp192).valid =
      [.structural (.forsTree key (7 : Fin 9) (64 : Fin 66)),
        .structural (.forsTree key (7 : Fin 9) (65 : Fin 66))] := rfl

example (key : Graph.ForsKey p192) :
    (Graph.StructuralNode.forsTree key (0 : Fin 9) (8447 : Fin 8448)).children (vp192).valid =
      [.structural (.forsPrf key (8447 : Fin 8448))] := rfl

example (key : Graph.ForsKey p192) :
    (Graph.StructuralNode.forsRoots key).children (vp192).valid =
      List.ofFn (fun tree : Fin 33 =>
        Graph.Node.structural (.forsTree key (8 : Fin 9) tree)) := rfl

example (location : Graph.Tree p192) :
    (Graph.StructuralNode.tree location (2 : Fin 3) (0 : Fin 1)).children (vp192).valid =
      [.structural (.tree location (1 : Fin 3) (0 : Fin 2)),
        .structural (.tree location (1 : Fin 3) (1 : Fin 2))] := rfl

example (location : Graph.Tree p128) :
    (Graph.StructuralNode.tree location (8 : Fin 9) (0 : Fin 1)).rank = 26 := rfl

example (location : Graph.Tree p192) :
    (Graph.StructuralNode.tree location (2 : Fin 3) (0 : Fin 1)).rank = 20 := rfl

example (key : Graph.WotsKey p192) : (Graph.StructuralNode.wotsPk key).rank = 17 := rfl

example : (Graph.Tree.mk (p := p128) (6 : Fin 7) (18014398509481983 : Fin (2 ^ 54))).tree =
    (18014398509481983 : Fin (2 ^ 54)) := rfl

example : (Graph.Tree.mk (p := p192) (21 : Fin 22) (9223372036854775807 : Fin (2 ^ 63))).tree =
    (9223372036854775807 : Fin (2 ^ 63)) := rfl

/-- The ordinary bridge recovers every existing ordered SHAKE-128s dependency list. -/
theorem shake128s_ordered_children (parent : Graph.StructuralNode p128) :
    (parent.children (vp128).valid).map SHAKE128s.Bridge.GraphStructure.nodeEquiv =
      (SHAKE128s.Bridge.GraphStructure.structuralEquiv parent).children :=
  SHAKE128s.Bridge.GraphStructure.structuralEquiv_children parent

/-- The ordinary bridge recovers all six existing SHAKE-128s natural address fields. -/
theorem shake128s_address (node : Graph.StructuralNode p128) :
    SHAKE128s.Bridge.toAdrs (SHAKE128s.Bridge.GraphStructure.structuralEquiv node).address =
      node.address :=
  SHAKE128s.Bridge.GraphStructure.structuralEquiv_address node

end SLHDSA.Refactor.GraphStructureTest
