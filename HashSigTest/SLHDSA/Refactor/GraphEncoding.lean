/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Encoding
public import HashSig.SLHDSA.Security.ByteModel
public import HashSig.SLHDSA.SHAKE128s.Bridge.GraphStructure

/-!
# Structural address clients and encoding scope checks

Actual SHAKE-128s and SHAKE-192f parameters supply explicit width certificates. The full
serialized addresses distinguish their nodes, and the original 128s address bytes are recovered.
A mathematically valid forest with a long enough answer demonstrates why byte representability
is a separate condition: distinct natural indices collide under the actual address and hash-input
encoders.
-/

public section

namespace SLHDSA.Refactor.GraphEncodingTest

local notation "p128" => FipsParameterSet.SLHDSA_SHAKE_128s.params
local notation "p192" => FipsParameterSet.SLHDSA_SHAKE_192f.params

/-- The complete actual SHAKE-128s coordinate domains fit the full address fields. -/
theorem shake128s_widths : Graph.Widths p128 := by
  constructor <;> decide

/-- The complete actual SHAKE-192f coordinate domains fit the same address fields. -/
theorem shake192f_widths : Graph.Widths p192 := by
  constructor <;> decide

/-- The actual full address codec distinguishes all actual SHAKE-128s structural nodes. -/
theorem shake128s_encoding_injective :
    Function.Injective (fun node : Graph.StructuralNode p128 => node.address.toVector) :=
  Graph.StructuralNode.toVector_address_injective shake128s_widths

/-- The same generic encoding theorem distinguishes all actual SHAKE-192f structural nodes. -/
theorem shake192f_encoding_injective :
    Function.Injective (fun node : Graph.StructuralNode p192 => node.address.toVector) :=
  Graph.StructuralNode.toVector_address_injective shake192f_widths

/-- Every actual SHAKE-128s address parses to the same natural fields after serialization. -/
theorem shake128s_roundtrip (node : Graph.StructuralNode p128) :
    Adrs.fromVector node.address.toVector = node.address :=
  node.fromVector_toVector_address shake128s_widths

/-- The same roundtrip theorem applies to every actual SHAKE-192f address. -/
theorem shake192f_roundtrip (node : Graph.StructuralNode p192) :
    Adrs.fromVector node.address.toVector = node.address :=
  node.fromVector_toVector_address shake192f_widths

/-- Serialized addresses retain the original 128s bit-vector address bytes exactly. -/
theorem shake128s_original_bytes (node : Graph.StructuralNode p128) :
    node.address.toBytes =
      (SHAKE128s.Bridge.GraphStructure.structuralEquiv node).address.toBytes := by
  exact (congrArg Adrs.toBytes
    (SHAKE128s.Bridge.GraphStructure.structuralEquiv_address node)).symm.trans
      (SHAKE128s.Bridge.toBytes_toAdrs _)

example (key : Graph.ForsKey p192) :
    Adrs.fromVector (Graph.StructuralNode.forsPrf key (8447 : Fin 8448)).address.toVector =
      ⟨0, key.tree, 6, key.leaf, 0, 8447⟩ :=
  Graph.StructuralNode.fromVector_toVector_address shake192f_widths _

example (key : Graph.WotsKey p192) :
    Adrs.fromVector
      (Graph.StructuralNode.wotsHash key (50 : Fin 51) (14 : Fin 15)).address.toVector =
      ⟨key.tree.layer, key.tree.tree, 0, key.leaf, 50, 14⟩ :=
  Graph.StructuralNode.fromVector_toVector_address shake192f_widths _

private abbrev wideForest : Params :=
  { n := 16, h := 63, d := 7, hp := 9, a := 33, k := 2, lgw := 4 }

private theorem wideForest_valid : wideForest.Valid := by decide
private theorem wideForest_prefix : wideForest.n ≤ wideForest.m := by decide
private abbrev wideVp : ValidatedParams := ⟨wideForest, wideForest_valid⟩
private def wideKey : Graph.ForsKey wideForest := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
private def leftNode : Graph.StructuralNode wideForest := .forsPrf wideKey ⟨0, by decide⟩
private def rightNode : Graph.StructuralNode wideForest := .forsPrf wideKey ⟨2 ^ 32, by decide⟩

private theorem wideForest_distinct :
    leftNode ≠ rightNode ∧ leftNode.address ≠ rightNode.address := by
  constructor
  · intro equal
    have bad : 0 = 2 ^ 32 := congrArg (fun node => node.address.word3) equal
    norm_num at bad
  · intro equal
    have bad : 0 = 2 ^ 32 := congrArg Adrs.word3 equal
    norm_num at bad

private theorem wideForest_address_collision :
    leftNode.address.toVector = rightNode.address.toVector := by
  decide

private def zeroSeed : Bytes wideForest.n := Vector.replicate 16 0

private def actualPrfInput (node : Graph.StructuralNode wideForest) : List Byte :=
  Security.encode wideVp (.inl (.thash zeroSeed
    ((Security.shakeCore wideVp).adrsToKey node.address) [zeroSeed]))

private theorem wideForest_input_collision :
    actualPrfInput leftNode = actualPrfInput rightNode := by
  decide

/-- Mathematical validity and sufficient answer length do not imply address capacities. -/
theorem valid_prefix_do_not_imply_widths :
    ¬ ∀ p : Params, p.Valid → p.n ≤ p.m → Graph.Widths p := by
  intro all
  have bad := (all wideForest wideForest_valid wideForest_prefix).forsIndex
  norm_num at bad

/-- Even with both other conditions, full serialized-address injectivity can fail. -/
theorem valid_prefix_do_not_imply_encoding_injective :
    ¬ ∀ p : Params, p.Valid → p.n ≤ p.m →
      Function.Injective (fun node : Graph.StructuralNode p => node.address.toVector) := by
  intro all
  exact wideForest_distinct.1
    (all wideForest wideForest_valid wideForest_prefix wideForest_address_collision)

/-- The actual canonical encoder can collide despite mathematical validity and prefix length. -/
theorem valid_prefix_encoder_collision :
    ∃ (vp : ValidatedParams) (seed : Bytes vp.params.n)
      (left right : Graph.StructuralNode vp.params),
      vp.params.n ≤ vp.params.m ∧ left ≠ right ∧ left.address ≠ right.address ∧
        Security.encode vp (.inl (.thash seed
          ((Security.shakeCore vp).adrsToKey left.address) [seed])) =
        Security.encode vp (.inl (.thash seed
          ((Security.shakeCore vp).adrsToKey right.address) [seed])) :=
  ⟨wideVp, zeroSeed, leftNode, rightNode, wideForest_prefix,
    wideForest_distinct.1, wideForest_distinct.2, wideForest_input_collision⟩

end SLHDSA.Refactor.GraphEncodingTest
