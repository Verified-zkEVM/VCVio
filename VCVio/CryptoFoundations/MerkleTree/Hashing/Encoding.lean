/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Hashing.Defs

/-!
# Common-domain Merkle hashing

Leaf and node requests are interpreted in one oracle domain. The two encodings are injective
within each role and address; their ranges may overlap. Both roles query the same oracle cell
when their encoded inputs agree.
-/

public section

namespace MerkleTreeHashing

open OracleComp OracleSpec

universe u v w x y

/-- Encodings of leaf payloads and ordered child labels into one oracle domain. -/
structure QueryEncoding (X : Type u) (LeafAddress : Type v) (NodeAddress : Type w)
    (Payload : Type x) (Y : Type y) where
  /-- Actual input of a leaf query. -/
  leaf : LeafAddress → Payload → X
  /-- Actual input of a node query. -/
  node : NodeAddress → Y × Y → X
  /-- At a fixed address the leaf input determines the payload. -/
  leaf_injective : ∀ a, Function.Injective (leaf a)
  /-- At a fixed address the node input determines both children. -/
  node_injective : ∀ a, Function.Injective (node a)

namespace QueryEncoding

variable {X : Type u} {LeafAddress : Type v} {NodeAddress : Type w}
  {Payload : Type x} {Y : Type y}

/-- Interpret the role-tagged syntax as an actual oracle input. -/
@[expose]
def encodeQuery (enc : QueryEncoding X LeafAddress NodeAddress Payload Y) :
    HashQuery LeafAddress NodeAddress Payload Y → X
  | .leaf a p => enc.leaf a p
  | .node a l r => enc.node a (l, r)

/-- Each abstract hash request makes one query to the common oracle. -/
@[expose]
def queryImpl (enc : QueryEncoding X LeafAddress NodeAddress Payload Y) :
    QueryImpl (spec LeafAddress NodeAddress Payload Y) (OracleComp (X →ₒ Y)) :=
  fun q => (X →ₒ Y).query (enc.encodeQuery q)

/-- Equal encoded inputs access the same oracle computation, irrespective of their roles. -/
theorem queryImpl_eq_of_encodeQuery_eq (enc : QueryEncoding X LeafAddress NodeAddress Payload Y)
    {q r : HashQuery LeafAddress NodeAddress Payload Y}
    (h : enc.encodeQuery q = enc.encodeQuery r) :
    enc.queryImpl q = enc.queryImpl r := by
  unfold queryImpl
  congr 2

end QueryEncoding

/-- A sound partial inverse for one role at one address.
Different roles may decode the same input. -/
structure RoleDecoder {X : Type u} {Payload : Type v} (encode : Payload → X) where
  /-- Recognize inputs belonging to this role. -/
  decode : X → Option Payload
  /-- Every constructed input is recognized. -/
  decode_encode : ∀ p, decode (encode p) = some p
  /-- Every recognized input is constructed from the decoded payload. -/
  encode_decode : ∀ x p, decode x = some p → encode p = x

namespace RoleDecoder
variable {X : Type u} {Payload : Type v} {encode : Payload → X}

/-- An injective role encoding has a partial inverse; no efficient parsing claim is required. -/
noncomputable def ofInjective (encode : Payload → X) (hinj : Function.Injective encode) :
    RoleDecoder encode where
  decode := Function.partialInv encode
  decode_encode := hinj.isPartialInv.eq
  encode_decode x p h := (hinj.isPartialInv p x).mp h

/-- Decoding succeeds exactly at the encoded payload. -/
theorem decode_eq_some_iff (decoder : RoleDecoder encode) (x : X) (p : Payload) :
    decoder.decode x = some p ↔ encode p = x := by
  constructor
  · exact decoder.encode_decode x p
  · rintro rfl
    exact decoder.decode_encode p

end RoleDecoder

end MerkleTreeHashing
