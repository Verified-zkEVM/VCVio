/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SecretProvider

/-!
# FORS selected-secret evaluation order

A height-two forest distinguishes the selected-secret draw from sibling subtree evaluation.
The complete callback trace pins the selected-secret-first schedule, both tree offsets,
leaf-to-root authentication order and left-to-right node inputs.
-/

public section

namespace SLHDSA.ForsSecretOrderTest

/-- Two height-two FORS trees over one-byte parameters. -/
@[expose] def params : Params :=
  { n := 1, h := 1, d := 1, hp := 1, a := 2, k := 2, lgw := 1 }

/-- A deterministic natural-number context with address-distinguishing secret values. -/
@[expose, reducible] def core : CorePrimitives params where
  PkSeed := Unit
  SkSeed := Unit
  SkPrf := Unit
  Y := Nat
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun _ _ a => 100 + a.word3
  PRFmsg := fun _ _ _ => 0
  yToBytes := fun x => #v[UInt8.ofNat x]

/-- Provider draws and public hash callbacks, including their exact addresses and inputs. -/
inductive Event where
  | secret (address : Adrs)
  | leafHash (address : Adrs) (input : Nat)
  | nodeHash (address : Adrs) (left right : Nat)
  deriving DecidableEq, Repr

/-- Record a secret draw and return its address-dependent value. -/
def secret (a : Adrs) : StateM (List Event) Nat := do
  modify (· ++ [.secret a])
  return 100 + a.word3

/-- Record a leaf hash and retain both its address and input in the result. -/
def hash (a : Adrs) (x : Nat) : StateM (List Event) Nat := do
  modify (· ++ [.leafHash a x])
  return 1000 + 10 * a.word3 + x

/-- Record a parent hash whose value distinguishes height, index and ordered children. -/
def nodeHash (a : Adrs) (left right : Nat) : StateM (List Event) Nat := do
  modify (· ++ [.nodeHash a left right])
  return 10000 + 100 * a.word2 + a.word3 + left + 2 * right

/-- A nonzero forest location and key-pair coordinate. -/
def base : Adrs := ⟨2, 7, 3, 3, 0, 0⟩

/-- Expected addresses are literal field layouts, independent of the production builders. -/
def secretAddress (i : Nat) : Adrs := ⟨2, 7, 6, 3, 0, i⟩

/-- Literal expected leaf-hash address at global index `i`. -/
def leafAddress (i : Nat) : Adrs := ⟨2, 7, 3, 3, 0, i⟩

/-- Literal expected height-one parent address at global index `i`. -/
def parentAddress (i : Nat) : Adrs := ⟨2, 7, 3, 3, 1, i⟩

/-- Selected-secret-first evaluation for digest `0x60`, including sibling-only path work. -/
def expectedTrace : List Event := [
  .secret (secretAddress 1),
  .secret (secretAddress 0), .leafHash (leafAddress 0) 100,
  .secret (secretAddress 2), .leafHash (leafAddress 2) 102,
  .secret (secretAddress 3), .leafHash (leafAddress 3) 103,
  .nodeHash (parentAddress 1) 1122 1133,
  .secret (secretAddress 6),
  .secret (secretAddress 7), .leafHash (leafAddress 7) 107,
  .secret (secretAddress 4), .leafHash (leafAddress 4) 104,
  .secret (secretAddress 5), .leafHash (leafAddress 5) 105,
  .nodeHash (parentAddress 2) 1144 1155]

/-- Fail the executable when an assertion is false. -/
def ensure (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"FORS secret-order check failed: {label}")

/-- Retain public hash traffic while forgetting provider draws. -/
def publicEvents (events : List Event) : List Event :=
  events.filter fun event => match event with
    | .secret _ => false
    | _ => true

/-- Assert exact signature fields, callback order and agreement with the honest provider. -/
def check : IO Unit := do
  let (signature, trace) :=
    (forsSignWithSecret core hash nodeHash secret [0x60] base).run []
  let fields := signature.toList.map fun tree => (tree.sk, tree.auth.toList)
  ensure "selected secrets and leaf-to-root paths"
    (fields == [(101, [1100, 13489]), (106, [1177, 13556])])
  ensure "selected secret precedes all sibling work in each tree"
    (decide (trace = expectedTrace))
  let (honest, honestTrace) :=
    (forsSignWith core hash nodeHash [0x60] () () base).run []
  ensure "honest provider preserves signature fields"
    (fields == honest.toList.map fun tree => (tree.sk, tree.auth.toList))
  ensure "honest provider preserves public hash traffic"
    (decide (publicEvents trace = honestTrace))
  IO.println "SLH-DSA FORS selected-secret order: PASS"

end SLHDSA.ForsSecretOrderTest

/-- Execute the FORS selected-secret order regression. -/
def main : IO Unit := SLHDSA.ForsSecretOrderTest.check
