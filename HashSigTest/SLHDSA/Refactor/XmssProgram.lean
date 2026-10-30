/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Proof.XmssAuthentication
public import HashSig.SLHDSA.SHAKE128s.Proof.XmssRecovery

/-!
# Paper XMSS traversal and recovery observations

Bounded real paper programs retain the order of WOTS+ leaves, parent hashes and authentication
paths. Literal raw inputs distinguish full natural-number index arithmetic from premature word
truncation. The failing signer observes authentication before message signing without building
the entire fixed-parameter tree.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.XmssProgramTest

private structure Observation where
  calls : List Bytes := []
  cache : List (Bytes × HashOutput) := []
  draws : Nat := 0
  deriving DecidableEq

private def answer (position : Nat) : HashOutput :=
  (BitVec.ofNat (8 * messageDigestBytes) (position + 1)) <<<
    (8 * (messageDigestBytes - n))

private def handler (failAt : Option Nat) :
    QueryImpl HashSpec (OptionT (StateM Observation)) := fun input =>
  show StateM Observation (Option HashOutput) from do
  let state ← get
  let calls := state.calls ++ [input]
  if failAt == some state.calls.length then
    set { state with calls }
    return none
  else
    match state.cache.find? (fun entry => entry.1 == input) with
    | some entry =>
        set { state with calls }
        return some entry.2
    | none =>
        let value := answer state.calls.length
        let next : Observation :=
          { calls, cache := state.cache ++ [(input, value)], draws := state.draws + 1 }
        set next
        return some value

private def observe {α : Type} (program : OracleComp HashSpec α)
    (initial : Observation := {}) (failAt : Option Nat := none) : Option α × Observation :=
  ((simulateQ (handler failAt) program).run).run initial

private def secretSeed : Digest := 0x42
private def publicSeed : Digest := 0x23
private def message : Digest := 0

private def base : Address :=
  { layer := 2, tree := 7, kind := .forsRoots, keyPair := 3,
    chainOrHeight := 9, hashOrIndex := 11 }

-- Independent integer byte layout includes the modular reduction of each encoded word.
private def natBytes (width value : Nat) : Bytes :=
  (List.range width).reverse.map fun i => UInt8.ofNat (value / 256 ^ i)

private def raw (kind keyPair height index : Nat) (payload : Bytes) : Bytes :=
  natBytes 16 0x23 ++ natBytes 4 2 ++ natBytes 12 7 ++ natBytes 4 kind ++
    natBytes 4 keyPair ++ natBytes 4 height ++ natBytes 4 index ++ payload

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"XMSS paper-program check failed: {label}")

private def actualNode : OracleComp HashSpec Digest :=
  Merkle.node secretSeed publicSeed base 1 3

private def reversedNode : OracleComp HashSpec Digest := do
  let right ← Wots.publicKey secretSeed publicSeed (Merkle.wotsAddress base 7)
  let left ← Wots.publicKey secretSeed publicSeed (Merkle.wotsAddress base 6)
  Hashing.tweakable publicSeed (Merkle.nodeAddress base 1 3)
    (bytesBE n left ++ bytesBE n right)

private def checkNode (program : OracleComp HashSpec Digest) : IO Unit := do
  let cold := observe program
  let first := raw 5 6 0 0 (natBytes 16 0x42)
  let parent := raw 2 0 1 3 (natBytes 16 561 ++ natBytes 16 1122)
  ensure "complete small node retains left/right WOTS order and literal parent payload"
    (cold.1 == some 1123 && cold.2.calls.length == 1123 && cold.2.draws == 1123 &&
      cold.2.calls.head? == some first && cold.2.calls.getLast? == some parent)
  let repeated := observe program { cache := cold.2.cache }
  ensure "cached node retains every request and the complete cache and result"
    (repeated.1 == cold.1 && repeated.2.calls == cold.2.calls &&
      repeated.2.cache == cold.2.cache && repeated.2.draws == 0)
  let aborted := observe program {} (some 1)
  ensure "failure retains secret derivation and attempted first WOTS step"
    (aborted.1.isNone && aborted.2.calls ==
      [first, raw 0 6 0 0 (natBytes 16 1)] && aborted.2.draws == 1)

private def actualClimb (index : Nat) : OracleComp HashSpec Digest :=
  Merkle.climb publicSeed base index 42 [100, 101, 102]

private def checkClimb (indexPolicy : Nat → Nat) : IO Unit := do
  let result := observe (actualClimb (indexPolicy 13))
  let inputs :=
    [raw 2 0 1 6 (natBytes 16 100 ++ natBytes 16 42),
     raw 2 0 2 3 (natBytes 16 1 ++ natBytes 16 101),
     raw 2 0 3 1 (natBytes 16 102 ++ natBytes 16 2)]
  ensure "raw climb retains parity-dependent payload order and each ancestor address"
    (result.1 == some 3 && result.2.calls == inputs && result.2.draws == 3)
  let overflow := observe (actualClimb (indexPolicy (2 ^ 32 + 13)))
  let overflowInputs :=
    [raw 2 0 1 (2 ^ 31 + 6) (natBytes 16 100 ++ natBytes 16 42),
     raw 2 0 2 (2 ^ 30 + 3) (natBytes 16 1 ++ natBytes 16 101),
     raw 2 0 3 (2 ^ 29 + 1) (natBytes 16 102 ++ natBytes 16 2)]
  ensure "full-Nat ancestor division precedes modular address encoding"
    (overflow.1 == some 3 && overflow.2.calls == overflowInputs && overflowInputs != inputs)
  let repeated := observe (actualClimb (indexPolicy 13)) { cache := result.2.cache }
  ensure "cached climb retains attempted requests and the full cache"
    (repeated.1 == result.1 && repeated.2.calls == inputs && repeated.2.draws == 0 &&
      repeated.2.cache == result.2.cache)
  let aborted := observe (actualClimb (indexPolicy 13)) {} (some 1)
  ensure "climb failure preserves only the attempted prefix"
    (aborted.1.isNone && aborted.2.calls == inputs.take 2 && aborted.2.draws == 1)
  let empty := observe (Merkle.climb publicSeed base (2 ^ 32 + 13) 42 [])
  ensure "empty climb returns its leaf without an oracle effect"
    (empty.1 == some 42 && empty.2.calls.isEmpty && empty.2.draws == 0)

private def signature : XmssSignature :=
  { wots := fun _ => 42, authentication := fun j => BitVec.ofNat (8 * n) (100 + j.val) }

private def recovery : OracleComp HashSpec Digest :=
  Merkle.publicKeyFromSignature ⟨5, by decide⟩ signature message publicSeed base

private def checkRecovery : IO Unit := do
  let result := observe recovery
  let first := raw 0 5 0 0 (natBytes 16 42)
  let parent := raw 2 0 1 2 (natBytes 16 100 ++ natBytes 16 511)
  ensure "actual recovery finishes WOTS before the first supplied sibling"
    (result.1 == some 520 && result.2.calls.length == 520 && result.2.draws == 520 &&
      result.2.calls.head? == some first && result.2.calls[511]? == some parent)
  let repeated := observe recovery { cache := result.2.cache }
  ensure "cached recovery retains every request, result and cache"
    (repeated.1 == result.1 && repeated.2.calls == result.2.calls &&
      repeated.2.cache == result.2.cache && repeated.2.draws == 0)
  let aborted := observe recovery {} (some 511)
  ensure "recovery failure retains the complete WOTS prefix and attempted parent"
    (aborted.1.isNone && aborted.2.calls == result.2.calls.take 512 &&
      aborted.2.draws == 511 && aborted.2.cache == result.2.cache.take 511)

private def checkAuthentication : IO Unit := do
  let path := Vector.toList <$>
    (Merkle.authenticationPath secretSeed publicSeed base 2 13 : OracleComp HashSpec _)
  let result := observe path
  ensure "actual path collects leaf-first siblings before its higher sibling root"
    (result.1 == some [561, 1684] && result.2.calls.length == 1684 &&
      result.2.calls.head? == some (raw 5 12 0 0 (natBytes 16 0x42)) &&
      result.2.calls.getLast? ==
        some (raw 2 0 1 7 (natBytes 16 1122 ++ natBytes 16 1683)))
  let aborted := observe path {} (some 561)
  ensure "path failure preserves the completed lower sibling and attempted next sibling"
    (aborted.1.isNone && aborted.2.calls == result.2.calls.take 562 &&
      aborted.2.cache == result.2.cache.take 561 && aborted.2.draws == 561)
  let empty := observe (Vector.toList <$>
    (Merkle.authenticationPath secretSeed publicSeed base 0 (2 ^ 32 + 13) : OracleComp HashSpec _))
  ensure "empty authentication has no provider or hash effect"
    (empty.1 == some [] && empty.2.calls.isEmpty && empty.2.draws == 0)

private def actualSign : OracleComp HashSpec XmssSignature :=
  Merkle.sign message secretSeed publicSeed base ⟨5, by decide⟩

private def signingFirst : OracleComp HashSpec XmssSignature := do
  let wots ← Wots.sign message secretSeed publicSeed (Merkle.wotsAddress base 5)
  let authentication ← Merkle.authenticationPath secretSeed publicSeed base subtreeHeight 5
  return { wots, authentication := fun j => authentication[j] }

private def checkSigning (program : OracleComp HashSpec XmssSignature) : IO Unit := do
  let aborted := observe program {} (some 1)
  ensure "actual fixed signer evaluates authentication before message WOTS signing"
    (aborted.1.isNone && aborted.2.calls ==
      [raw 5 4 0 0 (natBytes 16 0x42), raw 0 4 0 0 (natBytes 16 1)] &&
      aborted.2.draws == 1)

/-- Execute bounded actual node, recovery, authentication and retained-effect checks. -/
def runTests : IO Unit := do
  checkNode actualNode
  checkClimb id
  checkRecovery
  checkAuthentication
  checkSigning actualSign
  IO.println "SLH-DSA paper XMSS node: PASS"
  IO.println "SLH-DSA paper XMSS recovery: PASS"
  IO.println "SLH-DSA paper XMSS authentication: PASS"

/-- Run changed computations against the same positive observation assertions. -/
def runControl (name : String) : IO Unit :=
  if name == "reverse" then checkNode reversedNode
  else if name == "normalize-index" then checkClimb (fun index => index % 2 ^ 32)
  else if name == "sign-first" then checkSigning signingFirst
  else throw (IO.userError s!"unknown XMSS program control: {name}")

end SLHDSA.SHAKE128s.XmssProgramTest
