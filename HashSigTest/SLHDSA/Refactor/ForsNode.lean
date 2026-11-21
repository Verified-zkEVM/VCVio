/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsProgram

/-!
# FORS subtree program and raw-oracle observations

A direct reference recursion identifies the complete effectful subtree program. The runtime
fixture calls the paper's actual node through its raw hash oracle and checks a small nonzero
subtree, warm-cache requests, aborts, and the paper address encoding's modular coordinates.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.ForsNodeTest

private def referenceNode {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretSeed publicSeed : Digest) (address : Address) : Nat → Nat → m Digest
  | 0, index => do
      let value ← Fors.secret secretSeed publicSeed address index
      Hashing.tweakable publicSeed (Fors.nodeAddress address 0 index) (bytesBE n value)
  | height + 1, index => do
      let left ← referenceNode secretSeed publicSeed address height (2 * index)
      let right ← referenceNode secretSeed publicSeed address height (2 * index + 1)
      Hashing.tweakable publicSeed (Fors.nodeAddress address (height + 1) index)
        (bytesBE n left ++ bytesBE n right)

private theorem referenceNode_eq_node {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretSeed publicSeed : Digest) (address : Address) (height index : Nat) :
    referenceNode secretSeed publicSeed address height index =
      (Fors.node secretSeed publicSeed address height index : m Digest) := by
  unfold Fors.node
  induction height generalizing index with
  | zero => rfl
  | succ height ih => simp only [referenceNode, PerfectMerkleTree.merkleRootM, ih]

private structure Observation where
  calls : List Bytes := []
  cache : List (Bytes × HashOutput) := []
  draws : Nat := 0
  deriving DecidableEq

private def code (input : Bytes) (position : Nat) : Nat :=
  input.foldl (fun acc byte => 131 * acc + byte.toNat) (position + 1)

private def freshAnswer (input : Bytes) (position : Nat) : HashOutput :=
  (BitVec.ofNat (8 * messageDigestBytes) (code input position)) <<<
    (8 * (messageDigestBytes - n))

private def expectedDigest (input : Bytes) (position : Nat) : Digest :=
  BitVec.ofNat (8 * n) (code input position)

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
        let answer := freshAnswer input state.calls.length
        let next : Observation :=
          { calls, cache := state.cache ++ [(input, answer)], draws := state.draws + 1 }
        set next
        return some answer

private def secretSeed : Digest := 0x42
private def publicSeed : Digest := 0x23

private def base : Address :=
  { layer := 2, tree := 7, kind := .wotsPk, keyPair := 3,
    chainOrHeight := 9, hashOrIndex := 11 }

private abbrev NodeProgram := Nat → Nat → OracleComp HashSpec Digest

private def actual : NodeProgram := Fors.node secretSeed publicSeed base

private def reference : NodeProgram := referenceNode secretSeed publicSeed base

private def run (program : NodeProgram) (height index : Nat)
    (initial : Observation := {}) (failAt : Option Nat := none) :
    Option Digest × Observation :=
  ((simulateQ (handler failAt) (program height index)).run).run initial

-- Integer division gives an independent fixed-width byte layout, including modulo overflow.
private def natBytes (width value : Nat) : Bytes :=
  (List.range width).reverse.map fun i => UInt8.ofNat (value / 256 ^ i)

private def raw (kind height index : Nat) (payload : Bytes) : Bytes :=
  natBytes 16 0x23 ++ natBytes 4 2 ++ natBytes 12 7 ++ natBytes 4 kind ++
    natBytes 4 3 ++ natBytes 4 height ++ natBytes 4 index ++ payload

private def digestBytes (value : Digest) : Bytes := natBytes 16 value.toNat

-- The four leaves are12,13,14,15; the parents are(1,6),(1,7),(2,3).
private def expectedTree : List Bytes × Digest := Id.run do
  let s12 := raw 6 0 12 (natBytes 16 0x42)
  let l12 := raw 1 0 12 (digestBytes (expectedDigest s12 0))
  let s13 := raw 6 0 13 (natBytes 16 0x42)
  let l13 := raw 1 0 13 (digestBytes (expectedDigest s13 2))
  let p6 := raw 1 1 6 (digestBytes (expectedDigest l12 1) ++
    digestBytes (expectedDigest l13 3))
  let s14 := raw 6 0 14 (natBytes 16 0x42)
  let l14 := raw 1 0 14 (digestBytes (expectedDigest s14 5))
  let s15 := raw 6 0 15 (natBytes 16 0x42)
  let l15 := raw 1 0 15 (digestBytes (expectedDigest s15 7))
  let p7 := raw 1 1 7 (digestBytes (expectedDigest l14 6) ++
    digestBytes (expectedDigest l15 8))
  let root := raw 1 2 3 (digestBytes (expectedDigest p6 4) ++
    digestBytes (expectedDigest p7 9))
  return ([s12, l12, s13, l13, p6, s14, l14, s15, l15, p7, root],
    expectedDigest root 10)

private def ensure (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"FORS paper-node check failed: {label}")

private def checkProgram (program : NodeProgram) : IO Unit := do
  let (value, cold) := run program 2 3
  let (inputs, expectedRoot) := expectedTree
  ensure "literal nonzero subtree raw inputs, ordered payloads and original address kind"
    (cold.calls == inputs)
  ensure "complete returned root" (value == some expectedRoot)
  ensure "joint result, raw trace, cache and draws match the direct recursion"
    ((value, cold) == run reference 2 3)
  ensure "cold calls and fresh draws" (cold.calls.length == 11 && cold.draws == 11)
  let (warmValue, warm) := run program 2 3 { cache := cold.cache.take 2 }
  ensure "warm hits remain logged and charged"
    (warmValue == value && warm.calls == inputs && warm.draws == 9 && warm.cache == cold.cache)
  let (repeatValue, repeated) := run program 2 3 { cache := cold.cache }
  ensure "every repeated call is retained while all fresh draws disappear"
    (repeatValue == value && repeated.calls == inputs && repeated.draws == 0 &&
      repeated.cache == cold.cache)
  let (aborted, abortState) := run program 2 3 {} (some 1)
  ensure "failure retains the attempted leaf call and prevents later subtree/parent effects"
    (aborted == none && abortState.calls == inputs.take 2 && abortState.draws == 1 &&
      abortState.cache.length == 1 &&
      (aborted, abortState) == run reference 2 3 {} (some 1))
  let (overflowValue, overflow) := run program 2 (2 ^ 32 + 3)
  ensure "paper global indices retain their modular raw encoding"
    (overflowValue == value && overflow.calls == inputs)
  let (leafValue, leaf) := run program 0 (2 ^ 32 + 5)
  let secretInput := raw 6 0 5 (natBytes 16 0x42)
  let leafInput := raw 1 0 5 (digestBytes (expectedDigest secretInput 0))
  ensure "height-zero secret then leaf at an overflowing global index"
    (leaf.calls == [secretInput, leafInput] &&
      leafValue == some (expectedDigest leafInput 1) && leaf.draws == 2)
  ensure "node-address height and index overflow preserve the incoming kind and other fields"
    (natBytes 16 0x23 ++
        (Fors.nodeAddress base (2 ^ 32 + 2) (2 ^ 32 + 3)).toBytes ==
      raw 1 (2 ^ 32 + 2) (2 ^ 32 + 3) [])

private def reversedNode : NodeProgram
  | 0, index => reference 0 index
  | height + 1, index => do
      let right ← reversedNode height (2 * index + 1)
      let left ← reversedNode height (2 * index)
      Hashing.tweakable publicSeed (Fors.nodeAddress base (height + 1) index)
        (bytesBE n left ++ bytesBE n right)

private def withoutSecrets : NodeProgram :=
  PerfectMerkleTree.merkleRootM
    (fun index => Hashing.tweakable publicSeed (Fors.nodeAddress base 0 index)
      (bytesBE n secretSeed))
    (fun height index left right =>
      Hashing.tweakable publicSeed (Fors.nodeAddress base height index)
        (bytesBE n left ++ bytesBE n right))

private def recoverySignature : ForsSignature := fun i =>
  { secret := BitVec.ofNat (8 * n) (50 + i.val)
    authentication := fun j => BitVec.ofNat (8 * n) (1000 + 20 * i.val + j.val) }

private def recoveryIndices : Fors.Indices := fun i =>
  ⟨(i.val + 5) % 2 ^ forsHeight, Nat.mod_lt _ (by positivity)⟩

private def referenceRecovery : OracleComp HashSpec Digest := do
  let roots ← sequenceFin forsTrees fun i => do
    let index := i.val * 2 ^ forsHeight + (recoveryIndices i).val
    let leaf ← Hashing.tweakable publicSeed (Fors.nodeAddress base 0 index)
      (bytesBE n (recoverySignature i).secret)
    (List.finRange forsHeight).foldlM (fun value j => do
      let payload := if (recoveryIndices i).val / 2 ^ j.val % 2 = 0 then
        bytesBE n value ++ bytesBE n ((recoverySignature i).authentication j)
        else bytesBE n ((recoverySignature i).authentication j) ++ bytesBE n value
      Hashing.tweakable publicSeed (Fors.nodeAddress base (j.val + 1)
        (index / 2 ^ (j.val + 1))) payload) leaf
  Hashing.tweakable publicSeed
    { base.setTypeAndClear .forsRoots with keyPair := base.keyPair } (digestArrayBytes roots)

private def actualRecovery : OracleComp HashSpec Digest :=
  Fors.publicKeyFromSignature recoverySignature recoveryIndices publicSeed base

private theorem referenceRecovery_eq_actual : referenceRecovery = actualRecovery :=
  (Fors.publicKeyFromSignature_eq_fold recoverySignature recoveryIndices publicSeed base).symm

private def runRecovery (program : OracleComp HashSpec Digest)
    (initial : Observation := {}) (failAt : Option Nat := none) : Option Digest × Observation :=
  ((simulateQ (handler failAt) program).run).run initial

private def checkRecovery : IO Unit := do
  let (value, cold) := runRecovery actualRecovery
  ensure "actual paper recovery retains the complete reference observation"
    ((value, cold) == runRecovery referenceRecovery)
  ensure "each of14 recovered roots has one leaf and12 ancestor hashes, then compression"
    (cold.calls.length == 183 && cold.draws == 183 && value.isSome)
  let leafInput := raw 1 0 5 (natBytes 16 50)
  let parentInput := raw 1 1 2 (natBytes 16 1000 ++ digestBytes (expectedDigest leafInput 0))
  ensure "recovery's odd leaf places the first authentication node before the current value"
    (cold.calls.take 2 == [leafInput, parentInput])
  let roots := (List.range 14).map fun i =>
    digestBytes (expectedDigest (cold.calls[i * 13 + 12]!) (i * 13 + 12))
  ensure "root compression consumes recovered roots in increasing tree order"
    (cold.calls.getLast? == some (raw 4 0 0 roots.flatten))
  let (repeatedValue, repeated) := runRecovery actualRecovery { cache := cold.cache }
  ensure "recovery logs all183 repeated calls while preserving its full cache and result"
    (repeatedValue == value && repeated.calls == cold.calls && repeated.draws == 0 &&
      repeated.cache == cold.cache)
  let aborted := runRecovery actualRecovery {} (some 1)
  ensure "recovery failure retains only the attempted prefix"
    (aborted.1 == none && aborted.2.calls == [leafInput, parentInput] &&
      aborted == runRecovery referenceRecovery {} (some 1))

private def observe {α : Type} (program : OracleComp HashSpec α)
    (initial : Observation := {}) (failAt : Option Nat := none) : Option α × Observation :=
  ((simulateQ (handler failAt) program).run).run initial

private def actualPath (height index : Nat) : OracleComp HashSpec (List Digest) :=
  Vector.toList <$> Fors.authenticationPath secretSeed publicSeed base height index

private def referencePath (height index : Nat) : OracleComp HashSpec (List Digest) :=
  List.ofFn <$> sequenceFin height (fun j => Fors.node secretSeed publicSeed base j.val
    (PerfectMerkleTree.sibling (index / 2 ^ j.val)))

private theorem referencePath_eq_actual (height index : Nat) :
    referencePath height index = actualPath height index := by
  rw [referencePath, ← Fors.authenticationPath_eq_sequenceFin]
  simp only [actualPath, Functor.map_map]
  congr 1
  funext values
  apply List.ext_getElem <;> simp

private def expectedPath (parentIndex : Nat) : List Bytes × List Digest := Id.run do
  let s12 := raw 6 0 12 (natBytes 16 0x42)
  let l12 := raw 1 0 12 (digestBytes (expectedDigest s12 0))
  let s14 := raw 6 0 14 (natBytes 16 0x42)
  let l14 := raw 1 0 14 (digestBytes (expectedDigest s14 2))
  let s15 := raw 6 0 15 (natBytes 16 0x42)
  let l15 := raw 1 0 15 (digestBytes (expectedDigest s15 4))
  let parent := raw 1 1 parentIndex (digestBytes (expectedDigest l14 3) ++
    digestBytes (expectedDigest l15 5))
  return ([s12, l12, s14, l14, s15, l15, parent],
    [expectedDigest l12 1, expectedDigest parent 6])

private def checkAuthenticationWith (indexPolicy : Nat → Nat) : IO Unit := do
  let cold := observe (actualPath 2 (indexPolicy 13))
  let (inputs, values) := expectedPath 7
  ensure "actual intrinsic authentication retains ordered sibling queries and leaf-first values"
    (cold.1 == some values && cold.2.calls == inputs && cold.2.draws == 7)
  ensure "authentication retains the complete direct-reference observation"
    (cold == observe (referencePath 2 13))
  let repeated := observe (actualPath 2 (indexPolicy 13)) { cache := cold.2.cache }
  ensure "cached authentication retains every request and both typed path entries"
    (repeated.1 == cold.1 && repeated.2.calls == inputs && repeated.2.draws == 0 &&
      repeated.2.cache == cold.2.cache)
  let aborted := observe (actualPath 2 (indexPolicy 13)) {} (some 2)
  ensure "failure at the next sibling level preserves the completed lower-level effects"
    (aborted.1 == none && aborted.2.calls == inputs.take 3 && aborted.2.draws == 2 &&
      aborted == observe (referencePath 2 13) {} (some 2))
  let overflow := observe (actualPath 2 (indexPolicy (2 ^ 32 + 13)))
  let (overflowInputs, overflowValues) := expectedPath (2 ^ 31 + 7)
  ensure "full-Nat ancestor division precedes each modular address encoding"
    (overflow.1 == some overflowValues && overflow.2.calls == overflowInputs &&
      overflowInputs != inputs)
  let empty := observe (actualPath 0 (indexPolicy (2 ^ 32 + 13)))
  ensure "zero-height authentication has no provider or hash effect"
    (empty.1 == some [] && empty.2.calls.isEmpty && empty.2.draws == 0)

private def referenceSign : OracleComp HashSpec ForsSignature :=
  sequenceFin forsTrees fun i => do
    let selected ← Fors.secret secretSeed publicSeed base
      (i.val * 2 ^ forsHeight + (recoveryIndices i).val)
    let authentication ← sequenceFin forsHeight fun j =>
      Fors.node secretSeed publicSeed base j.val
        (i.val * 2 ^ (forsHeight - j.val) + Nat.xor ((recoveryIndices i).val / 2 ^ j.val) 1)
    return { secret := selected, authentication }

private def actualSign : OracleComp HashSpec ForsSignature :=
  Fors.sign recoveryIndices secretSeed publicSeed base

private theorem referenceSign_eq_actual : referenceSign = actualSign :=
  (Fors.sign_eq_sequenceFin recoveryIndices secretSeed publicSeed base).symm

private def checkSignerAbortWith (program : OracleComp HashSpec ForsSignature) : IO Unit := do
  let aborted := observe program {} (some 1)
  let reference := observe referenceSign {} (some 1)
  let selected := raw 6 0 5 (natBytes 16 0x42)
  let firstSibling := raw 6 0 4 (natBytes 16 0x42)
  ensure "actual fixed-parameter signer requests its selected secret before the first sibling"
    (aborted.1.isNone && aborted.2.calls == [selected, firstSibling] &&
      aborted.2.draws == 1 && reference.1.isNone && aborted.2 == reference.2)

private def pathFirstSign : OracleComp HashSpec ForsSignature :=
  sequenceFin forsTrees fun i => do
    let index := i.val * 2 ^ forsHeight + (recoveryIndices i).val
    let authentication ← Fors.authenticationPath secretSeed publicSeed base forsHeight index
    let selected ← Fors.secret secretSeed publicSeed base index
    return { secret := selected, authentication := fun j => authentication[j] }

/-- Run actual paper FORS traversal, recovery, authentication and signing-prefix checks. -/
def runTests : IO Unit := do
  checkProgram actual
  checkRecovery
  checkAuthenticationWith id
  checkSignerAbortWith actualSign
  IO.println "SLH-DSA paper FORS authentication: PASS"
  IO.println "SLH-DSA paper FORS recovery: PASS"
  IO.println "SLH-DSA paper FORS node: PASS"

/-- Run a deliberately changed computation against the unchanged positive assertions.
Each supported control must fail its corresponding unchanged observation assertion. -/
def runControl (name : String) : IO Unit :=
  if name == "reverse" then checkProgram reversedNode
  else if name == "drop-secret" then checkProgram withoutSecrets
  else if name == "normalize-index" then
    checkAuthenticationWith (fun index => index % 2 ^ 32)
  else if name == "auth-first" then checkSignerAbortWith pathFirstSign
  else throw (IO.userError s!"unknown FORS node control: {name}")

end SLHDSA.SHAKE128s.ForsNodeTest
