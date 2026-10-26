/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.ProviderObservation
public import HashSig.SLHDSA.Security.ByteModel
public import HashSig.SLHDSA.SHAKE128s.Bridge.ForsObservation
public import VCVio.OracleComp.QueryTracking.ListCache
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Effectful FORS interpretation clients and executable observations

The actual SHAKE-128s and SHAKE-192f component clients retain full signatures, ordered costs and
final states. A small validated forest runs the actual oracle-backed provider and public hashes,
checking literal query order, addresses, payloads, cached answers and nonzero state prefixes.
-/

public section

open OracleSpec OracleComp SLHDSA SLHDSA.Security

namespace SLHDSA.Refactor.ForsObservationTest

local notation "vp128" => FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams
local notation "core128" => shakeCore vp128
local notation "vp192" => FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams
local notation "core192" => shakeCore vp192

/-- The actual SHAKE-128s provider and hash callbacks share the chosen stateful interpreter. -/
theorem shake128s_observer_client
    (pk : (core128).PkSeed) (sk : (core128).SkSeed) (md : List Byte) (address : Adrs)
    {m : Type → Type*} [Monad m] [LawfulMonad m] {Cache C : Type} [AddMonoid C]
    (handler : QueryImpl (publicHashSpec core128) (StateT Cache m))
    (cost : (publicHashSpec core128).Domain → C) (initial : Cache) :
    ((simulateQ (handler.withAddCost cost)
      (forsSignWithSecretM core128 (oracleSecret core128 (Equiv.refl _) pk sk) md pk address :
        OracleComp (publicHashSpec core128)
          (ForsSigCore (vp128).params core128))).runAdd).run initial =
    ((forsSignWithSecret core128
      (fun a y => simulateQ (handler.withAddCost cost) (PublicHash.f core128 pk a y))
      (fun a left right => simulateQ (handler.withAddCost cost)
        (PublicHash.h core128 pk a left right))
      (fun a => simulateQ (handler.withAddCost cost)
        (oracleSecret core128 (Equiv.refl _) pk sk a)) md address).runAdd).run initial :=
  simulateQ_forsSignWithSecretM_oracleSecret_withAddCost_run core128 (Equiv.refl _)
    pk sk md address handler cost initial

/-- The actual SHAKE-192f provider and hash callbacks share the chosen stateful interpreter. -/
theorem shake192f_observer_client
    (pk : (core192).PkSeed) (sk : (core192).SkSeed) (md : List Byte) (address : Adrs)
    {m : Type → Type*} [Monad m] [LawfulMonad m] {Cache C : Type} [AddMonoid C]
    (handler : QueryImpl (publicHashSpec core192) (StateT Cache m))
    (cost : (publicHashSpec core192).Domain → C) (initial : Cache) :
    ((simulateQ (handler.withAddCost cost)
      (forsSignWithSecretM core192 (oracleSecret core192 (Equiv.refl _) pk sk) md pk address :
        OracleComp (publicHashSpec core192)
          (ForsSigCore (vp192).params core192))).runAdd).run initial =
    ((forsSignWithSecret core192
      (fun a y => simulateQ (handler.withAddCost cost) (PublicHash.f core192 pk a y))
      (fun a left right => simulateQ (handler.withAddCost cost)
        (PublicHash.h core192 pk a left right))
      (fun a => simulateQ (handler.withAddCost cost)
        (oracleSecret core192 (Equiv.refl _) pk sk a)) md address).runAdd).run initial :=
  simulateQ_forsSignWithSecretM_oracleSecret_withAddCost_run core192 (Equiv.refl _)
    pk sk md address handler cost initial

example : ((vp128).params.n, (vp128).params.a, (vp128).params.k) = (16, 12, 14) := rfl
example : ((vp192).params.n, (vp192).params.a, (vp192).params.k) = (24, 8, 33) := rfl


open OracleSpec OracleComp SLHDSA SLHDSA.Security

/-- Small validated FORS parameters with two height-two trees. -/
@[expose] def params : Params :=
  { n := 1, h := 1, d := 1, hp := 1, a := 2, k := 2, lgw := 1 }

/-- Arithmetic validity certificate for the executable forest. -/
@[expose, reducible] def vp : ValidatedParams := ⟨params, by decide⟩

/-- Natural-number hash values retain readable provider and authentication observations. -/
@[expose, reducible] def core : CorePrimitives vp.params where
  PkSeed := Unit
  SkSeed := Nat
  SkPrf := Unit
  Y := Nat
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun _ _ address => 100 + address.word3
  PRFmsg := fun _ _ _ => 0
  yToBytes := fun x => #v[UInt8.ofNat x]

private abbrev Spec := publicHashSpec core
private abbrev Key := Adrs × List Nat
private abbrev Cache := List (Key × Nat)

private inductive Event where
  | thash (address : Adrs) (payload : List Nat)
  | unexpectedHmsg
  deriving DecidableEq, Repr

private abbrev Cost := Nat × FreeAddMonoid Event

private def answer (key : Key) : Nat :=
  let (address, payload) := key
  if address.type = 6 then 100 + address.word3 else
    match payload with
    | [x] => 1000 + 10 * address.word3 + x
    | [left, right] => 10000 + 100 * address.word2 + address.word3 + left + 2 * right
    | _ => 0

private def draw : QueryImpl (Key →ₒ Nat) (StateM Nat) := fun key => do
  modify (· + 1)
  return answer key

private def handler : QueryImpl Spec (StateT Cache (StateM Nat))
  | .thash _ address payload => QueryImpl.ListCache.handler draw (address, payload)
  | .hmsg _ _ _ _ => pure (Vector.ofFn (fun _ => (0 : Byte)))

private def cost : Spec.Domain → Cost
  | .thash _ address payload =>
    (if address.type = 6 then 5 else if payload.length = 2 then 11 else 7,
      .of (.thash address payload))
  | .hmsg _ _ _ _ => (100, .of .unexpectedHmsg)

private def base : Adrs := ⟨2, 7, 3, 3, 0, 0⟩
private def secretAddress (i : Nat) : Adrs := ⟨2, 7, 6, 3, 0, i⟩
private def leafAddress (i : Nat) : Adrs := ⟨2, 7, 3, 3, 0, i⟩
private def parentAddress (i : Nat) : Adrs := ⟨2, 7, 3, 3, 1, i⟩

private def secret (address : Adrs) : OracleComp Spec Nat :=
  oracleSecret core (Equiv.refl Nat) () 9 address

private def canonical : OracleComp Spec (ForsSigCore vp.params core) :=
  forsSignWithSecretM core secret [0x60] () base

private def expected : List Event := [
  .thash (secretAddress 1) [9],
  .thash (secretAddress 0) [9], .thash (leafAddress 0) [100],
  .thash (secretAddress 2) [9], .thash (leafAddress 2) [102],
  .thash (secretAddress 3) [9], .thash (leafAddress 3) [103],
  .thash (parentAddress 1) [1122, 1133],
  .thash (secretAddress 6) [9],
  .thash (secretAddress 7) [9], .thash (leafAddress 7) [107],
  .thash (secretAddress 4) [9], .thash (leafAddress 4) [104],
  .thash (secretAddress 5) [9], .thash (leafAddress 5) [105],
  .thash (parentAddress 2) [1144, 1155]]

private def runProgram {α : Type} (program : OracleComp Spec α)
    (initial : Cache) (initialDraws : Nat) : (((α × Cost) × Cache) × Nat) :=
  (((simulateQ (handler.withAddCost cost) program).runAdd).run initial).run initialDraws

private def ensure (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- Validate actual effectful provider queries, chronology, cost and retained cache answers. -/
def run : IO Unit := do
  let (((signature, paid), cache), draws) := runProgram canonical [] 7
  let fields := signature.toList.map fun tree => (tree.sk, tree.auth.toList)
  ensure "literal selected secrets/authentication fields"
    (fields == [(101, [1100, 13489]), (106, [1177, 13556])])
  ensure "provider-inclusive weighted cost104" (paid.1 == 104)
  ensure "provider-inclusive query count16" (paid.2.toList.length == 16)
  ensure "selected-secret-first actual PRF/hash chronology" (decide (paid.2.toList = expected))
  ensure "full component shares one cache" (cache.length == 16 && draws == 23)
  let initial : Cache := [((secretAddress 1, [9]), 777)]
  let (((warm, paid), cache), draws) := runProgram canonical initial 41
  ensure "distinct cached provider response affects selected secret" (warm[0].sk == 777)
  ensure "warm component still charges all calls" (paid.1 == 104 && paid.2.toList.length == 16)
  ensure "warm PRF query hit retains its original value"
    (cache.lookup (secretAddress 1, [9]) == some 777 && draws == 56 && cache.length == 16)
  let repeated : OracleComp Spec (ForsSigCore vp.params core × Nat) := do
    let signature ← canonical
    let again ← secret (secretAddress 1)
    return (signature, again)
  let ((((signature, again), paid), cache), draws) := runProgram repeated initial 41
  ensure "repeated query reuses the actual provider answer"
    (signature[0].sk == 777 && again == 777 && draws == 56 && cache.length == 16)
  ensure "cache hit charges another provider event before delegation"
    (paid.1 == 109 && decide (paid.2.toList = expected ++ [.thash (secretAddress 1) [9]]))
  IO.println "FORS effectful provider, ordered-cost and shared-cache pilot: PASS"

end SLHDSA.Refactor.ForsObservationTest

/-- Run the effectful FORS provider observation checks. -/
def main : IO Unit := SLHDSA.Refactor.ForsObservationTest.run
