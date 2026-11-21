/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wots

/-!
# WOTS construction observations

The generic bridge equations below retain output and every stateful observation jointly.
The executable checks run the native WOTS entrypoints at both SHAKE-128s and SHAKE-192f
parameter dimensions. Their deterministic cache records every provider call and every ordered
hash input, including repeated hits. The handler is a test interpretation, not a hash assumption.
-/

public section

open OracleComp OracleSpec
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s

namespace SLHDSA.Refactor.WotsIntegration

/-- A state handler observes both representations of public-key generation jointly. -/
theorem observePublicKey {σ : Type}
    (handler : QueryImpl (Game.World FIPS205.Answer) (StateM σ))
    (secretSeed publicSeed : Digest) (address : Address)
    (hk : address.kind = .wotsHash) (hh : address.hashOrIndex = 0) :
    simulateQ handler (simulateQ (Bridge.relabel Bridge.answerEquiv)
      (SHAKE128s.Wots.publicKey secretSeed publicSeed address : OracleComp OracleWorld Digest)) =
    simulateQ handler (Bridge.digestEquiv.symm <$>
      simulateQ (encImpl FIPS205.params)
        (wotsPkGenWithSecret FIPS205.core
          (PublicHash.f FIPS205.core (Bridge.digestEquiv publicSeed))
          (PublicHash.tl FIPS205.core (Bridge.digestEquiv publicSeed))
          (oracleSecret FIPS205.core (Equiv.refl _) (Bridge.digestEquiv publicSeed)
            (Bridge.digestEquiv secretSeed)) (Bridge.toAdrs address) :
          OracleComp (unifSpec + hashSpec FIPS205.core) FIPS205.core.Y)) := by
  exact congrArg (simulateQ handler)
    (Bridge.simulateQ_relabel_wotsPublicKey secretSeed publicSeed address hk hh)

/-- A state handler observes both representations of signing jointly. -/
theorem observeSign {σ : Type}
    (handler : QueryImpl (Game.World FIPS205.Answer) (StateM σ))
    (message : FIPS205.core.Y) (secretSeed publicSeed : Digest) (address : Address)
    (hk : address.kind = .wotsHash) (hh : address.hashOrIndex = 0) :
    simulateQ handler (simulateQ (Bridge.relabel Bridge.answerEquiv)
      (SHAKE128s.Wots.sign (Bridge.digestEquiv.symm message) secretSeed publicSeed address :
        OracleComp OracleWorld WotsSignature)) =
    simulateQ handler (Bridge.wotsOfCore <$>
      simulateQ (encImpl FIPS205.params)
        (wotsSignWithSecret FIPS205.core
          (PublicHash.f FIPS205.core (Bridge.digestEquiv publicSeed))
          (oracleSecret FIPS205.core (Equiv.refl _) (Bridge.digestEquiv publicSeed)
            (Bridge.digestEquiv secretSeed)) message (Bridge.toAdrs address) :
          OracleComp (unifSpec + hashSpec FIPS205.core)
            (WotsSig FIPS205.params.params FIPS205.core))) := by
  exact congrArg (simulateQ handler)
    (Bridge.simulateQ_relabel_wotsSign message secretSeed publicSeed address hk hh)

/-- A state handler observes both representations of recovery jointly. -/
theorem observeRecovery {σ : Type}
    (handler : QueryImpl (Game.World FIPS205.Answer) (StateM σ))
    (signature : WotsSig FIPS205.params.params FIPS205.core) (message : FIPS205.core.Y)
    (publicSeed : Digest) (address : Address)
    (hk : address.kind = .wotsHash) (hh : address.hashOrIndex = 0) :
    simulateQ handler (simulateQ (Bridge.relabel Bridge.answerEquiv)
      (SHAKE128s.Wots.publicKeyFromSignature (Bridge.wotsOfCore signature)
        (Bridge.digestEquiv.symm message) publicSeed address : OracleComp OracleWorld Digest)) =
    simulateQ handler (Bridge.digestEquiv.symm <$>
      simulateQ (encImpl FIPS205.params)
        (wotsPkFromSigWith FIPS205.core
          (PublicHash.f FIPS205.core (Bridge.digestEquiv publicSeed))
          (PublicHash.tl FIPS205.core (Bridge.digestEquiv publicSeed))
          signature message (Bridge.toAdrs address) :
          OracleComp (unifSpec + hashSpec FIPS205.core) FIPS205.core.Y)) := by
  exact congrArg (simulateQ handler)
    (Bridge.simulateQ_relabel_wotsPublicKeyFromSignature signature message publicSeed address hk hh)

/-- The operation and complete native payload form the cache key. -/
inductive Request where
  | secret (address : Adrs)
  | hash (address : Adrs) (input : List Byte)
  | compress (address : Adrs) (inputs : List (List Byte))
  deriving DecidableEq

/-- Operation/address projection used to check chronological call shapes independently. -/
inductive Call where
  | secret (address : Adrs)
  | hash (address : Adrs)
  | compress (address : Adrs)
  deriving DecidableEq

/-- Keep the operation tag and the full structured address. -/
def Request.call : Request → Call
  | .secret address => .secret address
  | .hash address _ => .hash address
  | .compress address _ => .compress address

/-- Every call is logged; only fresh requests insert an answer into the cache. -/
structure Observation (n : Nat) where
  /-- Requests and returned bytes in invocation order, including cache hits. -/
  chronological : List (Request × SLHDSA.Bytes n) := []
  /-- Previously answered requests and their retained byte answers. -/
  cache : List (Request × SLHDSA.Bytes n) := []
  /-- Number of callback invocations, including repeated requests. -/
  calls : Nat := 0
  deriving DecidableEq

/-- A deterministic cache whose fresh answers depend on chronological position and payload. -/
def answer (n salt : Nat) (request : Request) : StateM (Observation n) (SLHDSA.Bytes n) := do
  let state ← get
  let bytes := match request with
    | .secret address => address.toBytes
    | .hash address input => address.toBytes ++ input
    | .compress address inputs => address.toBytes ++ inputs.flatten
  let code := bytes.foldl (fun acc byte => 131 * acc + byte.toNat) (salt + state.calls + 1)
  let value := match state.cache.find? (fun entry => decide (entry.1 = request)) with
    | some entry => entry.2
    | none => Vector.ofFn fun i => UInt8.ofNat (code + 17 * i.val)
  let cache := if state.cache.any (fun entry => decide (entry.1 = request)) then state.cache
    else state.cache ++ [(request, value)]
  set (⟨state.chronological ++ [(request, value)], cache, state.calls + 1⟩ : Observation n)
  return value

/-- Reject a runtime mismatch with a nonzero executable exit. -/
def ensure (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"WOTS construction check failed: {label}")

/-- A nonzero location makes all address fields observable. -/
def base : Adrs := ⟨2, 7, 0, 3, 0, 0⟩

/-- The expected schedule uses literal FIPS address fields and ascending native chain indices. -/
def expectedCalls (p : Params) (starts lengths : Nat → Nat) (readSecrets compressed : Bool) :
    List Call :=
  (List.range p.len).flatMap (fun i =>
    (if readSecrets then [.secret ⟨2, 7, 5, 3, i, 0⟩] else []) ++
      (List.range (lengths i)).map (fun offset => .hash ⟨2, 7, 0, 3, i, starts i + offset⟩)) ++
    (if compressed then [.compress ⟨2, 7, 1, 3, 0, 0⟩] else [])

/-- Run actual provider, signature and recovery entrypoints over byte-vector carriers. -/
def checkParameters (ps : FipsParameterSet) : IO Unit := do
  let vp := ps.validatedParams
  let core := shakeCore vp
  let hash := fun address (value : core.Y) =>
    answer vp.params.n 0 (.hash address value.toList)
  let secret := fun address => answer vp.params.n 0 (.secret address)
  let compress := fun address (values : List core.Y) =>
    answer vp.params.n 0 (.compress address (values.map Vector.toList))
  let message : core.Y := Vector.replicate vp.params.n 0x11
  let (tops, topped) := (wotsPkGenTopsWithSecret core hash secret base).run {}
  let (publicKey, keyed) :=
    (wotsPkGenWithSecret core hash compress secret base).run {}
  let (signature, signed) :=
    (wotsSignWithSecret core hash secret message base).run keyed
  let (recoveryTops, recoveredTopsState) :=
    (wotsPkFromSigTopsWith core hash signature message base).run signed
  let (recovered, verified) :=
    (wotsPkFromSigWith core hash compress signature message base).run signed
  let (replayed, replayedState) :=
    (wotsPkGenWithSecret core hash compress secret base).run verified
  let calls := fun (state : Observation vp.params.n) =>
    state.chronological.map (fun entry => entry.1.call)
  let digits := chainStepsCore core message
  ensure s!"{ps.name}: public-key provider/hash/compression order"
    (calls keyed == expectedCalls vp.params (fun _ => 0) (fun _ => vp.params.w - 1) true true)
  ensure s!"{ps.name}: signing provider/hash order"
    ((calls signed).drop keyed.calls == expectedCalls vp.params (fun _ => 0) digits true false)
  ensure s!"{ps.name}: recovery suffix order and absent provider calls"
    ((calls verified).drop signed.calls ==
      expectedCalls vp.params digits (fun i => vp.params.w - 1 - digits i) false true)
  ensure s!"{ps.name}: native tops have the same ordered observations"
    (keyed.chronological.take topped.calls == topped.chronological)
  match keyed.chronological.getLast? with
  | some (.compress _ inputs, _) =>
    ensure s!"{ps.name}: compression consumes the ordered typed tops"
      (inputs == tops.toList.map Vector.toList)
  | _ => throw (IO.userError "WOTS public key omitted its final compression")
  ensure s!"{ps.name}: typed recovery tops" (recoveryTops == tops)
  ensure s!"{ps.name}: recovery tops omit only the final compression"
    (verified.chronological.take recoveredTopsState.calls == recoveredTopsState.chronological &&
      verified.calls == recoveredTopsState.calls + 1)
  ensure s!"{ps.name}: typed recovery result" (recovered == publicKey)
  ensure s!"{ps.name}: repeated typed result" (replayed == publicKey)
  ensure s!"{ps.name}: signing/recovery/repetition retain the cache"
    (keyed.cache == signed.cache && signed.cache == verified.cache &&
      verified.cache == replayedState.cache)
  ensure s!"{ps.name}: every call is logged, including cache hits"
    (replayedState.chronological.length == replayedState.calls &&
      replayedState.calls - verified.calls == keyed.calls)
  ensure s!"{ps.name}: exact public-key callback count"
    (keyed.calls == vp.params.len * vp.params.w + 1)
  ensure s!"{ps.name}: actual joint signing/recovery callback count"
    (verified.calls - keyed.calls == vp.params.len * vp.params.w + 1)
  ensure s!"{ps.name}: reversed chronology control" (calls keyed != (calls keyed).reverse)
  let alteredSecret := fun address => answer vp.params.n 1 (.secret address)
  let (_, altered) := (wotsPkGenWithSecret core hash compress alteredSecret base).run {}
  ensure s!"{ps.name}: provider-answer/payload control"
    (altered.chronological != keyed.chronological)
  let initial : core.Y := Vector.replicate vp.params.n 0xA3
  let (zero, emptyState) := (chainWith hash base initial 9 0).run {}
  ensure s!"{ps.name}: zero steps have zero cost" (zero == initial && emptyState.calls == 0)
  let (_, overflowState) := (chainWith hash base initial (2 ^ 32) 2).run {}
  let fullMessage : core.Y := Vector.replicate vp.params.n 0xFF
  let (fullSignature, fullSigned) :=
    (wotsSignWithSecret core hash secret fullMessage base).run keyed
  let (_, fullRecovered) :=
    (wotsPkFromSigWith core hash compress fullSignature fullMessage base).run fullSigned
  let fullDigits := chainStepsCore core fullMessage
  ensure s!"{ps.name}: maximal message digit control" (fullDigits 0 == vp.params.w - 1)
  ensure s!"{ps.name}: maximal digits retain zero-length recovery chains"
    ((calls fullRecovered).drop fullSigned.calls ==
      expectedCalls vp.params fullDigits (fun i => vp.params.w - 1 - fullDigits i) false true)
  ensure s!"{ps.name}: structured indices retain overflow rather than assuming representability"
    (calls overflowState == [.hash ⟨2, 7, 0, 3, 0, 2 ^ 32⟩,
      .hash ⟨2, 7, 0, 3, 0, 2 ^ 32 + 1⟩])

/-- Execute the two advertised parameter-dimension consumers. -/
def runTests : IO Unit := do
  checkParameters .SLHDSA_SHAKE_128s
  checkParameters .SLHDSA_SHAKE_192f

end SLHDSA.Refactor.WotsIntegration
