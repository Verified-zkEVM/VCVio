/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.Profile

/-!
# Wire-game regression checks

Exact parsing rejects truncated and appended signatures. Strong freshness rejects an exact
replay while admitting a distinct signature on the same signed message. The profile theorem
binds this boundary to the structured reduction and the exact bound evaluator.
-/

public section

open OracleSpec SignatureAlg SLHDSA SLHDSA.Security

namespace SLHDSA.WireTest

def signatureCodec : WireCodec (Bytes 1) 1 := WireCodec.bytes 1

def context : PureContext := ⟨[0x41, 0x42], by decide⟩

def profile : ShakeProfile :=
  ⟨.SLHDSA_SHAKE_128f, rfl, .deterministic, context⟩

/-- The external pure prefix cannot identify distinct messages. -/
example (a b : List Byte) (h : context.encode a = context.encode b) : a = b :=
  context.encode_injective h

/-- The final named theorem applies directly to the bound profile's byte-game adversary. -/
example (adv : StrongUnforgeableAdversary profile.algorithm) {qh qs : Nat}
    (h : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (shakeRuntime profile.parameterSet.validatedParams) adv ≤
      KeyedHash.Covering.rationalValue (profile.boundEvaluator qh qs) :=
  profile.strongUnforgeableAdvantage_le_boundEvaluator adv h

def ensure (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

/-- Executable interpretation of the SUF experiment when message and signature equality are
decidable. The equality below connects this runner to the experiment used by the reduction. -/
def executableExperiment {ι : Type} {spec : OracleSpec ι} {M PK SK S : Type}
    [DecidableEq M] [DecidableEq S] {alg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : StrongUnforgeableAdversary alg) : OracleComp spec Bool := do
  let (pk, sk) ← alg.keygen
  let ((msg, sig), log) ← alg.runWithSigningOracle pk sk (adv.main pk)
  let verified ← alg.verify pk msg sig
  return !signingLogContains log msg sig && verified

theorem executableExperiment_eq {ι : Type} {spec : OracleSpec ι} {M PK SK S : Type}
    [DecidableEq M] [DecidableEq S] {alg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : StrongUnforgeableAdversary alg) :
    executableExperiment adv = strongUnforgeableExperiment adv := by
  simp only [executableExperiment, strongUnforgeableExperiment, signingLogContains]
  congr 1
  funext keys
  congr 1
  funext outcome
  congr 1
  funext verified
  congr 3
  exact decide_eq_decide.mpr Iff.rfl

abbrev toySpec : OracleSpec Nat := Nat →ₒ Nat

def toyMessage : List Byte := [0x43]

def toyKey : Bytes 1 := Vector.replicate 1 10

def toySignature (b : Byte) : Bytes 1 := Vector.replicate 1 b

/-- Deliberately forgeable scheme: zero and one are both valid signatures. Distinct oracle
indices mark key generation, signing, verification, and adversary traffic respectively. -/
def toyScheme : SignatureAlg (OracleComp toySpec) (List Byte) (Bytes 1) Unit (Bytes 1) where
  keygen := do
    let answer ← query (spec := toySpec) 0
    return (if answer == 10 then toyKey else toySignature 255, ())
  sign key _ msg := do
    let answer ← query (spec := toySpec)
      (if key == toyKey && msg == context.encode toyMessage then 1 else 101)
    return toySignature (if answer == 11 then 0 else 255)
  verify key msg sig := do
    let answer ← query (spec := toySpec) 2
    return answer == 12 && key == toyKey && msg == context.encode toyMessage &&
      (sig == toySignature 0 || sig == toySignature 1)

def toyWireScheme := SignatureAlg.Wire.scheme toyScheme context.encode
  signatureCodec.canonicalEncoding signatureCodec.canonicalEncoding

/-- Every candidate first asks twice at the same ambient point and signs the same message.
The output also depends on the forwarded public key and both ambient answers. -/
def toyAdversary (candidate : List Byte → List Byte) :
    StrongUnforgeableAdversary toyWireScheme where
  main key := do
    let first : Nat ← query (spec := toySpec + (List Byte →ₒ List Byte)) (.inl 3)
    let second : Nat ← query (spec := toySpec + (List Byte →ₒ List Byte)) (.inl 3)
    let sig ← query (spec := toySpec + (List Byte →ₒ List Byte)) (.inr toyMessage)
    return (toyMessage, if key == [10] && first == 13 && second == 13 then candidate sig else [])

/-- Log all ambient calls, including repeated requests, while returning recognizable answers. -/
def toyHandler : QueryImpl toySpec (StateM (List Nat)) := fun index => do
  modify (index :: ·)
  return index + 10

def runToy {α : Type} (program : OracleComp toySpec α) : α × List Nat :=
  (simulateQ toyHandler program).run []

def checkExperiments : IO Unit := do
  let codec := signatureCodec.canonicalEncoding
  let validCalls := [2, 1, 3, 3, 0]
  let rejectedCalls := [1, 3, 3, 0]
  let cases : List (String × (List Byte → List Byte) × Bool × List Nat) := [
    ("exact replay", id, false, validCalls),
    ("different valid signature on signed message", fun _ => codec.encode (toySignature 1),
      true, validCalls),
    ("invalid full-length signature", fun _ => codec.encode (toySignature 2), false, validCalls),
    ("truncated signature", fun _ => [], false, rejectedCalls),
    ("appended signature", fun sig => sig ++ [0], false, rejectedCalls)]
  for (label, candidate, win, calls) in cases do
    let adv := toyAdversary candidate
    let (result, trace) := runToy (executableExperiment adv)
    ensure s!"wrapped experiment: {label}" (result == win)
    ensure s!"wrapped experiment forwards every call: {label}" (trace == calls)
    let reduced := SignatureAlg.Wire.reduce toyScheme context.encode codec codec adv
    let (reducedResult, reducedTrace) := runToy (executableExperiment reduced)
    ensure s!"reduced experiment: {label}" (reducedResult == win)
    ensure s!"reduction forwards both ambient calls and the signing call: {label}"
      (reducedTrace == validCalls)
  for key in [[], [10, 0]] do
    let (result, trace) := runToy (toyWireScheme.verify key toyMessage [0])
    ensure "malformed public key rejects before underlying verification" (!result && trace.isEmpty)
  IO.println "Wrapped SUF experiments and forwarded query traces: PASS"

def main : IO Unit := do
  checkExperiments
  for set in [FipsParameterSet.SLHDSA_SHAKE_128s, .SLHDSA_SHAKE_128f,
      .SLHDSA_SHAKE_192s, .SLHDSA_SHAKE_192f, .SLHDSA_SHAKE_256s, .SLHDSA_SHAKE_256f] do
    let vp := set.validatedParams
    let publicCodec := publicKeyCodec (Concrete.shakeWireCodec vp.params)
    let wireCodec := SLHDSA.signatureCodec vp (Concrete.shakeWireCodec vp.params)
    let publicBytes := List.replicate vp.params.publicKeyBytes (0 : Byte)
    let signatureBytes := List.replicate vp.params.signatureBytes (0 : Byte)
    ensure "production public-key width accepted" ((publicCodec.decode publicBytes).toOption.isSome)
    ensure "production signature width accepted" ((wireCodec.decode signatureBytes).toOption.isSome)
    ensure "production short public key rejected" ((publicCodec.decode []).toOption.isNone)
    ensure "production short signature rejected" ((wireCodec.decode []).toOption.isNone)
    ensure "production appended public key rejected"
      ((publicCodec.decode (publicBytes ++ [0])).toOption.isNone)
    ensure "production appended signature rejected"
      ((wireCodec.decode (signatureBytes ++ [0])).toOption.isNone)
  let codec := signatureCodec.canonicalEncoding
  let s₀ : Bytes 1 := Vector.replicate 1 0
  let s₁ : Bytes 1 := Vector.replicate 1 1
  let m : List Byte := [0x43]
  let log : QueryLog (List Byte →ₒ List Byte) := [⟨m, codec.encode s₀⟩]
  ensure "short signature rejected" ((codec.decode []).isNone)
  ensure "appended signature rejected" ((codec.decode (codec.encode s₀ ++ [0])).isNone)
  ensure "canonical full signature accepted" (codec.decode (codec.encode s₀) == some s₀)
  let decoded := SignatureAlg.Wire.decodeLog context.encode codec log
  ensure "exact wire replay is stale" (signingLogContains log m (codec.encode s₀))
  ensure "decoded exact replay is stale" (signingLogContains decoded (context.encode m) s₀)
  ensure "second wire signature on same message is fresh"
    (!signingLogContains log m (codec.encode s₁))
  ensure "second decoded signature on same message is fresh"
    (!signingLogContains decoded (context.encode m) s₁)
  IO.println "SLH-DSA wire-game tests: PASS"

end SLHDSA.WireTest

def main : IO Unit := SLHDSA.WireTest.main
