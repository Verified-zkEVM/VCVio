/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire
public import HashSigTest.SLHDSA.SHAKE128s.Support

/-!
# Executable fixed-context wire query translation

The actual transformed adversary receives a recognizable encoded public key and signing
reply. A deterministic trace handler checks private sampling, repeated hash requests, signing
context and the final forgery without running FIPS key generation. A source-counted toy game
also checks exact replay and a distinct signature on the same signed message.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.SHAKE128s.WireBridgeTest

open Bridge

/-- Reject an observable mismatch with a nonzero executable exit. -/
def ensure (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"SHAKE-128s wire bridge check failed: {label}")

/-- A nonempty context whose framing is visible in both requests and the final forgery. -/
def context : SLHDSA.Security.PureContext := ⟨[0xCA, 0xFE], by decide⟩

/-- A typed public key with distinct seed and root bytes. -/
def publicKey : PublicKeyCore FIPS205.core :=
  ⟨Vector.replicate 16 0x12, Vector.replicate 16 0x34⟩

/-- Observable target queries, in chronological order. -/
inductive Event where
  | sample (index : Nat)
  | hash (input : Bytes)
  | sign (request : Message)
deriving DecidableEq

/-- The expected 30-byte hash reply. -/
def hashReply : FIPS205.Answer := Vector.replicate 30 0xA6

/-- The source program checks public-key encoding and every forwarded reply before forging. -/
def wireAdversary : StrongUnforgeableAdversary (wireAlgorithm context) where
  main key := do
    let sample : Fin 2 ← query (spec :=
      (unifSpec + SLHDSA.Security.shakeSpec FIPS205.params) + (Bytes →ₒ Bytes)) (.inl (.inl 1))
    let first : FIPS205.Answer ← query (spec :=
      (unifSpec + SLHDSA.Security.shakeSpec FIPS205.params) + (Bytes →ₒ Bytes))
        (.inl (.inr [0x91]))
    let second : FIPS205.Answer ← query (spec :=
      (unifSpec + SLHDSA.Security.shakeSpec FIPS205.params) + (Bytes →ₒ Bytes))
        (.inl (.inr [0x91]))
    let signature ← query (spec :=
      (unifSpec + SLHDSA.Security.shakeSpec FIPS205.params) + (Bytes →ₒ Bytes)) (.inr [0x41])
    return (if key == List.replicate 16 0x12 ++ List.replicate 16 0x34 &&
      sample.val == 1 && first == hashReply && second == hashReply then [0x42] else [], signature)

/-- Log actual target queries and answer with recognizable values. -/
def handler (answer : Option Bytes) :
    QueryImpl (Game.World FIPS205.Answer + Game.SigningSpec) (StateM (List Event))
  | .inl (.inl index) => do
      modify (· ++ [.sample index])
      return ⟨index, Nat.lt_succ_self index⟩
  | .inl (.inr input) => do
      modify (· ++ [.hash input])
      return hashReply
  | .inr request => do
      modify (· ++ [.sign request])
      return answer

/-- Execute the actual transformed adversary, without a challenger key-generation phase. -/
def run (answer : Option Bytes) : Game.Forgery × List Event :=
  (simulateQ (handler answer) ((fixedContextAdversary context wireAdversary).main publicKey)).run []

/-- The computable shared body is the program field of the actual transformation. -/
example : (fixedContextAdversary context wireAdversary).main publicKey =
    fixedContextMain context wireAdversary.main publicKey :=
  fixedContextAdversary_main context wireAdversary publicKey

/-- A source adversary returns either its actual signing reply or a distinct accepted signature. -/
def freshnessAdversary (different : Bool) :
    StrongUnforgeableAdversary (wireAlgorithm context) where
  main key := do
    let signature ← query (spec :=
      (unifSpec + SLHDSA.Security.shakeSpec FIPS205.params) + (Bytes →ₒ Bytes)) (.inr [0x41])
    return ([0x41], if key == List.replicate 16 0x12 ++ List.replicate 16 0x34 &&
      signature == [0xBE, 0xEF] then
        if different then [0xBE, 0xEE] else signature
      else [])

/-- A cheap scheme sharing the actual typed public key and accepting two signature byte strings. -/
def freshnessSchemeConfig : TestSupport.ToySchemeConfig (PublicKeyCore FIPS205.core) := {
  publicKey := publicKey
  signingReply := some [0xBE, 0xEF]
  acceptedSignatures := [[0xBE, 0xEF], [0xBE, 0xEE]] }

/-- Run the actual transformed adversary through the proved-equal counted-game runner. -/
def runFreshness (different : Bool) :
    ((Game.Outcome × Unforgeability.QueryCounts) × List (Bytes × FIPS205.Answer)) ×
      TestSupport.BackendTrace :=
  TestSupport.runWithCache hashReply
    (TestSupport.toyScheme (Output := FIPS205.Answer) freshnessSchemeConfig)
    (fixedContextAdversary context (freshnessAdversary different))

/-- Exact replay loses while a different valid signature on the same signed message wins. -/
def checkFreshness : IO Unit := do
  for different in [false, true] do
    let (((outcome, counts), _), trace) := runFreshness different
    ensure "actual transformed signing request and reply"
      (decide (outcome.signed = [⟨⟨[0x41], [0xCA, 0xFE]⟩, some [0xBE, 0xEF]⟩]))
    ensure "same signed message and fixed context"
      (outcome.forgery.message.message == [0x41] &&
        outcome.forgery.message.context == [0xCA, 0xFE])
    ensure "reply-dependent candidate signature"
      (outcome.forgery.signature == if different then [0xBE, 0xEE] else [0xBE, 0xEF])
    ensure "both literal signatures verify" outcome.verified
    ensure "actual returned-pair freshness" (decide (Game.Fresh outcome.signed outcome.forgery) ==
      different)
    ensure "actual computed win bit" (decide (Game.Wins outcome) == different)
    ensure "keygen and signer source counts" (counts .keygen == 1 && counts .signer == 2)
    ensure "direct, signing and verifier source counts"
      (counts .hash == 0 && counts .sign == 1 && counts .verifier == 1)
    ensure "selected work two" (TestSupport.selectedWork counts == 2)
    ensure "four full calls and four fresh answers"
      (trace.hashCalls == 4 && trace.answerDraws == 4 && trace.privateSamples == 0)
    ensure "chronological honest hash traffic" (trace.hashInputs == [[0], [1], [2], [4]])
  IO.println "SLH-DSA SHAKE-128s wire freshness: PASS (replay loses; distinct signature wins)"

/-- The actual pure-mode framer reports an oversized context with its observed length. -/
theorem encodePureMessage_error (request : Message) (long : 255 < request.context.length) :
    External.encodePureMessage request.context request.message =
      .error (.contextTooLong request.context.length) := by
  unfold External.encodePureMessage External.encodeMessage
  rw [External.requireContext_eq_error request.context long]
  rfl

/-- Execute the actual framing rejection when the context cannot fit its one-byte length. -/
def executableRejectedSign (request : Message) (long : 255 < request.context.length) :
    OracleComp (Game.World FIPS205.Answer) (Option Bytes) :=
  match framed : External.encodePureMessage request.context request.message with
  | .error _ => pure none
  | .ok _ => False.elim (by rw [encodePureMessage_error request long] at framed; cases framed)

/-- The computable context rejection equals actual FIPS signing at every secret key. -/
theorem executableRejectedSign_eq (sk : SecretKeyCore FIPS205.core)
    (request : Message) (long : 255 < request.context.length) :
    executableRejectedSign request long = FIPS205.scheme.sign sk request := by
  unfold executableRejectedSign
  split <;> rename_i framed
  · simp only [FIPS205.scheme, framed]
  · rw [encodePureMessage_error request long] at framed
    cases framed

/-- Retain the actual request charge and rejected-answer log of one invalid signing call. -/
def executableRejectedSigningCall (request : Message) (long : 255 < request.context.length) :
    OracleComp (Game.World FIPS205.Answer) ((Option Bytes × Game.Counts) × Game.SigningLog) :=
  (fun answer => ((answer, Game.Counts.single .signing 1), [⟨request, answer⟩])) <$>
    executableRejectedSign request long

/-- The executable invalid-context signing call is the actual source-counted game phase. -/
theorem executableRejectedSigningCall_eq (sk : SecretKeyCore FIPS205.core)
    (request : Message) (long : 255 < request.context.length) :
    executableRejectedSigningCall request long =
      Game.runPhase FIPS205.scheme sk
        (liftM ((Game.World FIPS205.Answer + Game.SigningSpec).query (.inr request))) [] := by
  rw [Game.runPhase_query_sign]
  rw [executableRejectedSigningCall, executableRejectedSign_eq sk request long]
  rfl

/-- Classify the actual framing or signature-decoding rejection branches. -/
def rejects (request : Message) (signature : Bytes) : Bool :=
  match External.encodePureMessage request.context request.message with
  | .error _ => true
  | .ok _ =>
    match decodeSignature FIPS205.params
        (Concrete.shakeWireCodec FIPS205.params.params) signature with
    | .error _ => true
    | .ok _ => false

/-- Execute actual framing and decoding on inputs whose parsed-valid branch is impossible. -/
def executableRejectedVerify (request : Message) (signature : Bytes)
    (rejected : rejects request signature = true) : OracleComp (Game.World FIPS205.Answer) Bool :=
  match framed : External.encodePureMessage request.context request.message with
  | .error _ => pure false
  | .ok _ =>
    match parsed : decodeSignature FIPS205.params
        (Concrete.shakeWireCodec FIPS205.params.params) signature with
    | .error _ => pure false
    | .ok _ => False.elim (by simp [rejects, framed, parsed] at rejected)

/-- The executable rejection branches are exactly the actual FIPS verifier program. -/
theorem executableRejectedVerify_eq (pk : PublicKeyCore FIPS205.core) (request : Message)
    (signature : Bytes) (rejected : rejects request signature = true) :
    executableRejectedVerify request signature rejected =
      FIPS205.scheme.verify pk request signature := by
  unfold executableRejectedVerify
  split <;> rename_i framed
  · simp [FIPS205.scheme, framed]
  · split <;> rename_i parsed
    · simp [FIPS205.scheme, framed, parsed]
    · simp [rejects, framed, parsed] at rejected

/-- The strict SHAKE-128s signature parser rejects the empty byte string by its exact width. -/
theorem decode_empty :
    decodeSignature FIPS205.params (Concrete.shakeWireCodec FIPS205.params.params) [] =
      .error (.invalidLength FIPS205.params.params.signatureBytes 0) := by
  exact WireCodec.decode_eq_error_of_length_ne _ _ (by decide)

/-- Empty signatures are rejected independently of the external context. -/
theorem rejects_empty (request : Message) : rejects request [] = true := by
  unfold rejects
  split
  · rfl
  · simp only [decode_empty]

/-- A context longer than the FIPS boundary rejects before the signature is decoded. -/
theorem rejects_long_context (request : Message) (signature : Bytes)
    (long : 255 < request.context.length) : rejects request signature = true := by
  have framed : External.encodePureMessage request.context request.message =
      .error (.contextTooLong request.context.length) := by
    unfold External.encodePureMessage External.encodeMessage
    rw [External.requireContext_eq_error request.context long]
    rfl
  simp [rejects, framed]

/-- Every signature whose byte width is wrong follows a certified decoding rejection branch. -/
theorem rejects_wrong_length (request : Message) (signature : Bytes)
    (wrong : signature.length ≠ FIPS205.params.params.signatureBytes) :
    rejects request signature = true := by
  have parsed : decodeSignature FIPS205.params
      (Concrete.shakeWireCodec FIPS205.params.params) signature =
      .error (.invalidLength FIPS205.params.params.signatureBytes signature.length) :=
    WireCodec.decode_eq_error_of_length_ne _ _ wrong
  unfold rejects
  split
  · rfl
  · simp only [parsed]

/-- Count actual verifier work through the proved-equal executable rejection front end. -/
def runRejected (request : Message) (signature : Bytes)
    (rejected : rejects request signature = true) :
    (((Bool × Game.Counts) × List (Bytes × FIPS205.Answer)) × TestSupport.BackendTrace) :=
  ((simulateQ (TestSupport.cachedHandler hashReply)
    (Game.countQueries
      (fun input => Game.Counts.single .verification
        (Game.hashCost (Output := FIPS205.Answer) input))
      (executableRejectedVerify request signature rejected))).run []).run {}

/-- Every certified rejection returns false without hash calls, cache draws or private samples. -/
def checkRejected (label : String) (request : Message) (signature : Bytes)
    (rejected : rejects request signature = true) : IO Unit := do
  let (((verified, counts), cache), trace) := runRejected request signature rejected
  ensure s!"{label}: verification rejects" (!verified)
  ensure s!"{label}: no verification, signing or direct work"
    (counts .verification == 0 && counts .signing == 0 && counts .hash == 0)
  ensure s!"{label}: no backend traffic"
    (trace.hashCalls == 0 && trace.answerDraws == 0 && trace.privateSamples == 0)
  ensure s!"{label}: cache and hash trace stay empty" (cache.isEmpty && trace.hashInputs.isEmpty)

/-- The actual FIPS invalid-context signer returns `none`, charges one request and never hashes. -/
def checkRejectedSigning (request : Message) (long : 255 < request.context.length) : IO Unit := do
  let ((((answer, counts), signed), cache), trace) :=
    ((simulateQ (TestSupport.cachedHandler hashReply)
      (executableRejectedSigningCall request long)).run []).run {}
  ensure "actual rejected FIPS signer returns none" (answer == none)
  ensure "actual rejected FIPS signing request charged once" (counts .signing == 1)
  ensure "actual rejected FIPS signer has no hash or verifier work"
    (counts .hash == 0 && counts .verification == 0)
  ensure "actual rejected FIPS signing log" (decide (signed = [⟨request, none⟩]))
  ensure "actual rejected FIPS signer makes no backend calls"
    (trace.hashCalls == 0 && trace.answerDraws == 0 && trace.privateSamples == 0)
  ensure "actual rejected FIPS signer preserves empty cache/trace"
    (cache.isEmpty && trace.hashInputs.isEmpty)

/-- Execute the real pure-mode framer at lengths 255 and 256 and the strict malformed parser. -/
def checkBoundaries : IO Unit := do
  let request255 : Message := ⟨[0x41], List.replicate 255 0xCA⟩
  match External.encodePureMessage request255.context request255.message with
  | .error _ => throw (IO.userError "255-byte pure context was rejected")
  | .ok framed =>
      ensure "actual 255-byte pure frame"
        (framed == [0, 0xFF] ++ List.replicate 255 0xCA ++ [0x41])
  checkRejected "context255/malformed signature" request255 [] (rejects_empty request255)
  let request256 : Message := ⟨[0x41], List.replicate 256 0xCA⟩
  match External.encodePureMessage request256.context request256.message with
  | .ok _ => throw (IO.userError "256-byte pure context was admitted")
  | .error error =>
      ensure "actual 256-byte context error" (decide (error = .contextTooLong 256))
  have long256 : 255 < request256.context.length := by
    change 255 < (List.replicate 256 (0xCA : UInt8)).length
    rw [List.length_replicate]
    exact Nat.lt_succ_self 255
  let fullWidth := List.replicate FIPS205.params.params.signatureBytes (0 : UInt8)
  checkRejected "context256" request256 fullWidth
    (rejects_long_context request256 fullWidth long256)
  checkRejectedSigning request256 long256
  match decodeSignature FIPS205.params (Concrete.shakeWireCodec FIPS205.params.params) [] with
  | .ok _ => throw (IO.userError "empty SHAKE-128s signature was admitted")
  | .error error =>
      ensure "actual malformed signature error"
        (decide (error = .invalidLength FIPS205.params.params.signatureBytes 0))
  let ordinary : Message := ⟨[0x41], context.bytes⟩
  checkRejected "empty signature" ordinary [] (rejects_empty ordinary)
  let oversized := List.replicate (FIPS205.params.params.signatureBytes + 1) (0 : UInt8)
  have oversizedWidth : oversized.length ≠ FIPS205.params.params.signatureBytes := by
    change (List.replicate (FIPS205.params.params.signatureBytes + 1) (0 : UInt8)).length ≠ _
    rw [List.length_replicate]
    omega
  checkRejected "oversized signature" ordinary oversized
    (rejects_wrong_length ordinary oversized oversizedWidth)
  IO.println "SLH-DSA SHAKE-128s wire boundaries: PASS (contexts 255/256; malformed zero-work)"

/-- Check literal trace, byte and context observations, including the total fallback branch. -/
def check : IO Unit := do
  ensure "literal pure-mode frame" (context.encode [0x41] == [0, 2, 0xCA, 0xFE, 0x41])
  let expectedTrace : List Event := [
    .sample 1, .hash [0x91], .hash [0x91], .sign ⟨[0x41], [0xCA, 0xFE]⟩]
  let (forgery, trace) := run (some [0xBE, 0xEF])
  ensure "private, repeated-hash and context-attached signing queries" (trace == expectedTrace)
  ensure "encoded public key and forwarded oracle responses" (forgery.message.message == [0x42])
  ensure "final forgery context" (forgery.message.context == [0xCA, 0xFE])
  ensure "recognizable Some signing reply" (forgery.signature == [0xBE, 0xEF])
  let (fallback, fallbackTrace) := run none
  ensure "None reply still makes exactly one signing request" (fallbackTrace == expectedTrace)
  ensure "total None fallback" (fallback.signature == [])
  checkFreshness
  checkBoundaries
  IO.println "SLH-DSA SHAKE-128s wire bridge: PASS (actual query translation; fixed context)"

end SLHDSA.SHAKE128s.WireBridgeTest

/-- Execute the fixed-context wire translation controls. -/
def main : IO Unit := SLHDSA.SHAKE128s.WireBridgeTest.check
