/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Security.OracleSurface

/-!
# Honest SLH-DSA Security Transcripts

This module fixes the probability space used by the security architecture.  Keys come from
`generateKeyPair`, the adversary is interpreted through the public-only query language, and the
complete execution query log is produced by VCVio's `QueryImpl.withLogging`.  Target data is
consumed only by component programs run after this distribution is sampled; certified target
packages additionally prove that every formula-indexed target occurs in this same log.

An honest signing call is logged as one execution event.  A refinement can expose the primitive
calls made inside Algorithms 19 and 20 without changing the public adversary language.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SLHDSA.Security

/-- The observable result and full named-query log of one adversarial execution under `keys`. -/
structure Transcript {p : Params} {prims : Primitives p} (keys : GeneratedKeyPair prims) where
  forgery : MessageInput × Signature prims
  log : QueryLog (oracleSpec prims keys.publicKey)

/-! ## Deterministic transcript projections -/

/-- Signing requests made in an execution log, in execution order. -/
def signedRequests {p : Params} {prims : Primitives p} {pk : PublicKey prims} :
    QueryLog (oracleSpec prims pk) → List MessageInput
  | [] => []
  | ⟨.sign request, _⟩ :: rest => request :: signedRequests rest
  | _ :: rest => signedRequests rest

/-- Reconstruct the authoritative ITSR history from honest signing queries.  Each signing answer
contains its message randomizer `R`; the digest is evaluated from that `R`, the complete request,
and the generated public key rather than accepted from an untrusted record field. -/
def signingITSRHistory {p : Params} {prims : Primitives p} (keys : GeneratedKeyPair prims)
    (encode : MessageInput → List Byte) :
    QueryLog (oracleSpec prims keys.publicKey) → List (ITSRRecord prims)
  | [] => []
  | ⟨.sign request, signature⟩ :: rest =>
      {
        input := ⟨signature.1, request⟩
        digest := prims.Hmsg signature.1 keys.publicSeed keys.publicKey.pkRoot (encode request)
      } :: signingITSRHistory keys encode rest
  | _ :: rest => signingITSRHistory keys encode rest

@[simp]
theorem signingITSRHistory_singleton_sign {p : Params} {prims : Primitives p}
    (keys : GeneratedKeyPair prims) (encode : MessageInput → List Byte)
    (request : MessageInput) (signature : Signature prims) :
    signingITSRHistory keys encode [⟨.sign request, signature⟩] =
      [{
        input := ⟨signature.1, request⟩
        digest := prims.Hmsg signature.1 keys.publicSeed keys.publicKey.pkRoot (encode request)
      }] := rfl

@[simp]
theorem signingITSRHistory_singleton_hmsg {p : Params} {prims : Primitives p}
    (keys : GeneratedKeyPair prims) (encode : MessageInput → List Byte)
    (origin : QueryOrigin) (randomizer : prims.Y) (request : MessageInput)
    (digest : Bytes p.m) :
    signingITSRHistory keys encode [⟨.hmsg origin randomizer request, digest⟩] = [] := rfl

/-- Every reconstructed history record is coherent with the generated public key. -/
theorem signingITSRHistory_coherent {p : Params} {prims : Primitives p}
    (keys : GeneratedKeyPair prims) (encode : MessageInput → List Byte)
    (log : QueryLog (oracleSpec prims keys.publicKey)) :
    ∀ record ∈ signingITSRHistory keys encode log,
      record.Coherent keys.publicKey encode := by
  induction log with
  | nil => simp [signingITSRHistory]
  | cons entry rest ih =>
      obtain ⟨query, answer⟩ := entry
      cases query with
      | sign request =>
          intro record hrecord
          simp only [signingITSRHistory, List.mem_cons] at hrecord
          rcases hrecord with rfl | hrest
          · rfl
          · exact ih record hrest
      | prf _ _ => simpa only [signingITSRHistory] using ih
      | prfMsg _ _ _ => simpa only [signingITSRHistory] using ih
      | f _ _ _ => simpa only [signingITSRHistory] using ih
      | h _ _ _ _ => simpa only [signingITSRHistory] using ih
      | tlFors _ _ _ => simpa only [signingITSRHistory] using ih
      | tlWots _ _ _ => simpa only [signingITSRHistory] using ih
      | hmsg _ _ _ => simpa only [signingITSRHistory] using ih

/-- The forgery's own keyed `H_msg` record.  Its randomizer is `R`, the first signature field. -/
def forgeryITSRRecord {p : Params} {prims : Primitives p}
    (keys : GeneratedKeyPair prims) (encode : MessageInput → List Byte)
    (transcript : Transcript keys) : ITSRRecord prims :=
  {
    input := ⟨transcript.forgery.2.1, transcript.forgery.1⟩
    digest := prims.Hmsg transcript.forgery.2.1 keys.publicSeed keys.publicKey.pkRoot
      (encode transcript.forgery.1)
  }

@[simp]
theorem forgeryITSRRecord_coherent {p : Params} {prims : Primitives p}
    (keys : GeneratedKeyPair prims) (encode : MessageInput → List Byte)
    (transcript : Transcript keys) :
    (forgeryITSRRecord keys encode transcript).Coherent keys.publicKey encode := by
  simp [forgeryITSRRecord, ITSRRecord.Coherent, GeneratedKeyPair.publicSeed]

/-- EUF-CMA success in the exact message mode/context domain. -/
def ForgerySuccess {p : Params} {prims : Primitives p} [DecidableEq prims.Y]
    (keys : GeneratedKeyPair prims) (encode : MessageInput → List Byte)
    (transcript : Transcript keys) : Prop :=
  slhVerify prims keys.publicKey (encode transcript.forgery.1) transcript.forgery.2 = true ∧
    Fresh (signedRequests transcript.log) transcript.forgery.1

/-- ITSR success extracted from the same execution transcript as the forgery event. -/
def TranscriptITSRBreak {p : Params} {prims : Primitives p} [DecidableEq prims.Y]
    (keys : GeneratedKeyPair prims) (encode : MessageInput → List Byte)
    (transcript : Transcript keys) : Prop :=
  ITSRBreak keys.publicKey encode (signingITSRHistory keys encode transcript.log)
    (forgeryITSRRecord keys encode transcript)

/-! ## The honest distribution -/

/-- Run `adversary` in the exact classical experiment.  This distribution owns
key generation and seed coupling; only external request encoding is left as an explicit future
API boundary. -/
def honestTranscriptDistribution {p : Params} (prims : Primitives p)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    (encode : MessageInput → List Byte) (adversary : ClassicalAdversary prims) :
    ProbComp (Σ keys : GeneratedKeyPair prims, Transcript keys) := do
  let keys ← generateKeyPair prims
  let execution := simulateQ (adversaryQueryImpl prims keys.publicKey)
    (adversary.main keys.publicKey)
  let result ← (simulateQ
    ((queryImpl keys encode (fun sk request => slhSign prims sk (encode request))).withLogging)
    execution).run
  return ⟨keys, { forgery := result.1, log := result.2 }⟩

end SLHDSA.Security
