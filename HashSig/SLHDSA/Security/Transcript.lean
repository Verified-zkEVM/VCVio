/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Security.OracleSurface

/-!
# Honest SLH-DSA Security Transcripts

This module fixes the probability space used by the security architecture.  Keys, signatures, and
verification come from an abstract `SchemeInterface`; S02 does not claim that its fields refine one
general SLH-DSA construction.  The adversary is interpreted through the public-only query language,
and the complete execution query log is produced by VCVio's
`QueryImpl.withLogging`.  The quantitative component games have their own source-shaped target
oracles and do not claim that their targets occur in this outer scheme log.

An honest signing call is logged as one execution event.  A refinement can expose the primitive
calls made inside Algorithms 19 and 20 without changing the public adversary language.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SLHDSA.Security

/-- The observable result and full named-query log of one adversarial execution under `keys`. -/
structure Transcript {p : Params} {prims : Primitives p} (scheme : SchemeInterface prims)
    (keys : GeneratedKeyPair prims) where
  forgery : MessageInput × scheme.Signature
  log : QueryLog (oracleSpec prims scheme keys.publicKey)

/-! ## Deterministic transcript projections -/

/-- Signing requests made in an execution log, in execution order. -/
def signedRequests {p : Params} {prims : Primitives p} {scheme : SchemeInterface prims}
    {pk : PublicKey prims} (log : QueryLog (oracleSpec prims scheme pk)) : List MessageInput :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.sign request, _⟩ => some request
    | _ => none

/-- Reconstruct the authoritative ITSR history from honest signing queries.  Each signing answer
contains its message randomizer `R`; the digest is evaluated from that `R`, the complete request,
and the generated public key rather than accepted from an untrusted record field. -/
def signingITSRHistory {p : Params} {prims : Primitives p} (scheme : SchemeInterface prims)
    (keys : GeneratedKeyPair prims) (encode : MessageInput → List Byte)
    (log : QueryLog (oracleSpec prims scheme keys.publicKey)) : List (ITSRRecord prims) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.sign request, signature⟩ =>
        let randomizer := scheme.randomizer signature
        some {
          input := ⟨randomizer, request⟩
          digest := prims.Hmsg randomizer keys.publicSeed keys.publicKey.pkRoot (encode request)
        }
    | _ => none

@[simp]
theorem signingITSRHistory_singleton_sign {p : Params} {prims : Primitives p}
    (scheme : SchemeInterface prims) (keys : GeneratedKeyPair prims)
    (encode : MessageInput → List Byte) (request : MessageInput)
    (signature : scheme.Signature) :
    signingITSRHistory scheme keys encode [⟨.sign request, signature⟩] =
      [{
        input := ⟨scheme.randomizer signature, request⟩
        digest := prims.Hmsg (scheme.randomizer signature) keys.publicSeed
          keys.publicKey.pkRoot (encode request)
      }] := rfl

@[simp]
theorem signingITSRHistory_singleton_hmsg {p : Params} {prims : Primitives p}
    (scheme : SchemeInterface prims) (keys : GeneratedKeyPair prims)
    (encode : MessageInput → List Byte)
    (origin : QueryOrigin) (randomizer : prims.Y) (request : MessageInput)
    (digest : Bytes p.m) :
    signingITSRHistory scheme keys encode [⟨.hmsg origin randomizer request, digest⟩] = [] := rfl

/-- Every reconstructed history record is coherent with the generated public key. -/
theorem signingITSRHistory_coherent {p : Params} {prims : Primitives p}
    (scheme : SchemeInterface prims) (keys : GeneratedKeyPair prims)
    (encode : MessageInput → List Byte)
    (log : QueryLog (oracleSpec prims scheme keys.publicKey)) :
    ∀ record ∈ signingITSRHistory scheme keys encode log,
      record.Coherent keys.publicKey encode := by
  intro record hrecord
  rw [signingITSRHistory, List.mem_filterMap] at hrecord
  obtain ⟨⟨query, answer⟩, _, hentry⟩ := hrecord
  cases query <;> simp at hentry
  subst record
  rfl

/-- The forgery's own keyed `H_msg` record.  Its randomizer is `R`, the first signature field. -/
def forgeryITSRRecord {p : Params} {prims : Primitives p} (scheme : SchemeInterface prims)
    (keys : GeneratedKeyPair prims) (encode : MessageInput → List Byte)
    (transcript : Transcript scheme keys) : ITSRRecord prims :=
  {
    input := ⟨scheme.randomizer transcript.forgery.2, transcript.forgery.1⟩
    digest := prims.Hmsg (scheme.randomizer transcript.forgery.2) keys.publicSeed
      keys.publicKey.pkRoot
      (encode transcript.forgery.1)
  }

@[simp]
theorem forgeryITSRRecord_coherent {p : Params} {prims : Primitives p}
    (scheme : SchemeInterface prims) (keys : GeneratedKeyPair prims)
    (encode : MessageInput → List Byte) (transcript : Transcript scheme keys) :
    (forgeryITSRRecord scheme keys encode transcript).Coherent keys.publicKey encode := by
  simp [forgeryITSRRecord, ITSRRecord.Coherent, GeneratedKeyPair.publicSeed]

/-- EUF-CMA success in the exact message mode/context domain. -/
def ForgerySuccess {p : Params} {prims : Primitives p} (scheme : SchemeInterface prims)
    (keys : GeneratedKeyPair prims) (transcript : Transcript scheme keys) : Prop :=
  scheme.verify keys.publicKey transcript.forgery.1 transcript.forgery.2 = true ∧
    Fresh (signedRequests transcript.log) transcript.forgery.1

/-- ITSR success extracted from the same execution transcript as the forgery event. -/
def TranscriptITSRBreak {p : Params} {prims : Primitives p} [DecidableEq prims.Y]
    (scheme : SchemeInterface prims) (keys : GeneratedKeyPair prims)
    (encode : MessageInput → List Byte) (transcript : Transcript scheme keys) : Prop :=
  ITSRBreak keys.publicKey encode (signingITSRHistory scheme keys encode transcript.log)
    (forgeryITSRRecord scheme keys encode transcript)

/-! ## The honest distribution -/

/-- Run `adversary` in the abstract classical signature-scheme experiment.  This distribution owns
one interface-supplied key-generation sample and its packaged public/secret seed coherence; general
SLH-DSA construction refinement and external request encoding remain explicit future boundaries. -/
def honestTranscriptDistribution {p : Params} (prims : Primitives p)
    (scheme : SchemeInterface prims) (encode : MessageInput → List Byte)
    (adversary : ClassicalAdversary prims scheme) :
    ProbComp (Σ keys : GeneratedKeyPair prims, Transcript scheme keys) := do
  let keys ← scheme.keygen
  let execution := simulateQ (adversaryQueryImpl prims scheme keys.publicKey)
    (adversary.main keys.publicKey)
  let result ← (simulateQ
    ((queryImpl scheme keys encode).withLogging)
    execution).run
  return ⟨keys, { forgery := result.1, log := result.2 }⟩

end SLHDSA.Security
