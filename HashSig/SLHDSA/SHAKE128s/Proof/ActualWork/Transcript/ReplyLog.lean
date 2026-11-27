/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.FIPS205.Params
public import HashSig.SLHDSA.SHAKE128s.Statement.Requests
public import HashSig.SLHDSA.Concrete.Codec
public import VCVio.CryptoFoundations.SignatureAlg.SigningView
public import HashSig.SLHDSA.External.Framing

/-!
# Decoding accepted signing replies and transporting freshness
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA

namespace SLHDSA.SHAKE128s.Settlement

/-- The internal SHAKE-128s signature obtained by decoding a wire response. -/
abbrev Sig := GeneralScheme.SignatureCore FIPS205.params FIPS205.core
/-- Signing requests paired with their optional byte responses, including rejections. -/
abbrev Log := QueryLog (Message →ₒ Option Bytes)

/-- Encode a pure-mode request when its context fits the FIPS 205 framing limit. -/
@[expose] def framed (req : Message) : Option Bytes :=
  (External.encodePureMessage req.context req.message).toOption

/-- Decode bytes as a SHAKE-128s signature using the FIPS wire codec. -/
@[expose] def parsed (wire : Bytes) : Option Sig :=
  (decodeSignature FIPS205.params (Concrete.shakeWireCodec FIPS205.params.params) wire).toOption

/-- Keep the signing-log entries whose requests frame successfully and whose replies
decode as signatures, preserving their order. -/
@[expose] def typedLog (log : Log) : QueryLog (Bytes →ₒ Sig) :=
  log.filterMap fun entry => do
    let msg ← framed entry.1
    let wire ← entry.2
    let sig ← parsed wire
    pure ⟨msg, sig⟩

private theorem framed_injective {r r' : Message} {msg : Bytes}
    (hr : framed r = some msg) (hr' : framed r' = some msg) : r = r' := by
  obtain ⟨hc, hm⟩ := External.encodePureMessage_toOption_injective _ _ _ _ _ hr hr'
  cases r
  cases r'
  congr

private theorem parsed_canonical {wire : Bytes} {sig : Sig} (hp : parsed wire = some sig) :
    wire = encodeSignature FIPS205.params (Concrete.shakeWireCodec FIPS205.params.params) sig := by
  apply (decodeSignature_eq_ok_iff _ _ _ _).1
  unfold parsed at hp
  cases h : decodeSignature FIPS205.params (Concrete.shakeWireCodec FIPS205.params.params) wire
    <;> simp_all [Except.toOption]

/-- A typed entry comes from the same request and successful wire reply in the raw log. -/
theorem data_of_mem_typedLog (log : Log) (entry : Σ _ : Bytes, Sig) (h : entry ∈ typedLog log) :
    ∃ raw ∈ log, ∃ w, raw.2 = some w ∧ parsed w = some entry.2 ∧ framed raw.1 = some entry.1 := by
  obtain ⟨raw, mem, same⟩ := List.mem_filterMap.mp h
  change (framed raw.1).bind (fun m => raw.2.bind (fun w => (parsed w).bind
    (fun k => some (⟨m, k⟩ : Σ _ : Bytes, Sig)))) = some entry at same
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at same
  obtain ⟨_, hf, w, hw, _, hp, rfl⟩ := same
  exact ⟨raw, mem, w, hw, hp, hf⟩

/-- A rejected signing attempt contributes no entry to the decoded log. -/
theorem typedLog_append_rejected (log : Log) (req : Message) :
    typedLog (log ++ [⟨req, none⟩]) = typedLog log := by
  cases h : framed req <;> simp [typedLog, List.filterMap_append, h]

private theorem filterMap_append_some {A B : Type} (f : A → Option B) (as : List A)
    (a : A) (b : B) (h : f a = some b) :
    (as ++ [a]).filterMap f = as.filterMap f ++ [b] := by
  simp [List.filterMap_append, h]

/-- Encoding a structured FIPS signature always yields a successfully parsed reply. -/
theorem parsed_encoded (sig : Sig) :
    parsed (encodeSignature FIPS205.params (Concrete.shakeWireCodec FIPS205.params.params) sig) =
      some sig := by
  simpa only [parsed, Except.toOption] using congrArg Except.toOption
    (decodeSignature_encode FIPS205.params (Concrete.shakeWireCodec FIPS205.params.params) sig)

/-- An accepted wire reply contributes its framed message and decoded signature. -/
theorem typedLog_append_accepted (log : Log) (req : Message) (msg wire : Bytes) (sig : Sig)
    (h : framed req = some msg) (hp : parsed wire = some sig) :
    typedLog (log ++ [⟨req, some wire⟩]) = typedLog log ++ [⟨msg, sig⟩] := by
  unfold typedLog
  apply filterMap_append_some
  change (framed req).bind (fun m => (parsed wire).bind
    (fun k => some (⟨m, k⟩ : Σ _ : Bytes, Sig))) = some ⟨msg, sig⟩
  rw [h, hp]
  rfl

/-- The original log's freshness excludes the typed forgery in its literal decoded log. -/
theorem fresh_decoded (log : Log) (r : Message) (wire msg : Bytes) (sig : Sig)
    (hf : framed r = some msg) (hp : parsed wire = some sig)
    (fresh : SigningView.Fresh id log (r, wire)) : ⟨msg, sig⟩ ∉ typedLog log := by
  intro mem
  obtain ⟨raw, he, w, hw, hs, hm⟩ := data_of_mem_typedLog log _ mem
  exact (SigningView.optional_fresh_iff log r wire).1 fresh
    ⟨raw, he, framed_injective hm hf, hw.trans (congrArg some
      ((parsed_canonical hs).trans (parsed_canonical hp).symm))⟩

end SLHDSA.SHAKE128s.Settlement
