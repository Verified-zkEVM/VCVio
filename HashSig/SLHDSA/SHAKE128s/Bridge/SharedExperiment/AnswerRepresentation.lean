/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.Relabel.RandomOracle
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Defs
public import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings

/-!
# Complete counted observations in the full byte-answer representation

The same external view and adversary are interpreted through the full30-byte answer
equivalence. Explicit policies retain the candidate, raw replies, verifier result and ordered
cost together with the public query-answer log and final warm cache. This is a representation
of one program; it does not reorder its private draws or identify different keygen programs.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA.SHAKE128s

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- The private-answer identity and full30-byte public-answer equivalence at each input. -/
abbrev byteAnswers : ∀ input,
    (Game.World HashOutput).Range input ≃ (Game.World FIPS205.Answer).Range input :=
  RandomOracleAnswerRelabel.worldAnswers (R := Bytes →ₒ HashOutput)
    (S := Bytes →ₒ FIPS205.Answer) (fun _ => answerEquiv)

/-- Full joint representation transport under the actual phase/input/request policy square. -/
theorem answerRepresentation_joint {PK SK C : Type} [AddMonoid C]
    (scheme : Game.ExternalScheme HashOutput PK SK) (adversary : Game.Adversary HashOutput PK)
    (paperPolicy : SigningView.Event (Game.World HashOutput) Message → C)
    (bytePolicy : SigningView.Event (Game.World FIPS205.Answer) Message → C)
    (policyMap : ∀ event, paperPolicy event = bytePolicy (SigningView.relabelEvent event))
    (cache : (Bytes →ₒ HashOutput).QueryCache) :
    let HR := (unifFwdImpl (Bytes →ₒ HashOutput)).liftTarget
        (WriterT (QueryLog (Bytes →ₒ HashOutput))
          (StateT (Bytes →ₒ HashOutput).QueryCache ProbComp)) +
      (Bytes →ₒ HashOutput).randomOracle.withLogging
    let HS := (unifFwdImpl (Bytes →ₒ FIPS205.Answer)).liftTarget
        (WriterT (QueryLog (Bytes →ₒ FIPS205.Answer))
          (StateT (Bytes →ₒ FIPS205.Answer).QueryCache ProbComp)) +
      (Bytes →ₒ FIPS205.Answer).randomOracle.withLogging
    (simulateQ HS
        (SigningView.countedExperiment bytePolicy
          (SigningView.relabelView byteAnswers (externalView scheme))
          (SigningView.relabelMain byteAnswers (externalMain adversary)))).run.run
            (QueryCache.mapAnswers (fun _ => answerEquiv) cache) =ᵈ
      (fun output => ((output.1.1, QueryLog.mapAnswers (fun _ => answerEquiv) output.1.2),
        QueryCache.mapAnswers (fun _ => answerEquiv) output.2)) <$>
        (simulateQ HR (SigningView.countedExperiment paperPolicy
          (externalView scheme) (externalMain adversary))).run.run cache :=
  SigningView.countedExperiment_world_transport (fun _ => answerEquiv)
    (fun _ => map_answerEquiv_uniformSample) paperPolicy bytePolicy
    (externalView scheme) (externalMain adversary) policyMap cache

/-- The canonical five-source observation has the same full byte-answer/log/cache law. -/
theorem answerRepresentation_sourceJoint {PK SK : Type}
    (scheme : Game.ExternalScheme HashOutput PK SK) (adversary : Game.Adversary HashOutput PK)
    (cache : (Bytes →ₒ HashOutput).QueryCache) :
    let HR := (unifFwdImpl (Bytes →ₒ HashOutput)).liftTarget
        (WriterT (QueryLog (Bytes →ₒ HashOutput))
          (StateT (Bytes →ₒ HashOutput).QueryCache ProbComp)) +
      (Bytes →ₒ HashOutput).randomOracle.withLogging
    let HS := (unifFwdImpl (Bytes →ₒ FIPS205.Answer)).liftTarget
        (WriterT (QueryLog (Bytes →ₒ FIPS205.Answer))
          (StateT (Bytes →ₒ FIPS205.Answer).QueryCache ProbComp)) +
      (Bytes →ₒ FIPS205.Answer).randomOracle.withLogging
    (simulateQ HS
        (SigningView.countedExperiment (sourcePolicy (Output := FIPS205.Answer))
          (SigningView.relabelView byteAnswers (externalView scheme))
          (SigningView.relabelMain byteAnswers (externalMain adversary)))).run.run
            (QueryCache.mapAnswers (fun _ => answerEquiv) cache) =ᵈ
      (fun output => ((output.1.1, QueryLog.mapAnswers (fun _ => answerEquiv) output.1.2),
        QueryCache.mapAnswers (fun _ => answerEquiv) output.2)) <$>
        (simulateQ HR (canonicalExperiment scheme adversary)).run.run cache := by
  apply answerRepresentation_joint
  intro event
  cases event with
  | ambient phase input => cases input <;> rfl
  | signingAttempt _ => rfl

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
