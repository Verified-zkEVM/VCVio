/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.AnswerRepresentation

/-! # Ordinary full30-byte answer clients with chronological phase/input cost words -/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA.SHAKE128s SLHDSA.SHAKE128s.Bridge

namespace SLHDSA.Refactor.AnswerRepresentation

/-- Chronological words of actual phase/input/request events. -/
abbrev Word := Additive (FreeMonoid (SigningView.Event (Game.World HashOutput) Message))

/-- Charge one chronological event for each operation of the source program. -/
@[expose] def paperPolicy (event : SigningView.Event (Game.World HashOutput) Message) : Word :=
  Additive.ofMul (FreeMonoid.of event)

/-- Pull the source event charge back along the shared-input representation map. -/
@[expose] def bytePolicy (event : SigningView.Event (Game.World FIPS205.Answer) Message) : Word :=
  paperPolicy (SigningView.relabelEvent (R := Game.World FIPS205.Answer)
    (S := Game.World HashOutput) event)

/-- One joint observation retains chronological costs and the complete actual public cache. -/
theorem ordered_client {PK SK : Type} (scheme : Game.ExternalScheme HashOutput PK SK)
    (adversary : Game.Adversary HashOutput PK)
    (cache : (SLHDSA.SHAKE128s.Bytes →ₒ HashOutput).QueryCache) :
    let HR := (unifFwdImpl (SLHDSA.SHAKE128s.Bytes →ₒ HashOutput)).liftTarget
        (WriterT (QueryLog (SLHDSA.SHAKE128s.Bytes →ₒ HashOutput))
          (StateT (SLHDSA.SHAKE128s.Bytes →ₒ HashOutput).QueryCache ProbComp)) +
      (SLHDSA.SHAKE128s.Bytes →ₒ HashOutput).randomOracle.withLogging
    let HS := (unifFwdImpl (SLHDSA.SHAKE128s.Bytes →ₒ FIPS205.Answer)).liftTarget
        (WriterT (QueryLog (SLHDSA.SHAKE128s.Bytes →ₒ FIPS205.Answer))
          (StateT (SLHDSA.SHAKE128s.Bytes →ₒ FIPS205.Answer).QueryCache ProbComp)) +
      (SLHDSA.SHAKE128s.Bytes →ₒ FIPS205.Answer).randomOracle.withLogging
    (simulateQ HS
        (SigningView.countedExperiment bytePolicy
          (SigningView.relabelView SharedExperiment.byteAnswers
            (SharedExperiment.externalView scheme))
          (SigningView.relabelMain SharedExperiment.byteAnswers
            (SharedExperiment.externalMain adversary)))).run.run
            (QueryCache.mapAnswers (fun _ => answerEquiv) cache) =ᵈ
      (fun output => ((output.1.1, QueryLog.mapAnswers (fun _ => answerEquiv) output.1.2),
        QueryCache.mapAnswers (fun _ => answerEquiv) output.2)) <$>
        (simulateQ HR (SigningView.countedExperiment paperPolicy
          (SharedExperiment.externalView scheme)
          (SharedExperiment.externalMain adversary))).run.run cache := by
  apply SharedExperiment.answerRepresentation_joint
  intro event
  cases event <;> rfl

end SLHDSA.Refactor.AnswerRepresentation
