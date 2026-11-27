/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Wire
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.AnswerRepresentation

/-!
# Whole context and public-answer observations

Context attachment uses the actual generated-key FIPS algorithms. Public-answer conversion uses
the full 30-byte equivalence, its actual sampler pushforward and the source-policy square. Raw
signing replies, candidate, verifier, ordered cost, public query-answer log and warm cache remain
joint under these production laws. They assert no private-seed trace or draw-reordering law.
-/

public section

universe v

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment

namespace SLHDSA.SHAKE128s.Examples.ContextObservation

/-- Fixed-context attachment retains the whole actual FIPS observation. -/
theorem context_observation {C : Type} [AddMonoid C]
    (policy : SigningView.Event (Game.World FIPS205.Answer) Message → C)
    (ctx : PureContext) (adv : StrongUnforgeableAdversary (Bridge.wireAlgorithm ctx)) :
    contextObservation ctx <$>
      SigningView.countedExperiment (contextPolicy ctx policy)
        (SigningView.ofTotal (Bridge.wireAlgorithm ctx)) adv.main =
      SigningView.countedExperiment policy (externalView FIPS205.scheme)
        (externalMain (Bridge.fixedContextAdversary ctx adv)) :=
  (countedExperiment_wire_eq_externalView policy ctx adv).symm

/-- An arbitrary handler, warm cache and continuation retain the same complete observation. -/
theorem context_continuation {C : Type} [AddMonoid C]
    (policy : SigningView.Event (Game.World FIPS205.Answer) Message → C)
    (ctx : PureContext) (adv : StrongUnforgeableAdversary (Bridge.wireAlgorithm ctx))
    {Cache β : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
    (handler : QueryImpl (Game.World FIPS205.Answer) (StateT Cache m)) (initial : Cache)
    (next : SigningView.Observation Message (List Byte) (Option (List Byte)) C × Cache → m β) :
    ((simulateQ handler (SigningView.countedExperiment (contextPolicy ctx policy)
      (SigningView.ofTotal (Bridge.wireAlgorithm ctx)) adv.main)).run initial >>=
        fun result => next (contextObservation ctx result.1, result.2)) =
      ((simulateQ handler (SigningView.countedExperiment policy (externalView FIPS205.scheme)
        (externalMain (Bridge.fixedContextAdversary ctx adv)))).run initial >>= next) :=
  countedExperiment_wire_run_bind_eq_externalView policy ctx adv handler initial next

/-- The actual full 30-byte answer equivalence pushes the uniform sampler forward. -/
theorem full30_sampler :
    Bridge.answerEquiv <$> ($ᵗ HashOutput : ProbComp HashOutput) =ᵈ
      ($ᵗ FIPS205.Answer : ProbComp FIPS205.Answer) :=
  Bridge.map_answerEquiv_uniformSample

/-- The original source policy pulls back pointwise along full-answer conversion. -/
theorem source_policy_square (event : SigningView.Event (Game.World HashOutput) Message) :
    sourcePolicy event = (sourcePolicy (Output := FIPS205.Answer))
      (SigningView.relabelEvent event) := by
  cases event with
  | ambient phase input => cases input <;> rfl
  | signingAttempt _ => rfl

/-- The same source-counted program retains its full public log and mapped warm cache jointly. -/
theorem full30_source {PK SK : Type}
    (scheme : Game.ExternalScheme HashOutput PK SK) (adv : Game.Adversary HashOutput PK)
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
        (SigningView.relabelMain byteAnswers (externalMain adv)))).run.run
          (QueryCache.mapAnswers (fun _ => Bridge.answerEquiv) cache) =ᵈ
      (fun output => ((output.1.1, QueryLog.mapAnswers (fun _ => Bridge.answerEquiv) output.1.2),
        QueryCache.mapAnswers (fun _ => Bridge.answerEquiv) output.2)) <$>
        (simulateQ HR (canonicalExperiment scheme adv)).run.run cache :=
  answerRepresentation_sourceJoint scheme adv cache

end SLHDSA.SHAKE128s.Examples.ContextObservation
