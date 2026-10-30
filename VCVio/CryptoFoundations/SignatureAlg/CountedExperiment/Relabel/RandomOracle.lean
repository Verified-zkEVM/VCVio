/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.Relabel
public import VCVio.OracleComp.QueryTracking.RandomOracle.AnswerRelabel

/-!
# Joint counted observations under public-answer representation transport

The complete counted program equality is interpreted with the existing logged random oracle.
The same joint tuple retains the candidate, raw replies, verifier result, ordered cost, public
query-answer log and arbitrary final warm cache. Private uniform queries remain stateless.
-/

public section

open OracleComp OracleSpec SignatureAlg SignatureAlg.SigningView
open OracleComp.RandomOracleAnswerRelabel

namespace SignatureAlg.SigningView

/-- Explicit public sampler transport and the actual policy square preserve the full joint law. -/
theorem countedExperiment_world_transport {ι : Type} [DecidableEq ι]
    {R S : OracleSpec ι} [∀ input, SampleableType (R input)]
    [∀ input, SampleableType (S input)] {Request PK SK Sig Reply C : Type} [AddMonoid C]
    (e : ∀ input, R input ≃ S input)
    (he : ∀ input,
      e input <$> ($ᵗ R input : ProbComp (R input)) =ᵈ
        ($ᵗ S input : ProbComp (S input)))
    (policyR : Event (unifSpec + R) Request → C)
    (policyS : Event (unifSpec + S) Request → C)
    (view : SigningView (OracleComp (unifSpec + R)) Request PK SK Sig Reply)
    (main : PK → OracleComp ((unifSpec + R) + (Request →ₒ Reply)) (Request × Sig))
    (diagram : ∀ event, policyR event = policyS (relabelEvent event)) (cache : R.QueryCache) :
    let HR := (unifFwdImpl R).liftTarget
        (WriterT (QueryLog R) (StateT R.QueryCache ProbComp)) + R.randomOracle.withLogging
    let HS := (unifFwdImpl S).liftTarget
        (WriterT (QueryLog S) (StateT S.QueryCache ProbComp)) + S.randomOracle.withLogging
    (simulateQ HS
        (countedExperiment policyS (relabelView (worldAnswers e) view)
          (relabelMain (worldAnswers e) main))).run.run
          (QueryCache.mapAnswers (fun input => e input) cache) =ᵈ
      (fun output => ((output.1.1, QueryLog.mapAnswers e output.1.2),
        QueryCache.mapAnswers (fun input => e input) output.2)) <$>
        (simulateQ HR (countedExperiment policyR view main)).run.run cache := by
  have h := evalDist_logged_world_run e he (countedExperiment policyR view main) cache
  rw [countedExperiment_relabel (worldAnswers e) policyR policyS view main diagram] at h
  exact h

end SignatureAlg.SigningView
