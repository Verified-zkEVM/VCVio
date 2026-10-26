/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Observation

/-!
# Joint winning and source-count transport

The same complete counted program is interpreted once by the shared random oracle.
Raw optional replies determine the same fresh pair, and the five counters are retained jointly.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA.SHAKE128s

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment


open scoped Classical in
/-- Observe the shared counted program's winning bit and full original source vector. -/
@[expose] noncomputable def observedGame {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) : SecurityGame Unit Unforgeability.QueryKind where
  Adversary := Game.Adversary Output PK
  experiment := fun _ adversary =>
    (fun result => (decide (SigningView.Wins id result.toOutcome), result.cost)) <$>
      RandomOracleModel.run (canonicalExperiment scheme adversary)

private theorem reconstruct
    (observed : SigningView.Observation Message Bytes (Option Bytes) SourceCounts) :
    (legacyObservation observed).2 = observed.cost := by
  funext kind
  cases kind with
  | sign => rfl
  | hash => rfl
  | keygen => rfl
  | verifier => rfl
  | signer =>
      change observed.cost .hash + observed.cost .signer + observed.cost .verifier -
        observed.cost .hash - observed.cost .verifier = observed.cost .signer
      omega

private theorem winning
    (observed : SigningView.Observation Message Bytes (Option Bytes) SourceCounts) :
    Game.Wins (legacyObservation observed).1 ↔ SigningView.Wins id observed.toOutcome := by
  simp only [Game.Wins, SigningView.Wins, legacyObservation, legacyOutcome]
  exact and_congr Iff.rfl
    (SigningView.optional_fresh_iff observed.rawLog observed.forgery.1 observed.forgery.2).symm

private theorem run_map {Output α β : Type} [SampleableType Output]
    (f : α → β) (program : OracleComp (Game.World Output) α) :
    RandomOracleModel.run (f <$> program) = f <$> RandomOracleModel.run program := by
  simp only [RandomOracleModel.run, simulateQ_map, StateT.run'_map']

/-- Both games have exactly the same joint winning-bit and five-source program. -/
theorem jointExperiment {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK) :
    (observedGame scheme).experiment () adversary =
      (Game.securityGame scheme).experiment () adversary := by
  change _ = (fun result => (decide (Game.Wins result.1), result.2)) <$>
    RandomOracleModel.run (Game.experimentBySource scheme adversary)
  rw [fullProgram, run_map, Functor.map_map]
  apply congrArg (fun f => f <$> RandomOracleModel.run (canonicalExperiment scheme adversary))
  funext observed
  apply Prod.ext
  · exact decide_eq_decide.mpr (winning observed).symm
  · exact (reconstruct observed).symm

/-- Every selected actual joint budget is preserved at the same cap. -/
theorem jointBudget {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK)
    (selected : Finset Unforgeability.QueryKind) (q : Nat) :
    (observedGame scheme).HasQueryBound () selected adversary q ↔
      (Game.securityGame scheme).HasQueryBound () selected adversary q := by
  simp only [SecurityGame.HasQueryBound, jointExperiment]

/-- The original probability-one signing limit is unchanged. -/
theorem lifetime {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK) :
    (Pr{let result ← (observedGame scheme).experiment () adversary}[
      result.2 .sign ≤ 2 ^ 64] = 1) ↔ Game.WithinSigningLimit scheme adversary := by
  simp only [jointExperiment, Game.WithinSigningLimit, signingLimit]

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
