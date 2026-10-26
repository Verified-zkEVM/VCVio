/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.Game

/-!
# Counted experiment and probability-one resource equations

The equations retain signing rejection as a returned reply, all source coordinates, actual
verification work and one shared random-oracle execution. Structural caps are a separate API.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal
open SLHDSA.SHAKE128s

namespace SLHDSA.Refactor.Semantics

/-- Every hash call costs one, including hits; private sampling is free. -/
theorem hashSelectorEquation {Output : Type} (input : (Game.World Output).Domain) :
    Game.hashCost input = match input with
      | .inl _ => 0
      | .inr _ => 1 := by
  cases input <;> rfl

/-- Every request costs one signing call and appends its exact optional reply. -/
theorem countedSigningEquation {Output PK SK : Type}
    (scheme : Game.ExternalScheme Output PK SK) (sk : SK) (request : Message) :
    Game.signingOracle scheme sk request = (do
      AddWriterT.addTell (Game.Counts.single .signing 1)
      let answer ← liftM (scheme.sign sk request : OracleComp (Game.World Output) (Option Bytes))
      liftM (modify (fun signed => signed ++ [⟨request, answer⟩]) :
        StateT Game.SigningLog (OracleComp (Game.World Output)) Unit)
      return answer) := rfl

/-- Actual verification follows the adversary phase and contributes its own source coordinate. -/
theorem countedAfterKeygenEquation {Output PK SK : Type}
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK)
    (keys : SK × PK) :
    Game.afterKeygen scheme adversary keys = (do
      let (sk, pk) := keys
      let ((forgery, adversaryCounts), signed) ←
        (simulateQ
          ((QueryImpl.ofLift (Game.World Output)
              (StateT Game.SigningLog (OracleComp (Game.World Output)))).withAddCost
              (fun input => Game.Counts.single .hash (Game.hashCost input)) +
            Game.signingOracle scheme sk)
          (adversary.main pk)).run.run []
      let (verified, verifierCounts) ← Game.countQueries
        (fun input => Game.Counts.single .verification (Game.hashCost input))
        (scheme.verify pk forgery.message forgery.signature)
      return {
        forgery := forgery
        signed := signed
        verified := verified
        counts := Multiplicative.toAdd adversaryCounts + verifierCounts }) := rfl

/-- Rejected replies cannot make a concrete forged pair stale. -/
theorem countedFreshnessEquation (signed : Game.SigningLog) (forgery : Game.Forgery) :
    Game.Fresh signed forgery ↔
      ¬∃ entry ∈ signed, entry.1 = forgery.message ∧ entry.2 = some forgery.signature := Iff.rfl

/-- Winning requires both actual acceptance and exact returned-pair freshness. -/
theorem countedWinningEquation (outcome : Game.Outcome) :
    Game.Wins outcome ↔ outcome.verified = true ∧
      ¬∃ entry ∈ outcome.signed,
        entry.1 = outcome.forgery.message ∧ entry.2 = some outcome.forgery.signature := Iff.rfl

/-- The five source coordinates retain the signer subtraction and actual verifier count. -/
theorem countedSourcesEquation (outcome : Game.Outcome) (keygenHashes laterHashes : Nat) :
    Game.sourceCounts outcome keygenHashes laterHashes = fun kind => match kind with
      | .sign => outcome.counts .signing
      | .hash => outcome.counts .hash
      | .keygen => keygenHashes
      | .signer => laterHashes - outcome.counts .hash - outcome.counts .verification
      | .verifier => outcome.counts .verification := rfl

/-- Both key generation and the later phase belong to one outer oracle program. -/
theorem countedExperimentEquation {Output PK SK : Type}
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK) :
    Game.experimentBySource scheme adversary = (do
      let (keys, keygenHashes) ← Game.countAllHashes scheme.keygen
      let (outcome, laterHashes) ← Game.countAllHashes (Game.afterKeygen scheme adversary keys)
      return (outcome, Game.sourceCounts outcome keygenHashes laterHashes)) := rfl

/-- One initially empty random-oracle cache is shared across the complete experiment. -/
theorem countedRandomOracleEquation {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK) :
    Game.runBySource scheme adversary =
      (simulateQ (RandomOracleModel.impl Bytes Output)
        (Game.experimentBySource scheme adversary)).run' ∅ := rfl

/-- The public security game retains the winning bit and every source count. -/
theorem countedSecurityGameEquation {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK) :
    (Game.securityGame scheme).experiment () adversary =
      (fun result => (decide (Game.Wins result.1), result.2)) <$>
        Game.runBySource scheme adversary := rfl

/-- A query budget is a probability-one joint event under the actual experiment distribution. -/
theorem probabilityOneBudgetEquation {Scheme Kind : Type}
    (game : SecurityGame Scheme Kind) (scheme : Scheme) (selected : Finset Kind)
    (adversary : game.Adversary) (budget : Nat) :
    game.HasQueryBound scheme selected adversary budget ↔
      Pr{let result ← game.experiment scheme adversary}[
        ∑ kind ∈ selected, result.2 kind ≤ budget] = 1 := Iff.rfl

/-- The per-key signing limit is exactly two to the sixty-fourth power. -/
theorem signingLimitEquation : signingLimit = 2 ^ 64 := rfl

/-- The lifetime event uses the actual signing-request count with probability one. -/
theorem lifetimeEquation {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK) :
    Game.WithinSigningLimit scheme adversary ↔
      Pr{let result ← (Game.securityGame scheme).experiment () adversary}[
        result.2 .sign ≤ 2 ^ 64] = 1 := Iff.rfl

/-- Bit security quantifies every positive joint budget and every lifetime-bounded adversary. -/
theorem bitSecurityEquation {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (selected : Finset Unforgeability.QueryKind)
    (bits : Nat) :
    Game.HasSecurityBits scheme selected bits ↔
      ∀ budget : Nat, 1 ≤ budget → ∀ adversary : Game.Adversary Output PK,
        Game.WithinSigningLimit scheme adversary →
        (Game.securityGame scheme).HasQueryBound () selected adversary budget →
        (Game.securityGame scheme).advantage () adversary ≤
          budget / ((2 ^ bits : Nat) : ℝ≥0∞) := Iff.rfl

/-- Selected actual work includes signing attempts, direct hashes and verifier hashes. -/
theorem selectedWorkEquation :
    Game.adversaryWork = ({.sign, .hash, .verifier} : Finset Unforgeability.QueryKind) := rfl

/-- The phase hash-work coordinate excludes signing attempts. -/
theorem hashWorkEquation (counts : Game.Counts) :
    counts.work = counts .hash + counts .verification := rfl

end SLHDSA.Refactor.Semantics
