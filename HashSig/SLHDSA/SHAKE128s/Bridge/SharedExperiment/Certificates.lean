/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Joint
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Component
public import HashSig.SLHDSA.SHAKE128s.Statement.FIPS205
public import HashSig.SLHDSA.SHAKE128s.Bridge.PaperGame
public import HashSig.SLHDSA.SHAKE128s.Statement.Theorems.StrongUnforgeability
import HashSig.SLHDSA.SHAKE128s.Statement.Game.CompleteBudget
import HashSig.SLHDSA.SHAKE128s.Statement.Theorems.SmallBudget
import HashSig.SLHDSA.SHAKE128s.Proof.VerificationBudget

/-!
# Security and verifier-cost certificates of the shared observation

Joint-work security bounds apply to the shared winning-bit and source observation.
Cached verifier runs retain their exact cost interval, and accepted outcomes retain their
verification-work lower bound.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

private theorem advantage_eq {Output PK SK : Type} [SampleableType Output]
    (scheme : Game.ExternalScheme Output PK SK) (adversary : Game.Adversary Output PK) :
    (observedGame scheme).advantage () adversary =
      (Game.securityGame scheme).advantage () adversary := by
  simp only [SecurityGame.advantage, jointExperiment]

/-- The shared FIPS observation retains the piecewise joint-work bound at every budget. -/
theorem advantage_le_jointWorkBound (q : Nat)
    (adversary : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (hlimit : Pr{let result ←
      (observedGame FIPS205.scheme).experiment () adversary}[result.2 .sign ≤ 2 ^ 64] = 1)
    (hbound : (observedGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adversary q) :
    (observedGame FIPS205.scheme).advantage () adversary ≤
      jointWorkBound q := by
  rw [advantage_eq]
  apply slhDsa_sufCma_le adversary q
  · simpa only [jointExperiment, Game.WithinSigningLimit, signingLimit] using hlimit
  · simpa only [SecurityGame.HasQueryBound, jointExperiment] using hbound

/-- A positive joint-work budget gives 127 bits within the signing lifetime. -/
theorem advantage_le_127 (q : Nat) (hq : 1 ≤ q)
    (adversary : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (hlimit : Pr{let result ←
      (observedGame FIPS205.scheme).experiment () adversary}[result.2 .sign ≤ 2 ^ 64] = 1)
    (hbound : (observedGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adversary q) :
    (observedGame FIPS205.scheme).advantage () adversary ≤
      q / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have _ := hq
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (advantage_le_jointWorkBound q adversary hlimit hbound).trans (jointWorkBound_le q)

/-- An almost-sure joint-work cap below 569 gives zero winning probability in the model. -/
theorem advantage_eq_zero_model (adversary : Game.Adversary HashOutput PublicKey)
    (q : Nat) (hq : q < 569)
    (hbound : (observedGame Bridge.model).HasQueryBound () Game.adversaryWork adversary q) :
    (observedGame Bridge.model).advantage () adversary = 0 := by
  rw [advantage_eq]
  apply VerificationBudget.advantage_eq_zero adversary q hq
  simpa only [SecurityGame.HasQueryBound, jointExperiment, Bridge.model] using hbound

/-- The scheme bridge gives zero FIPS forgery advantage below 569 joint calls. -/
theorem advantage_eq_zero_fips
    (adversary : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core))
    (q : Nat) (hq : q < 569)
    (hbound : (observedGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adversary q) :
    (observedGame FIPS205.scheme).advantage () adversary = 0 := by
  rw [advantage_eq]
  apply slhDsa_sufCma_eq_zero_of_lt_569 adversary q hq
  simpa only [SecurityGame.HasQueryBound, jointExperiment] using hbound

private theorem verification_projection (body : OracleComp (Game.World HashOutput) Bool) :
    Security.countQueries VerificationBudget.verificationCost body =
      (fun result => (result.1, phaseCounts result.2)) <$>
        (SigningView.costed sourcePolicy .verification body).runAdd := by
  change Game.countQueries (fun input => Game.Counts.single .verification
    (Game.hashCost input)) body = _
  rw [costed_eq_countAllHashes]
  have equality := congrArg (fun program => Prod.fst <$> program)
    (countAllHashes_countQueries_verification body)
  rw [Game.fst_map_countAllHashes] at equality
  rw [equality, Functor.map_map, Functor.map_map]
  congr 1
  funext result
  apply Prod.ext
  · rfl
  · funext kind
    cases kind <;> simp [Game.Counts.single, phaseCounts, sourceKind]

private theorem verifier_support (pk : PublicKey) (request : Message) (wire : SHAKE128s.Bytes)
    (cache : QueryCache HashSpec) (result : Bool × SourceCounts)
    (hresult : result ∈ support
      ((simulateQ (RandomOracleModel.impl SHAKE128s.Bytes HashOutput)
        ((SigningView.costed sourcePolicy .verification
          (Bridge.model.verify pk request wire)).runAdd)).run' cache)) :
    (result.1, phaseCounts result.2) ∈ support
      ((simulateQ (RandomOracleModel.impl SHAKE128s.Bytes HashOutput)
        (Security.countQueries VerificationBudget.verificationCost
          (Scheme.verify pk request wire))).run' cache) := by
  rw [verification_projection, simulateQ_map, StateT.run'_map', support_map]
  exact ⟨result, hresult, rfl⟩

/-- Framing and parsing bound verifier work between 569 and 3824 hashes. -/
theorem verification_count_bounds (pk : PublicKey) (request : Message)
    (wire message : Bytes) (signature : Signature)
    (hframe : request.frame = some message) (hparse : Signature.fromBytes? wire = some signature)
    (cache : QueryCache HashSpec) (result : Bool × SourceCounts)
    (hresult : result ∈ support ((simulateQ (RandomOracleModel.impl Bytes HashOutput)
      ((SigningView.costed sourcePolicy .verification
        (Bridge.model.verify pk request wire)).runAdd)).run' cache)) :
    569 ≤ result.2 .verifier ∧ result.2 .verifier ≤ 3824 := by
  exact VerificationBudget.verification_count_bounds pk request wire message signature
    hframe hparse cache (result.1, phaseCounts result.2)
    (verifier_support pk request wire cache result hresult)

/-- Acceptance alone suffices for the same interval without framing or parsing assumptions. -/
theorem verification_accepted_count_bounds (pk : PublicKey) (request : Message)
    (wire : Bytes) (cache : QueryCache HashSpec) (result : Bool × SourceCounts)
    (hresult : result ∈ support ((simulateQ (RandomOracleModel.impl Bytes HashOutput)
      ((SigningView.costed sourcePolicy .verification
        (Bridge.model.verify pk request wire)).runAdd)).run' cache))
    (haccept : result.1 = true) :
    569 ≤ result.2 .verifier ∧ result.2 .verifier ≤ 3824 := by
  exact VerificationBudget.verification_accepted_count_bounds pk request wire cache
    (result.1, phaseCounts result.2)
    (verifier_support pk request wire cache result hresult) haccept

/-- An accepted shared observation incurs at least 569 direct plus verification hashes. -/
theorem accepted_outcome_work (adversary : Game.Adversary HashOutput PublicKey)
    (observed : SigningView.Observation Message Bytes (Option Bytes) SourceCounts)
    (hsupport : observed ∈ support (RandomOracleModel.run
      (canonicalExperiment Bridge.model adversary))) (haccept : observed.verified = true) :
    569 ≤ observed.cost .hash + observed.cost .verifier := by
  exact VerificationBudget.accepted_observation_work adversary observed hsupport haccept

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
