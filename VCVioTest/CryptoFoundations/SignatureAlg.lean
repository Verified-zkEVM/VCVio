/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.SignatureAlg

/-!
# Signature security-game canaries

Executable symbolic canaries for the generic SUF-CMA endpoint. The toy scheme deliberately has
two valid signatures for each message, while honest signing returns only one of them. This makes
the distinction between message freshness and exact returned-pair freshness observable.
-/

public section

open OracleComp OracleSpec

namespace SignatureAlgTest

/-- The toy signature records the message in its first bit and has an ignored rerandomization
bit. Both values of the second bit verify. -/
abbrev ToySignature := Bool × Bool

/-- A deterministic scheme with two valid signatures per message. Honest signing uses
rerandomization bit `false`. -/
def twoSignatureAlg : SignatureAlg ProbComp Bool Unit Unit ToySignature where
  keygen := pure ((), ())
  sign _ _ msg := pure (msg, false)
  verify _ msg σ := pure (σ.1 == msg)

/-- Query one signature and replay the exact pair. -/
def replayAdv : SignatureAlg.StrongUnforgeableAdversary twoSignatureAlg where
  main _ := do
    let σ ← (unifSpec + (Bool →ₒ ToySignature)).query (Sum.inr false)
    return (false, σ)

/-- Query a signature, then flip its ignored rerandomization bit. -/
def rerandomizeAdv : SignatureAlg.StrongUnforgeableAdversary twoSignatureAlg where
  main _ := do
    let _ ← (unifSpec + (Bool →ₒ ToySignature)).query (Sum.inr false)
    return (false, (false, true))

/-- Forge directly on a fresh message without calling the signing oracle. -/
def freshMessageAdv : SignatureAlg.StrongUnforgeableAdversary twoSignatureAlg where
  main _ := pure (true, (true, true))

/-- Return a fresh-message pair whose signature encodes the wrong message. -/
def invalidFreshMessageAdv : SignatureAlg.StrongUnforgeableAdversary twoSignatureAlg where
  main _ := pure (true, (false, true))

/-- Query one message, then return a fresh pair for that message whose signature encodes the
other message. This reaches the same-message branch but must still fail verification. -/
def invalidSameMessageAdv : SignatureAlg.StrongUnforgeableAdversary twoSignatureAlg where
  main _ := do
    let _ ← (unifSpec + (Bool →ₒ ToySignature)).query (Sum.inr false)
    return (false, (true, true))

/-- Replaying an exact signing-oracle response loses SUF-CMA. -/
example :
    𝒟[SignatureAlg.strongUnforgeableExperiment replayAdv] {true} = 0 := by
  simp [SignatureAlg.strongUnforgeableExperiment,
    replayAdv, twoSignatureAlg,
    SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle, SignatureAlg.signingLogContains]

/-- A different valid signature on an already queried message is an eligible strong forgery. -/
example :
    𝒟[SignatureAlg.strongUnforgeableExperiment rerandomizeAdv] {true} = 1 := by
  simp [SignatureAlg.strongUnforgeableExperiment,
    rerandomizeAdv, twoSignatureAlg,
    SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle, SignatureAlg.signingLogContains]

/-- A valid signature on a fresh message wins exactly as in the ordinary unforgeability game. -/
example :
    𝒟[SignatureAlg.strongUnforgeableExperiment freshMessageAdv] {true} = 1 := by
  simp [SignatureAlg.strongUnforgeableExperiment,
    freshMessageAdv, twoSignatureAlg,
    SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle, SignatureAlg.signingLogContains]

/-- The ENNReal advantage endpoint assigns zero to replay and one to the two valid fresh-pair
forgeries in this deterministic scheme. -/
example : SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp replayAdv = 0 ∧
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp rerandomizeAdv = 1 ∧
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp freshMessageAdv = 1 := by
  simp [SignatureAlg.strongUnforgeableAdvantage,
    SignatureAlg.strongUnforgeableExperiment,
    replayAdv, rerandomizeAdv, freshMessageAdv,
    twoSignatureAlg, SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle,
    SignatureAlg.signingLogContains,
    ProbCompRuntime.probComp_evalDist]

/-- Exact-pair freshness alone is insufficient: an invalid fresh-message signature loses. -/
example :
    𝒟[SignatureAlg.strongUnforgeableExperiment
        invalidFreshMessageAdv] {true} = 0 := by
  simp [SignatureAlg.strongUnforgeableExperiment,
    invalidFreshMessageAdv, twoSignatureAlg,
    SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle, SignatureAlg.signingLogContains]

/-- Exact replay is excluded from the same-message residual as well as from SUF itself. This
pins exact-pair freshness independently in the residual experiment and its advantage endpoint. -/
example :
    𝒟[SignatureAlg.sameMessageStrongUnforgeableExperiment replayAdv] {true} = 0 ∧
      SignatureAlg.sameMessageStrongUnforgeableAdvantage ProbCompRuntime.probComp
        replayAdv = 0 := by
  simp [SignatureAlg.sameMessageStrongUnforgeableAdvantage,
    SignatureAlg.sameMessageStrongUnforgeableExperiment, replayAdv, twoSignatureAlg,
    SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle, SignatureAlg.signingLogContains,
    ProbCompRuntime.probComp_evalDist]

/-- The same-message residual requires verification: a new but invalid pair has probability
zero even after the message was submitted to the signing oracle. -/
example :
    𝒟[SignatureAlg.sameMessageStrongUnforgeableExperiment
        invalidSameMessageAdv] {true} = 0 := by
  simp [SignatureAlg.sameMessageStrongUnforgeableExperiment,
    invalidSameMessageAdv, twoSignatureAlg,
    SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle, SignatureAlg.signingLogContains]

/-- The SUF partition is exact on the two qualitatively different forgery branches: rerandomizing
an already signed message contributes only to the same-message term, while a fresh-message
forgery contributes only to EUF. -/
example :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        rerandomizeAdv.toUnforgeableAdversary = 0 ∧
      SignatureAlg.sameMessageStrongUnforgeableAdvantage ProbCompRuntime.probComp
        rerandomizeAdv = 1 ∧
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        freshMessageAdv.toUnforgeableAdversary = 1 ∧
      SignatureAlg.sameMessageStrongUnforgeableAdvantage ProbCompRuntime.probComp
        freshMessageAdv = 0 := by
  simp [SignatureAlg.unforgeableAdvantage, SignatureAlg.unforgeableExperiment,
    SignatureAlg.sameMessageStrongUnforgeableAdvantage,
    SignatureAlg.sameMessageStrongUnforgeableExperiment,
    SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary,
    rerandomizeAdv, freshMessageAdv, twoSignatureAlg, SignatureAlg.runWithSigningOracle,
    SignatureAlg.signingOracle,
    SignatureAlg.signingLogContains, QueryLog.wasQueried,
    ProbCompRuntime.probComp_evalDist]

/-- Direct executable-runtime consumer of the public exact SUF partition. -/
example (adv : SignatureAlg.StrongUnforgeableAdversary twoSignatureAlg) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp adv =
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp adv.toUnforgeableAdversary +
        SignatureAlg.sameMessageStrongUnforgeableAdvantage ProbCompRuntime.probComp adv :=
  SignatureAlg.strongUnforgeableAdvantage_eq_euf_add_sameMessage ProbCompRuntime.probComp adv

/-- The toy scheme satisfies the vacuous unit upper bound for the same-message residual. -/
private lemma twoSignatureBinding :
    twoSignatureAlg.SameMessageBinding ProbCompRuntime.probComp 1 := by
  intro adv
  unfold SignatureAlg.sameMessageStrongUnforgeableAdvantage
    SignatureAlg.sameMessageStrongUnforgeableExperiment
  exact MeasureTheory.measure_le_one _ _

/-- Direct consumer of the quantitative `SameMessageBinding` packaging. -/
example (adv : SignatureAlg.StrongUnforgeableAdversary twoSignatureAlg) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp adv ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp adv.toUnforgeableAdversary + 1 :=
  SignatureAlg.strongUnforgeableAdvantage_le_euf_add_of_sameMessageBinding
    ProbCompRuntime.probComp twoSignatureBinding adv

end SignatureAlgTest
