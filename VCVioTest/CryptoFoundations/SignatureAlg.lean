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

@[expose] public section

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
def replayAdv : SignatureAlg.strongUnforgeableAdv twoSignatureAlg where
  main _ := do
    let σ ← (unifSpec + (Bool →ₒ ToySignature)).query (Sum.inr false)
    return (false, σ)

/-- Query a signature, then flip its ignored rerandomization bit. -/
def rerandomizeAdv : SignatureAlg.strongUnforgeableAdv twoSignatureAlg where
  main _ := do
    let _ ← (unifSpec + (Bool →ₒ ToySignature)).query (Sum.inr false)
    return (false, (false, true))

/-- Forge directly on a fresh message without calling the signing oracle. -/
def freshMessageAdv : SignatureAlg.strongUnforgeableAdv twoSignatureAlg where
  main _ := pure (true, (true, true))

/-- Replaying an exact signing-oracle response loses SUF-CMA. -/
example :
    SignatureAlg.strongUnforgeableExp ProbCompRuntime.probComp replayAdv = pure false := by
  simp [SignatureAlg.strongUnforgeableExp, replayAdv, twoSignatureAlg,
    SignatureAlg.signingOracle, SignatureAlg.signingLogContains,
    ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

/-- A different valid signature on an already queried message is an eligible strong forgery. -/
example :
    SignatureAlg.strongUnforgeableExp ProbCompRuntime.probComp rerandomizeAdv = pure true := by
  simp [SignatureAlg.strongUnforgeableExp, rerandomizeAdv, twoSignatureAlg,
    SignatureAlg.signingOracle, SignatureAlg.signingLogContains,
    ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

/-- A valid signature on a fresh message wins exactly as in the ordinary unforgeability game. -/
example :
    SignatureAlg.strongUnforgeableExp ProbCompRuntime.probComp freshMessageAdv = pure true := by
  simp [SignatureAlg.strongUnforgeableExp, freshMessageAdv, twoSignatureAlg,
    SignatureAlg.signingOracle, SignatureAlg.signingLogContains,
    ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

/-- The ENNReal advantage endpoint assigns zero to replay and one to the two valid fresh-pair
forgeries in this deterministic scheme. -/
example : replayAdv.advantage ProbCompRuntime.probComp = 0 ∧
    rerandomizeAdv.advantage ProbCompRuntime.probComp = 1 ∧
    freshMessageAdv.advantage ProbCompRuntime.probComp = 1 := by
  simp [SignatureAlg.strongUnforgeableAdv.advantage,
    SignatureAlg.strongUnforgeableExp, replayAdv, rerandomizeAdv, freshMessageAdv,
    twoSignatureAlg, SignatureAlg.signingOracle, SignatureAlg.signingLogContains,
    ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

end SignatureAlgTest
