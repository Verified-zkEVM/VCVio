/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Game.Counted
public import HashSig.SLHDSA.SHAKE128s.Statement.BitSecurity

/-!
# The strong unforgeability game of a pure-mode signature over one hash oracle

Each pure-mode signing request contains a message and a context. All parties share one lazily
sampled random oracle with answers of type `Output`. The adversary receives the public key and
can query the hash and signing oracles. It wins when its forgery verifies and the signer has
never returned that signature for that request.

The game records each signing attempt and attributes each hash query to key generation, the
signer, the adversary or final verification. For every positive budget `q`, `HasSecurityBits`
bounds the winning probability by `q / 2 ^ bits` when the signing lifetime and the sum of the
counts selected by `Z` each satisfy their respective bounds with probability one.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s

/-- Lifetime allowance of `2 ^ 64` signing attempts per key, including rejected requests. -/
@[expose] def signingLimit : Nat := 2 ^ 64

namespace Game

variable {Output PK SK : Type}

/-- The supplied-key client and final verifier, with the full raw log and phase counters. -/
@[expose] noncomputable def afterKeygen (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) (keys : SK × PK) :
    OracleComp (World Output) Outcome :=
  Counted.legacyOutcome <$> Counted.canonicalAfterKeygen scheme adversary keys

/-- One source-counted execution retains the complete outcome and source-count observation. -/
@[expose] noncomputable def experimentBySource (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) :
    OracleComp (World Output) (Outcome × Unforgeability.QueryCounts) :=
  Counted.legacyObservation <$> Counted.canonicalExperiment scheme adversary

variable [SampleableType Output]

/-- All parties share one random oracle, starting empty. -/
@[expose] noncomputable def runBySource (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) :
    ProbComp (Outcome × Unforgeability.QueryCounts) :=
  RandomOracleModel.run (experimentBySource scheme adversary)

/-- The strong unforgeability game of `scheme`: the winning bit and the counts by source. -/
@[expose] noncomputable def securityGame (scheme : ExternalScheme Output PK SK) :
    SecurityGame Unit Unforgeability.QueryKind where
  Adversary := Adversary Output PK
  experiment := fun _ adversary =>
    (fun result => (decide (Wins result.1), result.2)) <$> runBySource scheme adversary

/-- At most `2 ^ 64` signing requests, with probability one. -/
@[expose] def WithinSigningLimit (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) : Prop :=
  Pr{let result ← (securityGame scheme).experiment () adversary}[result.2 .sign ≤ signingLimit] = 1

/-- `bits` bits of security in counting mode `Z`, for adversaries within the signing limit. -/
@[expose] def HasSecurityBits (scheme : ExternalScheme Output PK SK)
    (Z : Finset Unforgeability.QueryKind) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary : Adversary Output PK, WithinSigningLimit scheme adversary →
    (securityGame scheme).HasQueryBound () Z adversary q →
    (securityGame scheme).advantage () adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-- Source counters for the joint work budget. Each signing attempt, direct adversary hash
query and final-verifier hash query costs one. Rejections, cache hits and hashes performed on
losing runs count. Key-generation and signer hash queries have zero weight. -/
@[expose] def adversaryWork : Finset Unforgeability.QueryKind := {.sign, .hash, .verifier}

end Game

end SLHDSA.SHAKE128s
