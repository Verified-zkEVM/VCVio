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

A signature scheme in pure mode signs requests made of a message and a context, and produces
byte-string signatures; every party shares one lazily sampled random oracle on byte strings,
whose answers have type `Output` (`ExternalScheme`).

The adversary gets the public key, the random oracle and a signing oracle, and outputs a forgery.
It wins if the forgery verifies and the signing oracle never returned that message and signature
(`Wins`). Every hash call is counted by its source: the adversary's own, key generation's, the
signer's and the final verification's; signing requests are counted too (`securityGame`).
`HasSecurityBits Z bits` says that every adversary within `2 ^ 64` signing requests and with at
most `q ≥ 1` counted queries of the kinds in `Z` wins with probability at most `q / 2 ^ bits`.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s

/-- At most `2 ^ 64` signatures per key. -/
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

/-- The adversary's work is the sum of:
- its signing requests (+1 per request, at most `2^64`),
- its hash calls (+1 per call it makes to the random oracle),
- the hash calls of verifying its forgery (+1 per call). -/
@[expose] def adversaryWork : Finset Unforgeability.QueryKind := {.sign, .hash, .verifier}

end Game

end SLHDSA.SHAKE128s
