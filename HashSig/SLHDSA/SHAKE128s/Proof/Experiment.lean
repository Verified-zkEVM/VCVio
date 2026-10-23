/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Security

/-!
# Definitions the proof works with

The whole experiment in one computation, its total hash count, and two views of the scheme
used by the charges.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity

/-- Number of calls to `F` in Algorithm 8, before the final WOTS public-key compression. -/
def Checksum.chainVerificationCalls (digits : MessageDigits) : Nat :=
  (∑ i, (w - 1 - (digits i).val)) +
    ∑ i : Fin checksumDigits, (w - 1 - (Checksum.checksumDigit (Checksum.checksum digits) i).val)

namespace MessageDigest

abbrev Instance := Fin (2 ^ totalHeight)
abbrev View := Instance × (ForsTree → ForsLeaf)

/-- The 63-bit FORS-instance index and the FORS indices. -/
def parse (output : HashOutput) : View :=
  ((treeIndex output ++ leafIndex output).toFin, forsIndices output)

end MessageDigest

namespace Security

export Game (Counts.work)

/-- Key generation, then the adversary's phase and verification. -/
noncomputable def experiment (adversary : Adversary) : OracleComp OracleWorld Outcome := do
  let (sk, pk) ← Scheme.keygen
  let ((forgery, adversaryCounts), signed) ←
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
          (fun input => Counts.single .hash (hashCost input)) + signingOracle sk)
      (adversary.main pk)).run.run []
  let (verified, verifierCounts) ← countQueries
    (fun input => Counts.single .verification (hashCost input))
    (Scheme.verify pk forgery.message forgery.signature)
  return {
    forgery := forgery
    signed := signed
    verified := verified
    counts := Multiplicative.toAdd adversaryCounts + verifierCounts }

noncomputable def run (adversary : Adversary) : ProbComp Outcome :=
  Xmss.RandomOracleModel.run (experiment adversary)

/-- The experiment with its total hash count. -/
noncomputable def runAll (adversary : Adversary) : ProbComp (Outcome × Nat) :=
  Xmss.RandomOracleModel.run (countAllHashes (experiment adversary))

noncomputable def totalAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← runAll adversary}[Wins result.1]

end Security

end SlhDsaSecurity
