/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Security

/-!
# The forgery experiment and its counted views

The definitions the security proof works with: `Security.experiment`, the whole SUF-CMA
experiment (key generation, the adversary's phase with its signing oracle, and verification of
the forgery) as one oracle computation; its random-oracle runs `Security.run` and
`Security.runAll`, the latter with the total hash count; and the views of the scheme used by the
charges, namely the count `Checksum.chainVerificationCalls` of chain steps in Algorithm 8 and
the parse `MessageDigest.parse` of a message digest into a FORS instance and its indices.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity

/-- Number of calls to `F` in Algorithm 8, before the final WOTS public-key compression. -/
def Checksum.chainVerificationCalls (digits : MessageDigits) : Nat :=
  (∑ i, (w - 1 - (digits i).val)) +
    ∑ i : Fin checksumDigits, (w - 1 - (Checksum.checksumDigit (Checksum.checksum digits) i).val)

namespace MessageDigest

/-- A FORS instance, identified by its 63-bit hypertree tree-and-leaf index. -/
abbrev Instance := Fin (2 ^ totalHeight)
/-- What a message digest selects: a FORS instance and a leaf index in each of its trees. -/
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

/-- The experiment run against a lazily sampled random oracle. -/
noncomputable def run (adversary : Adversary) : ProbComp Outcome :=
  RandomOracleModel.run (experiment adversary)

/-- The experiment with its total hash count. -/
noncomputable def runAll (adversary : Adversary) : ProbComp (Outcome × Nat) :=
  RandomOracleModel.run (countAllHashes (experiment adversary))

/-- The probability that the adversary wins the experiment, read off `runAll`. -/
noncomputable def totalAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← runAll adversary}[Wins result.1]

end Security

end SlhDsaSecurity
