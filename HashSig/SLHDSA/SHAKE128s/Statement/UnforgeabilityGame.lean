/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import VCVio.OracleComp.ProbComp

/-!
# Query kinds of the unforgeability game

The kinds of hash and signing queries an unforgeability experiment counts, and a count per kind.
A counting mode selects which kinds are the adversary's work.
-/

public section

namespace SLHDSA.SHAKE128s.Unforgeability

/-- The kinds of queries counted by the experiment. -/
inductive QueryKind where
  /-- `q_S`: the adversary's signing queries. -/
  | sign
  /-- `q_H`: the hash queries the adversary makes directly. -/
  | hash
  /-- `q_Gen`: the hash queries of key generation. -/
  | keygen
  /-- `q_Sign`: the hash queries of the signer, summed over all signing queries. -/
  | signer
  /-- `q_Verify`: the hash queries of the verification of the forgery. -/
  | verifier
deriving DecidableEq, Repr

/-- A count per kind of query. -/
abbrev QueryCounts := QueryKind → ℕ

/-- `n` queries of kind `kind`, and none of the other kinds. -/
@[expose] def QueryCounts.single (kind : QueryKind) (n : ℕ) : QueryCounts := Pi.single kind n

end SLHDSA.SHAKE128s.Unforgeability
