/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Hypertree

/-!
# Oracle-parametric hypertree canaries

These examples cover the two observable contracts of the `d = 1` hypertree layer: signing is
transparent XMSS composition, and verification recovers a root before its final comparison.
-/

public section

namespace SLHDSA.HypertreeTest

open OracleComp

variable {p : Params} (core : CorePrimitives p)

/-- The canonical hypertree signer is exactly the addressed XMSS signer. -/
example (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    (htSignM core msg sk pk adrs idxTree idxLeaf :
      OracleComp (publicHashSpec core) (HtSigCore p core)) =
    xmssSignM core msg sk pk (htAdrs adrs idxTree) idxLeaf := by
  rfl

/-- Verification exposes recovery before the final pure comparison. -/
example [DecidableEq core.Y] (msg : core.Y) (sig : HtSigCore p core)
    (pk : core.PkSeed) (adrs : Adrs) (idxTree idxLeaf : ℕ) (pkRoot : core.Y) :
    (htVerifyM core msg sig pk adrs idxTree idxLeaf pkRoot :
      OracleComp (publicHashSpec core) Bool) = (do
        let recovered ← htPkFromSigM core msg sig pk adrs idxTree idxLeaf
        return decide (recovered = pkRoot)) := by
  rfl

end SLHDSA.HypertreeTest
