/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Wots

/-!
# Oracle-parametric WOTS+ canaries

These examples cover the distinct observable schedules in the canonical WOTS+ programs: adjacent
chain addresses, per-coordinate signing chains, and recovery followed by `T_ℓ` compression.
-/

public section

namespace SLHDSA.WotsTest

open OracleComp

variable {p : Params} (prims : Primitives p)

example (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y) (i : ℕ) :
    chainM prims.core pkSeed adrs x i 2 =
      (do
        let y ← PublicHash.f prims.core pkSeed (adrs.setHashAddress i) x
        PublicHash.f prims.core pkSeed (adrs.setHashAddress (i + 1)) y :
        OracleComp (publicHashSpec prims.core) prims.Y) := by
  simp [chainM, chainWith]

example (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    wotsSignM prims.core msg sk pk adrs =
      (Vector.ofFnM fun i : Fin p.len =>
        chainM prims.core pk (wotsChainAdrs adrs i.val)
          (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (chainStepsCore prims.core msg i.val) :
        OracleComp (publicHashSpec prims.core) (WotsSig p prims.core)) := rfl

example (sig : WotsSig p prims.core) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkFromSigM prims.core sig msg pk adrs = (do
      let tops ← Vector.ofFnM fun i : Fin p.len =>
        chainM prims.core pk (wotsChainAdrs adrs i.val) sig[i.val]
          (chainStepsCore prims.core msg i.val)
          (p.w - 1 - chainStepsCore prims.core msg i.val)
      PublicHash.tl prims.core pk (wotsPkAdrs adrs) tops.toList :
      OracleComp (publicHashSpec prims.core) prims.Y) := rfl

end SLHDSA.WotsTest
