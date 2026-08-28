/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Wots

/-!
# Oracle-parametric WOTS+ canaries

These producer-side examples pin the number, order, and addresses of public-hash queries in WOTS+
chains and top-level operations. They also exercise naturality, deterministic interpretation, and
the structural query-bound API of the canonical owner implementation in `Wots.lean`.
-/

public section

namespace SLHDSA.WotsTest

open OracleComp

variable {p : Params} (prims : Primitives p)

example (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y) (i : ℕ) :
    chainM prims.core pkSeed adrs x i 0 =
      (pure x : OracleComp (publicHashSpec prims.core) prims.Y) := rfl

example (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y) (i : ℕ) :
    chainM prims.core pkSeed adrs x i 2 =
      (do
        let y ← PublicHash.f prims.core pkSeed (adrs.setHashAddress i) x
        PublicHash.f prims.core pkSeed (adrs.setHashAddress (i + 1)) y :
        OracleComp (publicHashSpec prims.core) prims.Y) := by
  simp [chainM, chainWith]

example (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y) (i s : ℕ) :
    simulateQ (PublicHash.impl prims)
        (chainM prims.core pkSeed adrs x i s :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      chain prims pkSeed adrs x i s := by
  exact simulateQ_chainM prims pkSeed adrs x i s

example (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkGenM prims.core sk pk adrs = (do
      let tops ← wotsPkGenTopsM prims.core sk pk adrs
      PublicHash.tl prims.core pk (wotsPkAdrs adrs) tops.toList :
      OracleComp (publicHashSpec prims.core) prims.Y) := rfl

example (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    wotsSignM prims.core msg sk pk adrs =
      (Vector.ofFnM fun i : Fin p.len =>
        chainM prims.core pk (wotsChainAdrs adrs i.val)
          (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (chainSteps prims.core msg i.val) :
        OracleComp (publicHashSpec prims.core) (WotsSig p prims.core)) := rfl

example (sig : WotsSig p prims.core) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkFromSigM prims.core sig msg pk adrs = (do
      let tops ← Vector.ofFnM fun i : Fin p.len =>
        chainM prims.core pk (wotsChainAdrs adrs i.val) sig[i.val]
          (chainSteps prims.core msg i.val) (p.w - 1 - chainSteps prims.core msg i.val)
      PublicHash.tl prims.core pk (wotsPkAdrs adrs) tops.toList :
      OracleComp (publicHashSpec prims.core) prims.Y) := rfl

example {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec prims.core) m]
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := m)).toMonadHom
        (wotsSignM prims.core msg sk pk adrs :
          OracleComp (publicHashSpec prims.core) (WotsSig p prims.core)) =
      (wotsSignM prims.core msg sk pk adrs : m (WotsSig p prims.core)) := by
  exact wotsSignM_natural prims.core _ msg sk pk adrs

example (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y) (i s : ℕ) :
    IsTotalQueryBound
      (chainM prims.core pkSeed adrs x i s :
        OracleComp (publicHashSpec prims.core) prims.Y) s :=
  chainM_isTotalQueryBound prims.core pkSeed adrs x i s

example (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (wotsPkGenM prims.core sk pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y)
      (p.len * (p.w - 1) + 1) :=
  wotsPkGenM_isTotalQueryBound prims.core sk pk adrs

example (sig : WotsSig p prims.core) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (wotsPkFromSigM prims.core sig msg pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y)
      ((∑ i : Fin p.len, (p.w - 1 - chainSteps prims.core msg i.val)) + 1) :=
  wotsPkFromSigM_isTotalQueryBound prims.core sig msg pk adrs

example (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound ((do
      let sig ← wotsSignM prims.core msg sk pk adrs
      wotsPkFromSigM prims.core sig msg pk adrs) :
        OracleComp (publicHashSpec prims.core) prims.Y)
      (p.len * (p.w - 1) + 1) :=
  wotsSignM_then_wotsPkFromSigM_isTotalQueryBound prims.core msg sk pk adrs

end SLHDSA.WotsTest
