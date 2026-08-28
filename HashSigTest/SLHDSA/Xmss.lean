/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Xmss

/-!
# Oracle-parametric XMSS canaries

These producer-side examples pin XMSS address formation, left-to-right subtree evaluation,
FIPS authentication-path-before-WOTS signing, recovery-before-climb verification, naturality,
deterministic interpretation, and structural query bounds. They exercise the canonical `xmss*M`
programs in `Xmss.lean` directly.
-/

public section

namespace SLHDSA.XmssTest

open OracleComp

variable {p : Params} (core : CorePrimitives p)

example : xmssNodeQueryBound p 1 =
    2 ^ 1 * (p.len * (p.w - 1) + 1) + (2 ^ 1 - 1) * 1 := rfl

example : xmssAuthPathQueryBound p 2 =
    (2 ^ 2 - 1) * (p.len * (p.w - 1) + 1) + (2 ^ 2 - 2 - 1) * 1 := rfl

example : wotsLeafAdrs ((Adrs.zero.setLayerAddress 7).setTreeAddress 9) 3 =
    { layer := 7, tree := 9, type := 0, word1 := 3, word2 := 0, word3 := 0 } := rfl

example : xmssNodeAdrs ((Adrs.zero.setLayerAddress 7).setTreeAddress 9) 4 6 =
    { layer := 7, tree := 9, type := 2, word1 := 0, word2 := 4, word3 := 6 } := rfl

/-- Height zero is exactly the addressed WOTS+ leaf, with no tree-node query. -/
example (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) :
    (xmssNodeM core sk pk adrs 0 t : OracleComp (publicHashSpec core) core.Y) =
      xmssLeafM core sk pk adrs t := rfl

/-- Height one evaluates the left leaf, then the right leaf, then hashes the ordered pair at the
parent's `TREE` address. -/
example (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) :
    (xmssNodeM core sk pk adrs 1 t : OracleComp (publicHashSpec core) core.Y) = (do
      let left ← xmssLeafM core sk pk adrs (2 * t)
      let right ← xmssLeafM core sk pk adrs (2 * t + 1)
      xmssNodeHashM core pk adrs 1 t left right) := rfl

/-- The ordered children and exact encoded `TREE` address are part of the single public-hash
query identity. -/
example (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) (left right : core.Y) :
    (xmssNodeHashM core pk adrs z t left right :
      OracleComp (publicHashSpec core) core.Y) =
    query (spec := publicHashSpec core)
      (.thash pk (core.adrsToKey (xmssNodeAdrs adrs z t)) [left, right]) := rfl

/-- FIPS 205 Algorithm 10 computes the sibling-only authentication path before the WOTS+
signature. -/
example (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    (xmssSignM core msg sk pk adrs idx :
      OracleComp (publicHashSpec core) (XmssSig p core)) = (do
      let path ← PerfectMerkleTree.authPathM (xmssLeafM core sk pk adrs)
        (xmssNodeHashM core pk adrs) idx p.hp
      let sig ← wotsSignM core msg sk pk (wotsLeafAdrs adrs idx)
      return (sig, path)) := rfl

/-- Recovery computes the WOTS+ leaf before climbing the leaf-first authentication path. -/
example (idx : ℕ) (sig : XmssSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) :
    (xmssPkFromSigM core idx sig msg pk adrs :
      OracleComp (publicHashSpec core) core.Y) = (do
      let leaf ← wotsPkFromSigM core sig.1 msg pk (wotsLeafAdrs adrs idx)
      PerfectMerkleTree.climbM (xmssNodeHashM core pk adrs) idx leaf sig.2) := rfl

example (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (z t : ℕ) :
    simulateQ (PublicHash.impl prims)
        (xmssNodeM prims.core sk pk adrs z t :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      xmssNode prims sk pk adrs z t := by
  exact simulateQ_xmssNodeM prims sk pk adrs z t

/-- The legacy pure signing API keeps its source-level signature type and is literally the
canonical `xmssSignM` program under the concrete public-hash interpreter. -/
example (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    simulateQ (PublicHash.impl prims)
        (xmssSignM prims.core msg sk pk adrs idx :
          OracleComp (publicHashSpec prims.core) (XmssSig p prims)) =
      (xmssSign prims msg sk pk adrs idx : XmssSig p prims) := rfl

/-- Every deterministic total answer table interprets the same canonical `xmssSignM` program. -/
example (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    simulateQ answer
        (xmssSignM core msg sk pk adrs idx :
          OracleComp (publicHashSpec core) (XmssSig p core)) =
      xmssSign (PublicHash.withPublicHash core answer) msg sk pk adrs idx :=
  simulateQ_xmssSignM_withPublicHash core answer msg sk pk adrs idx

/-- One fixed total public-hash table gives end-to-end XMSS completeness through the canonical
signing, recovery, and root programs. -/
example (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp) :
    simulateQ answer (do
      let sig ← xmssSignM core msg sk pk adrs idx
      xmssPkFromSigM core idx sig msg pk adrs) =
    simulateQ answer (xmssRootM core sk pk adrs) :=
  simulateQ_xmssPkFromSigM_xmssSignM_withPublicHash core answer
    msg sk pk adrs idx hidx

/-- The explicit leaf program is natural under the canonical query interpreter. -/
example {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) :
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec core) (m := m)).toMonadHom
        (xmssLeafM core sk pk adrs t :
          OracleComp (publicHashSpec core) core.Y) =
      (xmssLeafM core sk pk adrs t : m core.Y) := by
  exact xmssLeafM_natural core _ sk pk adrs t

/-- One addressed node-hash query is natural under the canonical query interpreter. -/
example {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m]
    (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) (left right : core.Y) :
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec core) (m := m)).toMonadHom
        (xmssNodeHashM core pk adrs z t left right :
          OracleComp (publicHashSpec core) core.Y) =
      (xmssNodeHashM core pk adrs z t left right : m core.Y) := by
  exact xmssNodeHashM_natural core _ pk adrs z t left right

example (idx : ℕ) (sig : XmssSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (xmssPkFromSigM core idx sig msg pk adrs :
        OracleComp (publicHashSpec core) core.Y)
      ((∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) + 1 + sig.2.length) :=
  xmssPkFromSigM_isTotalQueryBound core idx sig msg pk adrs

example (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    IsTotalQueryBound ((do
      let sig ← xmssSignM core msg sk pk adrs idx
      xmssPkFromSigM core idx sig msg pk adrs) :
        OracleComp (publicHashSpec core) core.Y)
      ((p.len * (p.w - 1) + 1) + xmssAuthPathQueryBound p p.hp + p.hp) :=
  xmssSignM_then_xmssPkFromSigM_isTotalQueryBound core msg sk pk adrs idx

end SLHDSA.XmssTest
