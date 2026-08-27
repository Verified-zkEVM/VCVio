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
deterministic interpretation, and structural query bounds. They exercise the canonical owner
implementation in `Xmss.lean` directly.
-/

public section

namespace SLHDSA.XmssTest

open OracleComp

variable {p : Params} (prims : Primitives p)

example : xmssNodeQueryBound p 1 =
    (p.len * (p.w - 1) + 1) + (p.len * (p.w - 1) + 1) + 1 := rfl

example : xmssAuthPathQueryBound p 2 =
    xmssNodeQueryBound p 0 + xmssNodeQueryBound p 1 := by
  simp [xmssAuthPathQueryBound]

example : wotsLeafAdrs ((Adrs.zero.setLayerAddress 7).setTreeAddress 9) 3 =
    { layer := 7, tree := 9, type := 0, word1 := 3, word2 := 0, word3 := 0 } := rfl

example : xmssNodeAdrs ((Adrs.zero.setLayerAddress 7).setTreeAddress 9) 4 6 =
    { layer := 7, tree := 9, type := 2, word1 := 0, word2 := 4, word3 := 6 } := rfl

/-- Height zero is exactly the addressed WOTS+ leaf, with no tree-node query. -/
example (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    (xmssNodeM prims sk pk adrs 0 t : OracleComp (publicHashSpec prims) prims.Y) =
      xmssLeafM prims sk pk adrs t := rfl

/-- Height one evaluates the left leaf, then the right leaf, then hashes the ordered pair at the
parent's `TREE` address. -/
example (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    (xmssNodeM prims sk pk adrs 1 t : OracleComp (publicHashSpec prims) prims.Y) = (do
      let left ← xmssLeafM prims sk pk adrs (2 * t)
      let right ← xmssLeafM prims sk pk adrs (2 * t + 1)
      xmssNodeHashM prims pk adrs 1 t left right) := rfl

/-- The ordered children and exact encoded `TREE` address are part of the single public-hash
query identity. -/
example (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) (left right : prims.Y) :
    (xmssNodeHashM prims pk adrs z t left right :
      OracleComp (publicHashSpec prims) prims.Y) =
    query (spec := publicHashSpec prims)
      (.thash pk (prims.adrsToKey (xmssNodeAdrs adrs z t)) [left, right]) := rfl

/-- FIPS 205 Algorithm 10 computes the sibling-only authentication path before the WOTS+
signature. -/
example (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    (xmssSignM prims msg sk pk adrs idx :
      OracleComp (publicHashSpec prims) (XmssSig p prims)) = (do
      let path ← PerfectMerkleTree.authPathM (xmssLeafM prims sk pk adrs)
        (xmssNodeHashM prims pk adrs) idx p.hp
      let sig ← wotsSignM prims msg sk pk (wotsLeafAdrs adrs idx)
      return (sig, path)) := rfl

/-- Recovery computes the WOTS+ leaf before climbing the leaf-first authentication path. -/
example (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    (xmssPkFromSigM prims idx sig msg pk adrs :
      OracleComp (publicHashSpec prims) prims.Y) = (do
      let leaf ← wotsPkFromSigM prims sig.1 msg pk (wotsLeafAdrs adrs idx)
      PerfectMerkleTree.climbM (xmssNodeHashM prims pk adrs) idx leaf sig.2) := rfl

example (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) :
    simulateQ (PublicHash.impl prims)
        (xmssNodeM prims sk pk adrs z t : OracleComp (publicHashSpec prims) prims.Y) =
      xmssNode prims sk pk adrs z t := by
  exact simulateQ_xmssNodeM prims sk pk adrs z t

/-- Every deterministic total answer table interprets the same XMSS signing owner program. -/
example (answer : QueryImpl (publicHashSpec prims) Id)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    simulateQ answer
        (xmssSignM prims msg sk pk adrs idx :
          OracleComp (publicHashSpec prims) (XmssSig p prims)) =
      xmssSign (PublicHash.withPublicHash prims answer) msg sk pk adrs idx :=
  simulateQ_xmssSignM_withPublicHash prims answer msg sk pk adrs idx

/-- The explicit leaf program is natural under the canonical query interpreter. -/
example {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec prims) m]
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims) (m := m)).toMonadHom
        (xmssLeafM prims sk pk adrs t :
          OracleComp (publicHashSpec prims) prims.Y) =
      (xmssLeafM prims sk pk adrs t : m prims.Y) := by
  exact xmssLeafM_natural prims _ sk pk adrs t

/-- One addressed node-hash query is natural under the canonical query interpreter. -/
example {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec prims) m]
    (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) (left right : prims.Y) :
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims) (m := m)).toMonadHom
        (xmssNodeHashM prims pk adrs z t left right :
          OracleComp (publicHashSpec prims) prims.Y) =
      (xmssNodeHashM prims pk adrs z t left right : m prims.Y) := by
  exact xmssNodeHashM_natural prims _ pk adrs z t left right

example (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (xmssPkFromSigM prims idx sig msg pk adrs :
        OracleComp (publicHashSpec prims) prims.Y)
      ((∑ i : Fin p.len, (p.w - 1 - chainSteps prims msg i.val)) + 1 + sig.2.length) :=
  xmssPkFromSigM_isTotalQueryBound prims idx sig msg pk adrs

example (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    IsTotalQueryBound ((do
      let sig ← xmssSignM prims msg sk pk adrs idx
      xmssPkFromSigM prims idx sig msg pk adrs) :
        OracleComp (publicHashSpec prims) prims.Y)
      ((p.len * (p.w - 1) + 1) + xmssAuthPathQueryBound p p.hp + p.hp) :=
  xmssSignM_then_xmssPkFromSigM_isTotalQueryBound prims msg sk pk adrs idx

end SLHDSA.XmssTest
