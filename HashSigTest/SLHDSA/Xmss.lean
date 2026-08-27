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
WOTS-before-authentication-path signing, recovery-before-climb verification, and deterministic
handler parity. They exercise the canonical owner implementation in `Xmss.lean` directly.
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

/-- Signing computes the WOTS+ signature before evaluating the sibling-only authentication
path. -/
example (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    (xmssSignM prims msg sk pk adrs idx :
      OracleComp (publicHashSpec prims) (XmssSig p prims)) = (do
      let sig ← wotsSignM prims msg sk pk (wotsLeafAdrs adrs idx)
      let path ← PerfectMerkleTree.authPathM (xmssLeafM prims sk pk adrs)
        (xmssNodeHashM prims pk adrs) idx p.hp
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

end SLHDSA.XmssTest
