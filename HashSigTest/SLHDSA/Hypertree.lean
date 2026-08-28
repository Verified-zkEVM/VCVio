/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Hypertree

/-!
# Oracle-parametric hypertree canaries

These examples pin the `d = 1` hypertree as a transparent XMSS composition, including the
explicit recovery computation used by verification and fixed-answer completeness under one
shared public-hash implementation.
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

/-- Every deterministic total answer table interprets the same canonical program. -/
example (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    simulateQ answer
        (htSignM core msg sk pk adrs idxTree idxLeaf :
          OracleComp (publicHashSpec core) (HtSigCore p core)) =
      htSign (PublicHash.withPublicHash core answer) msg sk pk adrs idxTree idxLeaf :=
  simulateQ_htSignM_withPublicHash core answer msg sk pk adrs idxTree idxLeaf

/-- The thin hypertree layer inherits XMSS naturality without another traversal proof. -/
example {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec core) (m := m)).toMonadHom
        (htSignM core msg sk pk adrs idxTree idxLeaf :
          OracleComp (publicHashSpec core) (HtSigCore p core)) =
      (htSignM core msg sk pk adrs idxTree idxLeaf : m (HtSigCore p core)) := by
  exact htSignM_natural core _ msg sk pk adrs idxTree idxLeaf

/-- Naturality also covers the canonical verifier and its final pure comparison. -/
example {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
    (msg : core.Y) (sig : HtSigCore p core) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) (pkRoot : core.Y) :
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec core) (m := m)).toMonadHom
        (htVerifyM core msg sig pk adrs idxTree idxLeaf pkRoot :
          OracleComp (publicHashSpec core) Bool) =
      (htVerifyM core msg sig pk adrs idxTree idxLeaf pkRoot : m Bool) := by
  exact htVerifyM_natural core _ msg sig pk adrs idxTree idxLeaf pkRoot

/-- The `d = 1` hypertree signer reuses the XMSS structural bound verbatim. -/
example (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    IsTotalQueryBound
      (htSignM core msg sk pk adrs idxTree idxLeaf :
        OracleComp (publicHashSpec core) (HtSigCore p core))
      ((∑ i : Fin p.len, chainStepsCore core msg i.val) +
        xmssAuthPathQueryBound p p.hp) :=
  htSignM_isTotalQueryBound core msg sk pk adrs idxTree idxLeaf

/-- Signing, root generation, and verification share one answer function in the canonical
fixed-answer completeness theorem. -/
example (answer : QueryImpl (publicHashSpec core) Id) [DecidableEq core.Y]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) (hidx : idxLeaf < 2 ^ p.hp) :
    simulateQ answer (do
      let sig ← htSignM core msg sk pk adrs idxTree idxLeaf
      let root ← htRootM core sk pk adrs idxTree
      htVerifyM core msg sig pk adrs idxTree idxLeaf root) = true :=
  simulateQ_htVerifyM_htSignM_withPublicHash core answer msg sk pk adrs idxTree idxLeaf hidx

end SLHDSA.HypertreeTest
