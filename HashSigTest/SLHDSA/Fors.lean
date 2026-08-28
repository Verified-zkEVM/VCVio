/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Fors

/-!
# Oracle-parametric FORS canaries

These examples pin the FIPS 205 FORS query schedule: trees are traversed in increasing order,
authentication paths evaluate sibling subtrees only, signing does not hash the selected leaf,
root compression happens after all roots, and recovery performs `F`, the authentication-path
climb, then the final `T_k` compression.
-/

public section

namespace SLHDSA.ForsTest

open OracleComp

variable {p : Params} (prims : Primitives p)

/-- FIPS 205 Algorithm 15: a leaf is exactly one addressed `F` query. -/
example (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    forsLeafM prims.core sk pk adrs t =
      (PublicHash.f prims.core pk (forsNodeAdrs adrs 0 t)
        (forsSkGenCore prims.core sk pk adrs t) :
        OracleComp (publicHashSpec prims.core) prims.Y) := rfl

/-- FIPS 205 Algorithm 15: root construction delegates to the oracle-agnostic Merkle traversal. -/
example (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (i : ℕ) :
    forsRootM prims.core sk pk adrs i =
      (PerfectMerkleTree.merkleRootM
        (forsLeafWith prims.core (PublicHash.f prims.core pk) sk pk adrs)
        (forsNodeHashWith (PublicHash.h prims.core pk) adrs) p.a i :
        OracleComp (publicHashSpec prims.core) prims.Y) := rfl

/-- Public-key generation computes roots in increasing `Fin k` order and compresses only after
the complete root vector is available. -/
example (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    forsPkGenM prims.core sk pk adrs = (do
      let roots ← Vector.ofFnM fun i : Fin p.k =>
        forsRootM prims.core sk pk adrs i.val
      PublicHash.tl prims.core pk (forsPkAdrs adrs) roots.toList :
      OracleComp (publicHashSpec prims.core) prims.Y) := rfl

/-- Signing processes trees in increasing order. For each selected leaf it evaluates only the
sibling-only authentication path and returns the raw secret; there is no selected-leaf `F` call. -/
example (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    forsSignM prims.core md sk pk adrs =
      (Vector.ofFnM fun i : Fin p.k => do
        let idx := i.val * 2 ^ p.a + forsIdx p md i.val
        let path ← PerfectMerkleTree.authPathM
          (forsLeafWith prims.core (PublicHash.f prims.core pk) sk pk adrs)
          (forsNodeHashWith (PublicHash.h prims.core pk) adrs) idx p.a
        return (forsSkGenCore prims.core sk pk adrs idx, path) :
        OracleComp (publicHashSpec prims.core) (ForsSigCore p prims.core)) := rfl

/-- Recovery performs one `F`, then a leaf-to-root climb, per tree in increasing order, followed
by the final `T_k` compression. -/
example (sig : ForsSigCore p prims.core) (md : List Byte) (pk : prims.PkSeed) (adrs : Adrs) :
    forsPkFromSigM prims.core sig md pk adrs = (do
      let roots ← Vector.ofFnM fun i : Fin p.k => do
        let idx := i.val * 2 ^ p.a + forsIdx p md i.val
        let leaf ← PublicHash.f prims.core pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).1
        PerfectMerkleTree.climbM
          (forsNodeHashWith (PublicHash.h prims.core pk) adrs) idx leaf (sig[i.val]).2
      PublicHash.tl prims.core pk (forsPkAdrs adrs) roots.toList :
      OracleComp (publicHashSpec prims.core) prims.Y) := rfl

/-- The sibling-only signing budget excludes the selected leaf and its direct ancestor chain. -/
example (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (forsSignM prims.core md sk pk adrs :
        OracleComp (publicHashSpec prims.core) (ForsSigCore p prims.core))
      (p.k * ((2 ^ p.a - 1) + (2 ^ p.a - p.a - 1))) :=
  forsSignM_isTotalQueryBound prims.core md sk pk adrs

/-- Public-key generation uses one complete-tree budget per FORS tree and one final compression. -/
example (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (forsPkGenM prims.core sk pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y)
      (p.k * (2 ^ p.a + (2 ^ p.a - 1)) + 1) :=
  forsPkGenM_isTotalQueryBound prims.core sk pk adrs

/-- The height-zero edge case normalizes to no signing queries: the secret is returned directly
and there is no sibling subtree. -/
example (ha : p.a = 0) (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) :
    IsTotalQueryBound
      (forsSignM prims.core md sk pk adrs :
        OracleComp (publicHashSpec prims.core) (ForsSigCore p prims.core)) 0 := by
  simpa [ha] using forsSignM_isTotalQueryBound prims.core md sk pk adrs

/-- At height zero, key generation makes one leaf query per tree and one final compression. -/
example (ha : p.a = 0) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (forsPkGenM prims.core sk pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y) (p.k + 1) := by
  simpa [ha] using forsPkGenM_isTotalQueryBound prims.core sk pk adrs

/-- A FIPS-shaped signature makes one `F` and `a` climb queries per tree, then `T_k`. -/
example (sig : ForsSigCore p prims.core) (md : List Byte) (pk : prims.PkSeed) (adrs : Adrs)
    (hlen : ∀ i : Fin p.k, (sig[i.val]).2.length = p.a) :
    IsTotalQueryBound
      (forsPkFromSigM prims.core sig md pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y)
      (p.k * (p.a + 1) + 1) :=
  forsPkFromSigM_isTotalQueryBound_fips prims.core sig md pk adrs hlen

/-- Honest pure signatures satisfy the FIPS-shaped recovery schedule without an extra premise. -/
example (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (forsPkFromSigM prims.core (forsSign prims md sk pk adrs) md pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y)
      (p.k * (p.a + 1) + 1) :=
  forsPkFromSigM_isTotalQueryBound_fips prims.core (forsSign prims md sk pk adrs) md pk adrs
    (fun i => forsSign_authPath_length prims md sk pk adrs i)

/-- Query-preserving handlers commute with canonical FORS signing. -/
example {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec prims.core) m]
    (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := m)).toMonadHom
        (forsSignM prims.core md sk pk adrs :
          OracleComp (publicHashSpec prims.core) (ForsSigCore p prims.core)) =
      (forsSignM prims.core md sk pk adrs : m (ForsSigCore p prims.core)) := by
  exact forsSignM_natural prims.core _ md sk pk adrs

/-- An arbitrary fixed answer table interprets the canonical program as the induced pure API. -/
example (answer : QueryImpl (publicHashSpec prims.core) Id)
    (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (forsSignM prims.core md sk pk adrs :
          OracleComp (publicHashSpec prims.core) (ForsSigCore p prims.core)) =
      forsSign (PublicHash.withPublicHash prims.core answer) md sk pk adrs :=
  simulateQ_forsSignM_withPublicHash prims.core answer md sk pk adrs

/-- A fixed answer table gives extensional FORS completeness through the canonical programs. -/
example (answer : QueryImpl (publicHashSpec prims.core) Id)
    (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer (do
      let sig ← forsSignM prims.core md sk pk adrs
      forsPkFromSigM prims.core sig md pk adrs) =
    simulateQ answer (forsPkGenM prims.core sk pk adrs) :=
  simulateQ_forsPkFromSigM_forsSignM_withPublicHash prims.core answer md sk pk adrs

/-- The pre-oracle pure secret-generation helper remains source-compatible. -/
example (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    forsSkGen prims sk pk adrs t = prims.PRF pk sk (forsSkAdrs adrs t) := rfl

end SLHDSA.ForsTest
