/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Oracle
public import HashSig.SLHDSA.Wots

/-!
# Oracle-parametric WOTS+

This module is the explicit-oracle counterpart of `HashSig.SLHDSA.Wots`.  Secret-value
derivation remains the keyed `PRF` operation from `Primitives`, while every public `F` and `T_l`
evaluation is issued through `PublicHash`.  The functions are monad-parametric and therefore do
not choose or reset an oracle cache; a caller that wants random-oracle semantics must run the
whole surrounding computation with one `PublicHash.randomOracle` state.

`simulateQ_chainM` is the first executable bridge: the canonical oracle syntax interpreted by the
deterministic handler is exactly the existing pure hash chain.
-/

@[expose] public section

open OracleComp

namespace SLHDSA

variable {p : Params}

namespace WotsOracle

/-- Apply `F` for `s` WOTS+ chain steps, issuing one explicit query per successor step. -/
def chainM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y)
    (i : ℕ) : ℕ → m prims.Y
  | 0 => pure x
  | s + 1 => do
      let y ← chainM prims pkSeed adrs x i s
      PublicHash.f prims pkSeed (adrs.setHashAddress (i + s)) y

/-- The canonical vector of WOTS+ chain indices. -/
def indices (len : ℕ) : Vector (Fin len) len :=
  Vector.ofFn id

/-- Generate every WOTS+ chain top with explicit public-hash calls. -/
def wotsPkGenTopsM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    m (Vector prims.Y p.len) :=
  (indices p.len).mapM fun i =>
    chainM prims pk (wotsChainAdrs adrs i.val) (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0
      (p.w - 1)

/-- WOTS+ public-key generation with explicit `F` and `T_l` queries. -/
def wotsPkGenM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    m prims.Y := do
  let tops ← wotsPkGenTopsM prims sk pk adrs
  PublicHash.tl prims pk (wotsPkAdrs adrs) tops.toList

/-- WOTS+ signing with explicit `F` queries. -/
def wotsSignM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : m (WotsSig p prims) :=
  (indices p.len).mapM fun i =>
    chainM prims pk (wotsChainAdrs adrs i.val) (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0
      (chainSteps prims msg i.val)

/-- Complete every WOTS+ chain from a signature to its top using explicit `F` queries. -/
def wotsPkFromSigTopsM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (sig : WotsSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : m (Vector prims.Y p.len) :=
  (indices p.len).mapM fun i =>
    chainM prims pk (wotsChainAdrs adrs i.val) sig[i.val] (chainSteps prims msg i.val)
      (p.w - 1 - chainSteps prims msg i.val)

/-- Recover a WOTS+ public key from a signature with explicit `F` and `T_l` queries. -/
def wotsPkFromSigM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (sig : WotsSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : m prims.Y := do
  let tops ← wotsPkFromSigTopsM prims sig msg pk adrs
  PublicHash.tl prims pk (wotsPkAdrs adrs) tops.toList

/-- Deterministic interpretation of the explicit WOTS+ chain is the existing pure chain. -/
@[simp]
theorem simulateQ_chainM (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) (i s : ℕ) :
    simulateQ (PublicHash.impl prims)
        (chainM prims pkSeed adrs x i s : OracleComp (publicHashSpec prims) prims.Y) =
      chain prims pkSeed adrs x i s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      simp only [chainM, simulateQ_bind, PublicHash.simulateQ_f, chain]
      rw [ih]
      rfl

end WotsOracle

end SLHDSA
