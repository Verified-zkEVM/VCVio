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

The `simulateQ_*_withPublicHash` lemmas interpret the entire layer through an arbitrary fixed
answer function and recover the legacy pure WOTS+ construction for the induced primitive bundle.
Canonical `PublicHash.impl` corollaries recover the original executable specification.
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

private theorem simulateQ_indices_mapM {ι α : Type} {spec : OracleSpec ι} (len : ℕ)
    (f : QueryImpl spec Id) (g : Fin len → OracleComp spec α) :
    simulateQ f ((indices len).mapM g) = Vector.ofFn fun i => simulateQ f (g i) := by
  have mapM_id (xs : List (Fin len)) :
      xs.mapM (fun i => simulateQ f (g i)) = xs.map (fun i => simulateQ f (g i)) := by
    change xs.mapM (fun i => (pure (simulateQ f (g i)) : Id α)) = _
    simp only [List.mapM_pure]
    exact Id.pure_run _
  apply Vector.toArray_inj.mp
  calc
    _ = simulateQ f (Vector.toArray <$> (indices len).mapM g) :=
      (simulateQ_map f ((indices len).mapM g) Vector.toArray).symm
    _ = _ := by
      rw [Vector.toArray_mapM, Array.mapM_eq_mapM_toList, simulateQ_map,
        simulateQ_list_mapM]
      rw [mapM_id]
      simp only [indices, Vector.toArray_ofFn, Array.toList_ofFn, List.map_ofFn,
        Function.comp_id]
      apply Id.ext
      rw [Id.run_map]
      change (List.ofFn fun i => simulateQ f (g i)).toArray =
        Array.ofFn fun i => simulateQ f (g i)
      exact List.toArray_ofFn

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

/-- Interpreting the explicit WOTS+ chain by any total deterministic answer function is the pure
chain for the functional primitive bundle induced by that answer function. -/
@[simp]
theorem simulateQ_chainM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) (i s : ℕ) :
    simulateQ answer
        (chainM prims pkSeed adrs x i s : OracleComp (publicHashSpec prims) prims.Y) =
      chain (PublicHash.withPublicHash prims answer) pkSeed adrs x i s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      simp only [chainM, simulateQ_bind, PublicHash.f, simulateQ_HasQuery_query, chain]
      rw [ih]
      rfl

/-- The canonical deterministic interpretation of the explicit WOTS+ chain is the legacy pure
chain. -/
@[simp]
theorem simulateQ_chainM (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) (i s : ℕ) :
    simulateQ (PublicHash.impl prims)
        (chainM prims pkSeed adrs x i s : OracleComp (publicHashSpec prims) prims.Y) =
      chain prims pkSeed adrs x i s := by
  convert
    simulateQ_chainM_withPublicHash prims (PublicHash.impl prims) pkSeed adrs x i s using 1
  all_goals rfl

/-- Replacing only the public hashes leaves WOTS+ message digit derivation unchanged. -/
@[simp]
theorem chainSteps_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (msg : prims.Y) (i : ℕ) :
    chainSteps (PublicHash.withPublicHash prims answer) msg i = chainSteps prims msg i := rfl

/-- Any deterministic public-hash answer function makes oracle WOTS+ key-generation tops agree
with the legacy pure construction for its induced functional primitive bundle. -/
@[simp]
theorem simulateQ_wotsPkGenTopsM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) :
    simulateQ answer
        (wotsPkGenTopsM prims sk pk adrs :
          OracleComp (publicHashSpec prims) (Vector prims.Y p.len)) =
      wotsPkGenTops (PublicHash.withPublicHash prims answer) sk pk adrs := by
  simp only [wotsPkGenTopsM, simulateQ_indices_mapM, wotsPkGenTops,
    simulateQ_chainM_withPublicHash]

/-- Canonical deterministic-handler parity for WOTS+ key-generation tops. -/
@[simp]
theorem simulateQ_wotsPkGenTopsM (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkGenTopsM prims sk pk adrs :
          OracleComp (publicHashSpec prims) (Vector prims.Y p.len)) =
      wotsPkGenTops prims sk pk adrs := by
  convert
    simulateQ_wotsPkGenTopsM_withPublicHash prims (PublicHash.impl prims) sk pk adrs using 1
  all_goals rfl

/-- Any deterministic public-hash answer function makes oracle WOTS+ public-key generation agree
with the legacy pure construction for its induced functional primitive bundle. -/
@[simp]
theorem simulateQ_wotsPkGenM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) :
    simulateQ answer
        (wotsPkGenM prims sk pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      wotsPkGen (PublicHash.withPublicHash prims answer) sk pk adrs := by
  simp only [wotsPkGenM, simulateQ_bind, simulateQ_wotsPkGenTopsM_withPublicHash,
    PublicHash.tl, simulateQ_HasQuery_query, wotsPkGen]
  apply Id.ext
  rfl

/-- Canonical deterministic-handler parity for WOTS+ public-key generation. -/
@[simp]
theorem simulateQ_wotsPkGenM (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkGenM prims sk pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      wotsPkGen prims sk pk adrs := by
  convert simulateQ_wotsPkGenM_withPublicHash prims (PublicHash.impl prims) sk pk adrs using 1
  all_goals rfl

/-- Any deterministic public-hash answer function makes oracle WOTS+ signing agree with the
legacy pure construction for its induced functional primitive bundle. -/
@[simp]
theorem simulateQ_wotsSignM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (wotsSignM prims msg sk pk adrs : OracleComp (publicHashSpec prims) (WotsSig p prims)) =
      wotsSign (PublicHash.withPublicHash prims answer) msg sk pk adrs := by
  simp only [wotsSignM, simulateQ_indices_mapM, wotsSign,
    simulateQ_chainM_withPublicHash, chainSteps_withPublicHash]

/-- Canonical deterministic-handler parity for WOTS+ signing. -/
@[simp]
theorem simulateQ_wotsSignM (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsSignM prims msg sk pk adrs : OracleComp (publicHashSpec prims) (WotsSig p prims)) =
      wotsSign prims msg sk pk adrs := by
  convert
    simulateQ_wotsSignM_withPublicHash prims (PublicHash.impl prims) msg sk pk adrs using 1
  all_goals rfl

/-- Any deterministic public-hash answer function makes oracle WOTS+ signature-recovery tops
agree with the legacy pure construction for its induced functional primitive bundle. -/
@[simp]
theorem simulateQ_wotsPkFromSigTopsM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sig : WotsSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (wotsPkFromSigTopsM prims sig msg pk adrs :
          OracleComp (publicHashSpec prims) (Vector prims.Y p.len)) =
      wotsPkFromSigTops (PublicHash.withPublicHash prims answer) sig msg pk adrs := by
  simp only [wotsPkFromSigTopsM, simulateQ_indices_mapM, wotsPkFromSigTops,
    simulateQ_chainM_withPublicHash, chainSteps_withPublicHash]

/-- Canonical deterministic-handler parity for WOTS+ signature-recovery tops. -/
@[simp]
theorem simulateQ_wotsPkFromSigTopsM (prims : Primitives p) (sig : WotsSig p prims)
    (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkFromSigTopsM prims sig msg pk adrs :
          OracleComp (publicHashSpec prims) (Vector prims.Y p.len)) =
      wotsPkFromSigTops prims sig msg pk adrs := by
  convert
    simulateQ_wotsPkFromSigTopsM_withPublicHash prims (PublicHash.impl prims) sig msg pk adrs
      using 1
  all_goals rfl

/-- Any deterministic public-hash answer function makes oracle WOTS+ public-key recovery agree
with the legacy pure construction for its induced functional primitive bundle. -/
@[simp]
theorem simulateQ_wotsPkFromSigM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sig : WotsSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (wotsPkFromSigM prims sig msg pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      wotsPkFromSig (PublicHash.withPublicHash prims answer) sig msg pk adrs := by
  simp only [wotsPkFromSigM, simulateQ_bind, simulateQ_wotsPkFromSigTopsM_withPublicHash,
    PublicHash.tl, simulateQ_HasQuery_query, wotsPkFromSig]
  apply Id.ext
  rfl

/-- Canonical deterministic-handler parity for WOTS+ public-key recovery. -/
@[simp]
theorem simulateQ_wotsPkFromSigM (prims : Primitives p) (sig : WotsSig p prims)
    (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkFromSigM prims sig msg pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      wotsPkFromSig prims sig msg pk adrs := by
  convert
    simulateQ_wotsPkFromSigM_withPublicHash prims (PublicHash.impl prims) sig msg pk adrs using 1
  all_goals rfl

/-- Functional WOTS+ completeness for every fixed deterministic public-hash answer function. -/
theorem simulateQ_wotsPkFromSigM_wotsSignM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer (do
      let sig ← wotsSignM prims msg sk pk adrs
      wotsPkFromSigM prims sig msg pk adrs) =
    simulateQ answer (wotsPkGenM prims sk pk adrs) := by
  simp only [simulateQ_bind, simulateQ_wotsSignM_withPublicHash,
    simulateQ_wotsPkFromSigM_withPublicHash, simulateQ_wotsPkGenM_withPublicHash]
  exact wotsPkFromSig_wotsSign (PublicHash.withPublicHash prims answer) msg sk pk adrs

end WotsOracle

end SLHDSA
