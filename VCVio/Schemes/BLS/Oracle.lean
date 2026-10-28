/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Basic
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-! # Indexed oracle executions for BLS

Shared hash and signing state for the Boneh–Lynn–Shacham signature game and its
index-guessing reduction. The cache records insertion indices, the signed-message list
records freshness, and a persistent flag records signing at the selected index.
-/

public section

open OracleComp OracleSpec

namespace BLS

/-- State of an indexed hash oracle, with passive freshness and selected-slot bookkeeping. -/
@[ext] structure OracleState (V M : Type) where
  /-- Cached values paired with their insertion indices. -/
  cache : (M →ₒ (V × ℕ)).QueryCache
  /-- Number of distinct messages inserted so far. -/
  count : ℕ
  /-- Messages submitted to the signing oracle. -/
  signed : List M
  /-- Value inserted at the selected slot, when that slot has been reached. -/
  selected : Option V
  /-- Whether the selected slot has been signed. -/
  bad : Bool

namespace OracleState

/-- Empty cache, with no hash or signing history. -/
@[expose] def empty {V M : Type} : OracleState V M := ⟨∅, 0, [], none, false⟩

/-- Insert one newly sampled value and record its insertion index. -/
@[expose] def insert {V M : Type} [DecidableEq M] (s : OracleState V M)
    (j : Option ℕ) (msg : M) (v : V) : OracleState V M :=
  { s with
    cache := s.cache.cacheQuery msg (v, s.count)
    count := s.count + 1
    selected := if j = some s.count then some v else s.selected }

/-- Record a signing request and raise the flag if its insertion index was selected. -/
@[expose] def recordSign {V M : Type} (s : OracleState V M)
    (j : Option ℕ) (msg : M) (idx : ℕ) : OracleState V M :=
  { s with signed := s.signed ++ [msg], bad := s.bad || decide (j = some idx) }

/-- Map cached and selected values, preserving indices, freshness history, and the flag. -/
@[expose] def map {V W M : Type} (f : V → W) (s : OracleState V M) : OracleState W M :=
  { cache := QueryCache.ofFn fun msg => (s.cache msg).map (Prod.map f id)
    count := s.count
    signed := s.signed
    selected := s.selected.map f
    bad := s.bad }

/-- Forget the selected-slot bookkeeping while retaining the indexed hash and signing history. -/
@[expose] def eraseSelection {V M : Type} (s : OracleState V M) : OracleState V M :=
  { s with selected := none, bad := false }

end OracleState

/-- Reuse a cached value or draw a new one at the current insertion index. -/
@[expose] def indexedEntry {V M : Type} [DecidableEq M] (draw : ℕ → ProbComp V)
    (j : Option ℕ) (msg : M) : StateT (OracleState V M) ProbComp (V × ℕ) :=
  fun s => match s.cache msg with
  | some z => pure (z, s)
  | none => (fun v => ((v, s.count), s.insert j msg v)) <$> draw s.count

/-- Hash and signing queries share one indexed cache. Public randomness is forwarded.
The signing response may depend on the stored value, but the signing history and flag
are recorded independently of that response. -/
@[expose] def indexedOracle {V M G : Type} [DecidableEq M] (draw : ℕ → ProbComp V)
    (hash sign : V → G) (j : Option ℕ) :
    QueryImpl ((unifSpec + (M →ₒ G)) + (M →ₒ G)) (StateT (OracleState V M) ProbComp) :=
  let unif : QueryImpl unifSpec (StateT (OracleState V M) ProbComp) :=
    fun t s => (fun v => (v, s)) <$> (unifSpec.query t : ProbComp _)
  let ro : QueryImpl (M →ₒ G) (StateT (OracleState V M) ProbComp) :=
    fun msg s => (fun z => (hash z.1.1, z.2)) <$> (indexedEntry draw j msg).run s
  let signer : QueryImpl (M →ₒ G) (StateT (OracleState V M) ProbComp) :=
    fun msg s => (fun z => (sign z.1.1, z.2.recordSign j msg z.1.2)) <$>
      (indexedEntry draw j msg).run s
  (unif + ro) + signer

/-- A public-randomness step leaves all oracle state unchanged. -/
private theorem indexedOracle_run_unif {V M G : Type} [DecidableEq M] (draw : ℕ → ProbComp V)
    (hash sign : V → G) (j : Option ℕ) (t : unifSpec.Domain) (s : OracleState V M) :
    (indexedOracle draw hash sign j (.inl (.inl t))).run s =
      (fun v => (v, s)) <$> (unifSpec.query t : ProbComp _) := rfl

/-- A hash step reads the indexed entry and exposes its hash value. -/
theorem indexedOracle_run_hash {V M G : Type} [DecidableEq M] (draw : ℕ → ProbComp V)
    (hash sign : V → G) (j : Option ℕ) (msg : M) (s : OracleState V M) :
    (indexedOracle draw hash sign j (.inl (.inr msg))).run s =
      (fun z => (hash z.1.1, z.2)) <$> (indexedEntry draw j msg).run s := rfl

/-- A signing step reads the indexed entry and records the request before returning its response. -/
theorem indexedOracle_run_sign {V M G : Type} [DecidableEq M] (draw : ℕ → ProbComp V)
    (hash sign : V → G) (j : Option ℕ) (msg : M) (s : OracleState V M) :
    (indexedOracle draw hash sign j (.inr msg)).run s =
      (fun z => (sign z.1.1, z.2.recordSign j msg z.1.2)) <$>
        (indexedEntry draw j msg).run s := rfl

private theorem eraseSelection_recordSign {V M : Type}
    (s : OracleState V M) (j : Option ℕ) (msg : M) (idx : ℕ) :
    (s.recordSign j msg idx).eraseSelection = s.eraseSelection.recordSign none msg idx := by
  simp [OracleState.recordSign, OracleState.eraseSelection]

private theorem indexedEntry_eraseSelection {V M : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (j : Option ℕ) (msg : M) (s : OracleState V M) :
    Prod.map id OracleState.eraseSelection <$> (indexedEntry draw j msg).run s =
      (indexedEntry draw none msg).run s.eraseSelection := by
  cases hc : s.cache msg <;>
    simp [indexedEntry, StateT.run, OracleState.eraseSelection, hc, Functor.map_map,
      OracleState.insert, Prod.map]

/-- Erasing the selected-slot fields commutes with every oracle step. -/
private theorem indexedOracle_eraseSelection {V M G : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (hash sign : V → G) (j : Option ℕ)
    (t : ((unifSpec + (M →ₒ G)) + (M →ₒ G)).Domain) (s : OracleState V M) :
    Prod.map id OracleState.eraseSelection <$> (indexedOracle draw hash sign j t).run s =
      (indexedOracle draw hash sign none t).run s.eraseSelection := by
  rcases t with (t | msg) | msg
  · change Prod.map id OracleState.eraseSelection <$>
      ((fun v => (v, s)) <$> (unifSpec.query t : ProbComp _)) = _
    simp only [Functor.map_map]
    rfl
  · rw [indexedOracle_run_hash, indexedOracle_run_hash, ← indexedEntry_eraseSelection draw j msg s]
    simp [Functor.map_map, Prod.map]
  · rw [indexedOracle_run_sign, indexedOracle_run_sign, ← indexedEntry_eraseSelection draw j msg s]
    simp [Functor.map_map, Prod.map, eraseSelection_recordSign]

/-- Selected-slot bookkeeping has no effect on the adversary's execution or indexed cache. -/
theorem simulateQ_indexedOracle_eraseSelection {V M G α : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (hash sign : V → G) (j : Option ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) α) (s : OracleState V M) :
    Prod.map id OracleState.eraseSelection <$>
        (simulateQ (indexedOracle draw hash sign j) oa).run s =
      (simulateQ (indexedOracle draw hash sign none) oa).run s.eraseSelection :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _
    (indexedOracle_eraseSelection draw hash sign j) oa s

end BLS
