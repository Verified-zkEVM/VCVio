/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Covariance
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-! # Identifying the BLS random-oracle game

The Boneh–Lynn–Shacham EUF-CMA experiment uses the standard shared lazy random oracle.
Its signing log is reconstructed as an input list, then combined with the cache in one
stateful execution. Index bookkeeping projects to precisely this execution.
-/

public section

open OracleComp OracleSpec

namespace BLS

/-- Forget insertion indices when projecting the indexed cache to the standard random oracle. -/
@[expose] def valueCache {V M : Type} (s : OracleState V M) : (M →ₒ V).QueryCache :=
  QueryCache.ofFn fun msg => (s.cache msg).map Prod.fst

/-- Honest signing through the standard lazy random-oracle cache. -/
@[expose] def realSign {F G M : Type} [SMul F G] [SampleableType G] [DecidableEq M]
    (x : F) : QueryImpl (M →ₒ G) (StateT (M →ₒ G).QueryCache ProbComp) :=
  fun msg => (x • ·) <$> (M →ₒ G).randomOracle msg

/-- The real hash/signing handler, with its signing input log and random-oracle cache flattened
into a single state. -/
@[expose] def realOracle {F G M : Type} [SMul F G] [SampleableType G] [DecidableEq M]
    (x : F) : QueryImpl ((unifSpec + (M →ₒ G)) + (M →ₒ G))
      (StateT (List M × (M →ₒ G).QueryCache) ProbComp) :=
  let impl : QueryImpl ((unifSpec + (M →ₒ G)) + (M →ₒ G))
      (StateT (List M) (StateT (M →ₒ G).QueryCache ProbComp)) :=
    ((M →ₒ G).romImpl.liftTarget
      (StateT (List M) (StateT (M →ₒ G).QueryCache ProbComp))) +
      QueryImpl.appendInputLog (realSign (M := M) (G := G) x)
  impl.flattenStateT

private theorem valueCache_insert {V M : Type} [DecidableEq M]
    (s : OracleState V M) (j : Option ℕ) (msg : M) (v : V) :
    valueCache (s.insert j msg v) = (valueCache s).cacheQuery msg v := by
  apply QueryCache.ext
  intro n
  by_cases hn : n = msg
  · subst n
    simp [valueCache, OracleState.insert]
  · simp [valueCache, OracleState.insert, hn]

private theorem indexedEntry_valueCache {G M : Type} [SampleableType G] [DecidableEq M]
    (j : Option ℕ) (msg : M) (s : OracleState G M) :
    (fun z => (z.1.1, valueCache z.2)) <$>
      (indexedEntry (fun _ => $ᵗ G) j msg).run s =
      ((M →ₒ G).randomOracle msg).run (valueCache s) := by
  rw [randomOracle.run_eq]
  cases hc : s.cache msg with
  | some vi =>
    obtain ⟨v, i⟩ := vi
    simp [indexedEntry, StateT.run, valueCache, hc]
  | none =>
    have he : valueCache s msg = none := by simp [valueCache, hc]
    simp only [indexedEntry, StateT.run, hc, he, Functor.map_map, bind_pure_comp]
    congr 1
    funext v
    exact Prod.ext rfl (valueCache_insert s j msg v)

private theorem indexedEntry_signed {G M : Type} [SampleableType G] [DecidableEq M]
    (j : Option ℕ) (msg : M) (s : OracleState G M) {α : Type}
    (k : G → (M →ₒ G).QueryCache → List M → α) :
    (fun z => k z.1.1 (valueCache z.2) z.2.signed) <$>
      (indexedEntry (fun _ => $ᵗ G) j msg).run s =
    (fun z => k z.1.1 (valueCache z.2) s.signed) <$>
      (indexedEntry (fun _ => $ᵗ G) j msg).run s := by
  cases hc : s.cache msg <;> simp [indexedEntry, StateT.run, hc, Functor.map_map,
    OracleState.insert]

/-- Projecting the insertion bookkeeping yields the real hash/signing handler step by step. -/
theorem indexedOracle_realOracle_proj {F G M : Type} [SMul F G]
    [SampleableType G] [DecidableEq M] (x : F) (j : Option ℕ)
    (t : ((unifSpec + (M →ₒ G)) + (M →ₒ G)).Domain) (s : OracleState G M) :
    (fun z => (z.1, z.2.signed, valueCache z.2)) <$>
      (indexedOracle (fun _ => $ᵗ G) id (x • ·) j t).run s =
      (realOracle x t).run (s.signed, valueCache s) := by
  rcases t with (t | msg) | msg
  · simp only [realOracle, QueryImpl.flattenStateT, indexedOracle, HAdd.hAdd, QueryImpl.add,
      OracleSpec.romImpl, unifFwdImpl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
      StateT.run_monadLift, monadLift_self, Functor.map_map, StateT.run_mk,
      StateT.run_map, bind_pure_comp]
    simp only [StateT.run, Functor.map_map]
    rfl
  · rw [indexedOracle_run_hash]
    simp only [Functor.map_map, id_eq]
    rw [indexedEntry_signed j msg s (fun v c l => (v, l, c))]
    have he := congrArg (fun oa => (fun z => (z.1, s.signed, z.2)) <$> oa)
      (indexedEntry_valueCache j msg s)
    simp only [Functor.map_map] at he
    rw [he]
    simp only [realOracle, QueryImpl.flattenStateT, OracleSpec.romImpl,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply,
      StateT.run_monadLift, monadLift_self, StateT.run_map,
      StateT.run_mk, Functor.map_map, bind_pure_comp]
    rfl
  · rw [indexedOracle_run_sign]
    simp only [Functor.map_map]
    change (fun z => (x • z.1.1, z.2.signed ++ [msg], valueCache z.2)) <$>
      (indexedEntry (fun _ => $ᵗ G) j msg).run s = _
    rw [indexedEntry_signed j msg s (fun v c l => (x • v, l ++ [msg], c))]
    have he := congrArg (fun oa => (fun z => (x • z.1, s.signed ++ [msg], z.2)) <$> oa)
      (indexedEntry_valueCache j msg s)
    simp only [Functor.map_map] at he
    rw [he]
    simp only [realOracle, QueryImpl.flattenStateT, QueryImpl.add_apply_inr,
      QueryImpl.appendInputLog_apply, realSign, StateT.run_bind, StateT.run_map,
      StateT.run_modify, StateT.run_monadLift, monadLift_self, StateT.run_mk,
      Functor.map_map, pure_bind, bind_pure_comp]

/-- The indexed execution projects to the real execution for any adaptive program. -/
theorem simulateQ_indexedOracle_realOracle_proj {F G M α : Type} [SMul F G]
    [SampleableType G] [DecidableEq M] (x : F) (j : Option ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) α) (s : OracleState G M) :
    (fun z => (z.1, z.2.signed, valueCache z.2)) <$>
      (simulateQ (indexedOracle (fun _ => $ᵗ G) id (x • ·) j) oa).run s =
      (simulateQ (realOracle x) oa).run (s.signed, valueCache s) :=
  map_run_simulateQ_eq_of_query_map_eq _ _
    (fun st : OracleState G M => (st.signed, valueCache st))
    (indexedOracle_realOracle_proj x j) oa s

private theorem rom_writerTMapBase {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (pk : G₁ × G₂) (x : F) :
    (M →ₒ G₁).romImpl.writerTMapBase
      ((unifSpec + (M →ₒ G₁)).passthrough + (scheme (M := M) e g₁ g₂).signingOracle pk x) =
    ((M →ₒ G₁).romImpl.liftTarget
      (WriterT (QueryLog (M →ₒ G₁)) (StateT (M →ₒ G₁).QueryCache ProbComp))) +
      QueryImpl.withLogging (realSign (M := M) (G := G₁) x) := by
  funext t
  rcases t with t | msg
  · ext c
    simp only [QueryImpl.writerTMapBase, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      WriterT.mk]
    rfl
  · ext c
    simp [QueryImpl.writerTMapBase, SignatureAlg.signingOracle, QueryImpl.withLogging_apply,
      scheme, realSign, OracleSpec.romImpl, QueryImpl.add_apply_inr,
      StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
      WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell, WriterT.run_pure,
      map_eq_bind_pure_comp]

/-- The standard signing-oracle run under the ROM runtime is the flattened real execution,
with the WriterT signature log projected to its queried messages. -/
theorem runWithSigningOracle_realOracle {F G₁ G₂ Gₜ M α : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (pk : G₁ × G₂) (x : F)
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) α)
    (c : (M →ₒ G₁).QueryCache) (l : List M) :
    (fun z => (z.1.1, l ++ z.1.2.map (fun e => e.1), z.2)) <$>
      (simulateQ (M →ₒ G₁).romImpl ((scheme e g₁ g₂).runWithSigningOracle pk x oa)).run c =
      (simulateQ (realOracle x) oa).run (l, c) := by
  let hq : HasQuery (unifSpec + (M →ₒ G₁)) (StateT (M →ₒ G₁).QueryCache ProbComp) :=
    (M →ₒ G₁).romImpl.toHasQuery
  rw [SignatureAlg.runWithSigningOracle_def, QueryImpl.simulateQ_writerTMapBase_run,
    rom_writerTMapBase]
  have hr := QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
    (spec₀ := unifSpec + (M →ₒ G₁)) (loggedSpec := M →ₒ G₁)
    (m₀ := StateT (M →ₒ G₁).QueryCache ProbComp) (realSign (M := M) (G := G₁) x) oa l
  have hr' := congrArg (fun z : StateT (M →ₒ G₁).QueryCache ProbComp _ => z.run c) hr
  simp only [StateT.run_map] at hr'
  rw [realOracle, simulateQ_flattenStateT_run]
  have hbase : @HasQuery.toQueryImpl _ (unifSpec + (M →ₒ G₁))
      (StateT (M →ₒ G₁).QueryCache ProbComp) hq = (M →ₒ G₁).romImpl := rfl
  simp only [hbase] at hr'
  rw [← hr']
  simp only [bind_pure_comp, Functor.map_map]

end BLS
