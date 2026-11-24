/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial
public import VCVio.OracleComp.QueryTracking.WriterCost
import PolyFun.Control.Monad.Hom.Writer

/-!
# Costed replay from a settled cache

A partial cache settles a program when its partial interpretation returns `some`.
Such a program has a fixed natural-number query charge and replays from every larger cache.
The charge is recorded before cache lookup, so repeated hits each pay their declared weight.
The replay retains the result, charge and entire live cache for any lawful answer handler.
This is an execution identity for the supplied query weights, not a running-time bound.
-/

public section

open OracleComp OracleSpec

namespace QueryImpl

universe v

variable {ι : Type} {spec : OracleSpec ι} {α : Type}
  {m : Type → Type v} [Monad m] [LawfulMonad m]

/-- Interpreting a free program with its query charges agrees with charging the handler.
The writer records each charge before calling that handler.
-/
theorem simulateQ_withAddCost_runAdd_fusion (impl : QueryImpl spec m)
    (w : spec.Domain → Nat) (body : OracleComp spec α) :
    simulateQ impl (simulateQ ((QueryImpl.id' spec).withAddCost w) body).runAdd =
      (simulateQ (impl.withAddCost w) body).runAdd := by
  -- The monoid writer lifts the existing free-program interpreter without changing its log.
  let F := WriterT.mapHom (ω := Multiplicative Nat) (simulateQ' impl)
  have natural := PFunctor.FreeM.liftM_natural ((QueryImpl.id' spec).withAddCost w) F body
  change F (simulateQ ((QueryImpl.id' spec).withAddCost w) body) =
    simulateQ (fun t => F (((QueryImpl.id' spec).withAddCost w) t)) body at natural
  have point : (fun t => F (((QueryImpl.id' spec).withAddCost w) t)) = impl.withAddCost w := by
    funext t
    apply WriterT.ext
    simp [F, withAddCost, withCost_apply, WriterT.run_bind, simulateQ_map]
  rw [point] at natural
  -- Read the same writer equality through the additive natural-number view.
  have run := congrArg WriterT.run natural
  simpa only [F, AddWriterT.runAdd, simulateQ_map, WriterT.run_mapHom,
    simulateQ'_apply] using
    congrArg (fun action => Prod.map id Multiplicative.toAdd <$> action) run

/-- A successful partial interpretation also settles its program's accumulated query charge. -/
theorem exists_cost_of_toPartialImpl (w : spec.Domain → Nat) (body : OracleComp spec α)
    (known : spec.QueryCache) (a : α)
    (settled : simulateQ known.toPartialImpl body = some a) :
    ∃ delta, simulateQ known.toPartialImpl
      (simulateQ ((QueryImpl.id' spec).withAddCost w) body).runAdd = some (a, delta) := by
  -- Erasing the writer recovers the given successful partial interpretation.
  have erase :
      Prod.fst <$> (simulateQ (known.toPartialImpl.withAddCost w) body).runAdd = some a := by
    rw [AddWriterT.fst_map_runAdd]
    simpa only [withAddCost, fst_map_run_withCost] using settled
  rw [simulateQ_withAddCost_runAdd_fusion]
  cases h : (simulateQ (known.toPartialImpl.withAddCost w) body).runAdd with
  | none => simp [h] at erase
  | some pair =>
      obtain ⟨value, delta⟩ := pair
      have same : value = a := by simpa [h] using erase
      exact ⟨delta, by simp [same]⟩

/-- A settled program replays with the same result and charge, leaving the entire live cache.
The live cache may contain extra rows, and the underlying handler may keep arbitrary state.
Cost instrumentation surrounds the cache, so hits pay their weights too.
-/
theorem run_simulateQ_withCaching_withAddCost_eq_pure_of_toPartialImpl [DecidableEq ι]
    (so : QueryImpl spec m) (w : spec.Domain → Nat) (body : OracleComp spec α)
    (known live : spec.QueryCache) (hcache : known ≤ live) (a : α)
    (settled : simulateQ known.toPartialImpl body = some a) :
    ∃ delta,
      simulateQ known.toPartialImpl
        (simulateQ ((QueryImpl.id' spec).withAddCost w) body).runAdd = some (a, delta) ∧
      ((simulateQ (so.withCaching.withAddCost w) body).runAdd).run live =
        pure ((a, delta), live) := by
  obtain ⟨delta, hdelta⟩ := exists_cost_of_toPartialImpl w body known a settled
  refine ⟨delta, hdelta, ?_⟩
  -- Replay the already scored free program using the same cache extension and endpoint.
  have replay := run_simulateQ_withCaching_eq_pure_of_toPartialImpl so
    (simulateQ ((QueryImpl.id' spec).withAddCost w) body).runAdd
    (QueryCache.simulateQ_toPartialImpl_mono hcache _ hdelta)
  rw [simulateQ_withAddCost_runAdd_fusion] at replay
  exact replay

end QueryImpl
