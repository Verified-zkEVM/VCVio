/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.Control.WriterT.Map
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Homomorphic mapping of instrumented query costs

The same handler receives every query. Only its accumulated writer cost is mapped, before
any interpretation or cache can answer the query.
-/

public section

open OracleSpec OracleComp

universe v

namespace QueryImpl

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type v} [Monad m] [LawfulMonad m]
variable {C D α : Type} [AddMonoid C] [AddMonoid D]

/-- The cost of each query is mapped without changing its handler or returned value. -/
theorem mapCostHom_withAddCost (f : C →+ D) (impl : QueryImpl spec m)
    (cost : spec.Domain → C) (input : spec.Domain) :
    AddWriterT.mapCostHom f (impl.withAddCost cost input) =
      impl.withAddCost (fun query => f (cost query)) input := by
  apply WriterT.ext
  simp [withAddCost_apply, AddWriterT.mapCostHom, WriterT.mapOutputHom,
    AddWriterT.addTell, Functor.map_map]

/-- A monoid cost homomorphism commutes with the complete free-oracle fold. -/
theorem mapCostHom_simulateQ_withAddCost (f : C →+ D) (impl : QueryImpl spec m)
    (cost : spec.Domain → C) (body : OracleComp spec α) :
    AddWriterT.mapCostHom f (simulateQ (impl.withAddCost cost) body) =
      simulateQ (impl.withAddCost (fun query => f (cost query))) body := by
  have natural := PFunctor.FreeM.liftM_natural (impl.withAddCost cost)
    (AddWriterT.mapCostHom f) body
  change AddWriterT.mapCostHom f (simulateQ (impl.withAddCost cost) body) =
    simulateQ (fun input => AddWriterT.mapCostHom f (impl.withAddCost cost input)) body at natural
  simpa only [mapCostHom_withAddCost] using natural

end QueryImpl
