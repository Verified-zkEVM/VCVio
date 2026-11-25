/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# Results in large universes

`ProbComp` returns values in every universe, and its output measure is defined there. A
handler whose answers lie in a large universe runs into `ProbComp` at that universe.

`simulateQ` returns results in the answer universe of the source specification, and
`QueryImpl.withLogging` stores its log in that universe. A log over a large query index therefore
cannot pass through a handler with small answers. `OracleComp.subst` returns results in any
universe, and the path run `PFunctor.FreeM.map (pathLogResult oa) (PFunctor.FreeM.withPath oa)`
records the log in the universe of the index.
-/

public section

open OracleComp OracleSpec MeasureTheory

universe u

namespace VCVioTest.LargeResultUniverse

/-! ## `ProbComp` at a large universe -/

example (α : Type u) (x : α) : ProbComp α := pure x

/-- A small sampler moves to a large output type through the free monad's map, which changes
universes; `<$>` keeps one universe. -/
example (α : Type u) (f : Fin 3 → α) : ProbComp α := PFunctor.FreeM.map f ($ᵗ Fin 3)

noncomputable example (α : Type u) [MeasurableSpace α] (oa : ProbComp α) : Measure α := 𝒟[oa]

example (α : Type u) [MeasurableSpace α] (x : α) :
    𝒟[(pure x : ProbComp α)] = Measure.dirac x := by
  simp

/-- A handler with large answers into `ProbComp`, the shape of a challenge sampler whose
challenges lie in the message universe. -/
example {ι : Type u} (spec : OracleSpec.{u, u} ι) (impl : QueryImpl spec ProbComp)
    (oa : OracleComp spec PUnit.{u + 1}) : ProbComp PUnit.{u + 1} :=
  simulateQ impl oa

/-! ## A large query log through a small-answer target -/

example {ι : Type u} (spec : OracleSpec.{u, 0} ι) {κ : Type} (target : OracleSpec.{0, 0} κ)
    (impl : QueryImpl spec (OracleComp target)) (oa : OracleComp spec Bool) :
    OracleComp target (Bool × QueryLog spec) :=
  subst impl (PFunctor.FreeM.map (pathLogResult oa) (PFunctor.FreeM.withPath oa))

example {ι : Type u} (spec : OracleSpec.{u, 0} ι) {κ : Type} (target : OracleSpec.{0, 0} κ)
    (impl : QueryImpl spec (OracleComp target)) (oa : OracleComp spec Bool) :
    PFunctor.FreeM.map Prod.fst
        (subst impl (PFunctor.FreeM.map (pathLogResult oa) (PFunctor.FreeM.withPath oa))) =
      simulateQ impl oa := by
  rw [map_fst_subst_map_pathLogResult_withPath, subst_eq_simulateQ]

-- `withLogging` rejects a large index: its writer log lies in the answer universe.
/--
error: Application type mismatch
-/
#guard_msgs (substring := true) in
example {ι : Type u} (spec : OracleSpec.{u, 0} ι) {κ : Type} (target : OracleSpec.{0, 0} κ)
    (impl : QueryImpl spec (OracleComp target)) :
    QueryImpl spec (WriterT (QueryLog spec) (OracleComp target)) :=
  impl.withLogging

end VCVioTest.LargeResultUniverse
