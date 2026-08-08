/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.PFunctor
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.QueryTracking.Tracing

/-!
# PFunctor and OracleSpec Semantics Canaries

These examples exercise the generic polynomial-functor API directly and the
`OracleSpec` compatibility façade. They ensure that probability semantics and
handler instrumentation remain usable without unfolding VCVio internals.
-/

@[expose] public section

namespace VCVioTest.PFunctorFacade

/-- A one-operation polynomial interface returning one of three directions. -/
@[reducible] def triPFunctor : PFunctor := ⟨Unit, fun _ => Fin 3⟩

instance : triPFunctor.Fintype where
  fintypeB _ := by infer_instance

instance : triPFunctor.Inhabited where
  inhabitedB _ := by infer_instance

noncomputable instance : triPFunctor.IsUniformSpec :=
  PFunctor.IsUniformSpec.ofFintypeInhabited _

/-- The direct PFunctor program issuing the three-way operation once. -/
def directSample : PFunctor.FreeM triPFunctor (Fin 3) :=
  PFunctor.FreeM.lift ()

example : 𝒟[directSample] =
    (PFunctor.IsProbabilitySpec.toPMF (P := triPFunctor) () : SPMF (Fin 3)) := by
  simpa only [directSample] using
    (PFunctor.FreeM.evalDist_lift (P := triPFunctor) ())

example := PFunctor.FreeM.evalDist_lift_eq_uniform (P := triPFunctor) ()

example : support directSample = Set.univ := by
  simpa only [directSample] using
    (PFunctor.FreeM.support_lift (P := triPFunctor) ())

example : EvalDistCompatible (PFunctor.FreeM triPFunctor) := inferInstance

/-- A deterministic handler used to exercise generic instrumentation. -/
def zeroHandler : PFunctor.Handler Option triPFunctor :=
  fun _ => some 0

example : zeroHandler.preInsert (fun _ => some ()) () = some 0 := by
  simp [zeroHandler, seqRight_eq]

example : zeroHandler.postInsert (fun _ _ => some ()) () = some 0 := by
  simp [zeroHandler]

/-! ## OracleSpec compatibility -/

/-- The oracle presentation of the same Boolean interface. -/
@[reducible] def boolOracleSpec : OracleSpec (Fin 1) := fun _ => Bool

noncomputable instance : IsUniformSpec boolOracleSpec :=
  OracleSpec.IsUniformSpec.ofFintypeInhabited _

noncomputable example : PFunctor.IsProbabilitySpec boolOracleSpec.toPFunctor := inferInstance

noncomputable example : PFunctor.IsUniformSpec boolOracleSpec.toPFunctor :=
  OracleSpec.IsUniformSpec.toPFunctor

example (program : OracleComp boolOracleSpec Bool) :
    𝒟[program] = program.liftM PFunctor.IsProbabilitySpec.toPMF :=
  PFunctor.FreeM.evalDist_eq_liftM program

example (program : OracleComp boolOracleSpec Bool) :
    𝒟[program] = simulateQ OracleSpec.IsProbabilitySpec.toPMF program :=
  OracleComp.evalDist_eq_simulateQ program

end VCVioTest.PFunctorFacade
