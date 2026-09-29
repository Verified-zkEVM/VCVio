/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.PFunctorMeasure.Core
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.QueryTracking.Tracing.Core
import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# PFunctor and OracleSpec Semantics Canaries

These examples exercise the generic polynomial-functor API directly and its `OracleSpec`
presentation. They ensure that measure semantics and handler instrumentation remain usable
without unfolding VCVio internals.
-/

public section

namespace VCVioTest.PFunctorFacade

/-- A one-operation polynomial interface returning one of three directions. -/
@[expose, reducible] def triPFunctor : PFunctor := ⟨Unit, fun _ => Fin 3⟩

noncomputable instance : triPFunctor.IsMeasureSpec :=
  PFunctor.IsMeasureSpec.uniformOfFiniteNonempty _

/-- The direct PFunctor program issuing the three-way operation once. -/
@[expose]
def directSample : PFunctor.FreeM triPFunctor (Fin 3) :=
  PFunctor.FreeM.lift ()

example : 𝒟[directSample] = ProbabilityTheory.uniformOn Set.univ :=
  PFunctor.FreeM.evalDist_lift (P := triPFunctor) ()

example : support directSample = Set.univ :=
  PFunctor.FreeM.support_lift (P := triPFunctor) ()

noncomputable example : EvalDistSemantics (PFunctor.FreeM triPFunctor) := inferInstance

/-- A deterministic handler used to exercise generic instrumentation. -/
@[expose]
def zeroHandler : PFunctor.Handler Option triPFunctor :=
  fun _ => some 0

example : zeroHandler.preInsert (fun _ => some ()) () = some 0 := by
  simp [zeroHandler, seqRight_eq]

example : zeroHandler.postInsert (fun _ _ => some ()) () = some 0 := by
  simp [zeroHandler]

/-! ## OracleSpec compatibility -/

/-- The oracle presentation of the same Boolean interface. -/
@[expose, reducible] def boolOracleSpec : OracleSpec (Fin 1) := fun _ => Bool

noncomputable instance : OracleSpec.IsUniformMeasureSpec boolOracleSpec :=
  .ofFiniteNonempty _

noncomputable example : EvalDistSemantics (OracleComp boolOracleSpec) := inferInstance

-- Instance synthesis at the erased literal. Tactics that unfold the reducible layers above
-- `OracleSpec` leave a bare `PFunctor.mk` in the goal; the support instances are still found there
-- with no transparency help from `OracleSpec` itself (see the comment on its
-- `implicit_reducible` attribute, which serves dependent-type checks, not synthesis).
example : MonadAttach (PFunctor.FreeM (PFunctor.mk (Fin 1) fun _ => Bool)) := inferInstance

/-- The uniform answer measure of the oracle presentation is the uniform measure on `Bool`. -/
example : 𝒟[(liftM (boolOracleSpec.query 0) : OracleComp boolOracleSpec Bool)] =
    ProbabilityTheory.uniformOn Set.univ :=
  OracleComp.evalDist_liftM_query_uniform (spec := boolOracleSpec) 0

/-! ## Nested coproduct transparency -/

section NestedCoproductTransparency

variable {ι₁ ι₂ ι₃ : Type}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃}

set_option linter.tacticCheckInstances true

example (impl : QueryImpl ((spec₁ + spec₂) + spec₃) Id) (t : spec₂.Domain)
    (consume : spec₂.Range t → Nat) :
    consume (impl (.inl (.inr t))) = consume (impl (.inl (.inr t))) := by
  rfl

example (impl : QueryImpl ((spec₁ + spec₂) + spec₃) Id) (t : spec₃.Domain)
    (consume : spec₃.Range t → Nat) :
    consume (impl (.inr t)) = consume (impl (.inr t)) := by
  rfl

example (impl : QueryImpl ((spec₁ + spec₂) + spec₃) Id) :
    QueryImpl spec₃ (StateT (List spec₃.Domain) Id) :=
  QueryImpl.appendInputLog (fun t => impl (.inr t))

example [OracleSpec.IsMeasureSpec ((spec₁ + spec₂) + spec₃)] (t : spec₂.Domain)
    (program : OracleComp ((spec₁ + spec₂) + spec₃)
      ((((spec₁ + spec₂) + spec₃).Range (.inl (.inr t))) × Bool)) :
    Pr{let z ← program}[(z : spec₂.Range t × Bool).2 = true] =
      Pr{let z ← program}[(z : spec₂.Range t × Bool).2 = true] := by
  rfl

example [OracleSpec.IsMeasureSpec ((spec₁ + spec₂) + spec₃)] (t : spec₃.Domain)
    (program : OracleComp ((spec₁ + spec₂) + spec₃)
      ((((spec₁ + spec₂) + spec₃).Range (.inr t)) × Bool)) :
    Pr{let z ← program}[(z : spec₃.Range t × Bool).2 = true] =
      Pr{let z ← program}[(z : spec₃.Range t × Bool).2 = true] := by
  rfl

end NestedCoproductTransparency

end VCVioTest.PFunctorFacade
