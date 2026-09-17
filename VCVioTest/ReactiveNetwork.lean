/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.Interaction.UC.ReactiveRuntime

/-!
# Nonconstant execution observations

The runtime observation distinguishes returned Boolean values. Its exact behavior
adequacy theorem preserves the same measure, rather than making all networks equivalent.
-/

public section

namespace VCVioTest.ReactiveNetwork

open PFunctor Interaction.UC ReactiveNetwork ReactiveProcess ReactiveRuntime MeasureTheory

@[expose] def returnedNetwork (value : Bool) : Network Unit PortBoundary.empty Bool where
  effect _ := ⟨Empty, Empty.elim⟩
  ports _ := PortBoundary.empty
  component _ := DynSystem.DynComputation.ofFn fun _ => .returned value
  route _ packet := packet.1.elim
  ingress packet := packet.1.elim
  environment := ()

def noEffects (value : Bool) :
    (id : Unit) → Handler (StateT Unit ProbComp) ((returnedNetwork value).effect id) :=
  fun _ operation => operation.elim

instance : MeasurableSpace (Option (Outcome Bool)) := ⊤

/-- A runtime-derived observation distinguishes two constant-returning networks. -/
theorem returned_laws_ne :
    tokenLaw (returnedNetwork false) (noEffects false) (pure ()) 1 ≠
      tokenLaw (returnedNetwork true) (noEffects true) (pure ()) 1 := by
  have law (value : Bool) :
      tokenLaw (returnedNetwork value) (noEffects value) (pure ()) 1 =
        Measure.dirac (some (.returned value)) := by
    rw [tokenLaw_eq_evalDist (returnedNetwork value) (noEffects value) (pure ()) 1]
    change 𝒟[(pure (some (.returned value)) : ProbComp (Option (Outcome Bool)))] = _
    simp
  rw [law, law]
  intro h
  have hh := congrArg (fun μ : Measure (Option (Outcome Bool)) =>
    μ {some (.returned true)}) h
  simp at hh

/-- The exact behavior presentation preserves this actual distinguishing observation. -/
example (value : Bool) :
    tokenLaw (returnedNetwork value).behavior (noEffects value) (pure ()) 1 =
      tokenLaw (returnedNetwork value) (noEffects value) (pure ()) 1 :=
  tokenLaw_behavior _ _ _ _

end VCVioTest.ReactiveNetwork
