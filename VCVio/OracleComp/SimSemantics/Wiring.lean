/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import PolyFun.PFunctor.Wiring
public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Recursive wiring with a shared oracle boundary

A recursive polynomial wiring exposing one oracle interface compiles to an `OracleComp` over
that interface. Every reference to the external input uses the same oracle handler, including
its private state. The box equation permits local implementations to be expanded compositionally.
-/

public section

open OracleComp

universe uB

namespace PFunctor.Wiring

attribute [local implicit_reducible] PFunctor.sigma

variable {ι Boxes : Type} {spec : OracleSpec.{0, uB} ι} {Arity : Boxes → Type}
  {Dom : (b : Boxes) → Arity b → PFunctor.{0, uB}} {Cod : Boxes → PFunctor.{0, uB}}

/-- Compile a recursively wired handler to its single shared oracle boundary. -/
@[expose] def oracleProgram
    (implementation : (b : Boxes) → (a : (Cod b).A) →
      FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    {output : PFunctor.{0, uB}}
    (wiring : Wiring Boxes Arity Dom Cod Unit (fun _ => spec.toPFunctor) output)
    (a : output.A) : OracleComp spec (output.B a) :=
  (wiring.eval implementation a).liftM
    fun q : (PFunctor.sigma fun _ : Unit => spec.toPFunctor).A =>
      FreeM.lift (P := spec.toPFunctor) q.2

/-- An external wire performs one query against the shared handler. -/
@[simp]
theorem oracleProgram_input
    (implementation : (b : Boxes) → (a : (Cod b).A) →
      FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a)) (a : ι) :
    oracleProgram (spec := spec) implementation (.input ()) a =
      FreeM.lift (P := spec.toPFunctor) a := by
  simp only [oracleProgram, eval_input]
  exact FreeM.liftM_lift
    (fun q : (PFunctor.sigma fun _ : Unit => spec.toPFunctor).A =>
      FreeM.lift (P := spec.toPFunctor) q.2) ⟨(), a⟩

/-- Expanding a box runs its implementation against the recursively compiled child handlers. -/
theorem oracleProgram_box
    (implementation : (b : Boxes) → (a : (Cod b).A) →
      FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a)) (b : Boxes)
    (children : (port : Arity b) →
      Wiring Boxes Arity Dom Cod Unit (fun _ => spec.toPFunctor) (Dom b port))
    (a : (Cod b).A) :
    oracleProgram implementation (.box b children) a =
      (implementation b a).liftM (fun q : (PFunctor.sigma (Dom b)).A =>
        oracleProgram implementation (children q.1) q.2) := by
  simp only [oracleProgram, eval_box, FreeM.liftM_comp]
  rfl

end PFunctor.Wiring
