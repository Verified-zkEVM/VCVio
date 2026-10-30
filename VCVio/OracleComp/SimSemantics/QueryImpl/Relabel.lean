/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import PolyFun.PFunctor.Handler.Free

/-!
# Dependent answer representations for oracle handlers

One shared query input is forwarded once. The target answer is read through the inverse
of the equivalence at that input. The handler delegates to the polynomial lens interface.
-/

public section

universe u v

open OracleComp OracleSpec

namespace QueryImpl

variable {ι : Type u} {R S : OracleSpec.{u, v} ι}

/-- The lens forwarding an input and reading its target answer through the inverse map. -/
@[expose] def answerLens (e : ∀ input, R input ≃ S input) :
    PFunctor.Lens R.toPFunctor S.toPFunctor where
  toFunA := id
  toFunB input := (e input).symm

/-- A single target query whose answer is read in the source representation. -/
@[expose] def relabel (e : ∀ input, R input ≃ S input) : QueryImpl R (OracleComp S) :=
  PFunctor.Handler.ofLens (answerLens e)

/-- Relabelling asks the same input and reads back its dependent answer. -/
@[simp] theorem relabel_apply (e : ∀ input, R input ≃ S input) (input : ι) :
    relabel e input = (e input).symm <$> (liftM (S.query input) : OracleComp S (S input)) :=
  rfl

/-- Reading each answer in the opposite representation recovers the original program. -/
theorem simulateQ_relabel_symm_relabel (e : ∀ input, R input ≃ S input)
    {α : Type v} (program : OracleComp R α) :
    simulateQ (relabel (fun input => (e input).symm)) (simulateQ (relabel e) program) =
      program := by
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := QueryImpl.id' _), simulateQ_id']
  intro input
  simp [relabel_apply]

/-- Reading back after the inverse answer conversion recovers the target program. -/
theorem simulateQ_relabel_relabel_symm (e : ∀ input, R input ≃ S input)
    {α : Type v} (program : OracleComp S α) :
    simulateQ (relabel e) (simulateQ (relabel (fun input => (e input).symm)) program) =
      program := by
  simpa only [Equiv.symm_symm] using
    simulateQ_relabel_symm_relabel (fun input => (e input).symm) program

end QueryImpl
