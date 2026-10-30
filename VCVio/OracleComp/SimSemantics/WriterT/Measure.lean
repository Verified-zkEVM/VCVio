/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.Control.WriterT.State
public import VCVio.OracleComp.SimSemantics.WriterT.Core
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Joint append-log and service-state distributions

Local laws transport the entire chronological log and retained state through an adaptive fold.
-/

public section

universe u v idx

open OracleComp OracleSpec

namespace OracleComp

/-- Product-state accumulation commutes with the existing free-oracle fold. -/
theorem writerToState_simulateQ
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ ω α : Type u} {ι : Type idx}
    {spec : OracleSpec.{idx, u} ι} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (impl : QueryImpl spec (WriterT ω (StateT σ m))) (program : OracleComp spec α) :
    WriterT.appendToState (simulateQ impl program) =
      simulateQ (fun input => WriterT.appendToState (impl input)) program := by
  simpa only [simulateQ, WriterT.appendToStateHom] using
    (PFunctor.FreeM.liftM_natural impl
      (WriterT.appendToStateHom (m := m) (σ := σ) (ω := ω)) program)

/-- Local joint response, append-log and state laws lift to complete adaptive runs. -/
theorem evalDistEq_simulateQ_run_writerT_stateT_map :
  ∀ {ι : Type} {spec : OracleSpec ι} {σ τ ω ν α : Type}
    [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    [EmptyCollection ν] [Append ν] [LawfulAppend ν]
    (left : QueryImpl spec (WriterT ν (StateT τ ProbComp)))
    (right : QueryImpl spec (WriterT ω (StateT σ ProbComp)))
    (project : σ → τ) (mapLog : ω → ν),
    mapLog ∅ = ∅ →
    (∀ first second, mapLog (first ++ second) = mapLog first ++ mapLog second) →
    (∀ input state,
      (left input).run.run (project state) =ᵈ
        (fun output => ((output.1.1, mapLog output.1.2), project output.2)) <$>
          (right input).run.run state) →
    ∀ (program : OracleComp spec α) (state : σ),
      (simulateQ left program).run.run (project state) =ᵈ
        (fun output => ((output.1.1, mapLog output.1.2), project output.2)) <$>
          (simulateQ right program).run.run state := by
  intro ι spec σ τ ω ν α _ _ _ _ _ _ left right project mapLog hzero happ hstep program state
  have augmentedStep : ∀ input (current : σ × ω),
      (WriterT.appendToState (left input)).run (project current.1, mapLog current.2) =ᵈ
        Prod.map id (fun final => (project final.1, mapLog final.2)) <$>
          (WriterT.appendToState (right input)).run current := by
    intro input current
    have h := (hstep input current.1).map fun output =>
      (output.1.1, (output.2, mapLog current.2 ++ output.1.2))
    simpa only [WriterT.appendToState, StateT.run_mk, Functor.map_map, Function.comp_def,
      Prod.map, id_eq, happ] using h
  have h := OracleComp.evalDistEq_simulateQ_run_map
    (fun input => WriterT.appendToState (left input))
    (fun input => WriterT.appendToState (right input))
    (fun current => (project current.1, mapLog current.2)) augmentedStep
    program (state, (∅ : ω))
  rw [← writerToState_simulateQ, ← writerToState_simulateQ] at h
  have joint := h.map fun output : α × (τ × ν) =>
    ((output.1, output.2.2), output.2.1)
  simp only [WriterT.appendToState, StateT.run_mk, hzero,
    LawfulAppend.empty_append, Functor.map_map, Prod.map, id_eq,
    Prod.mk.eta] at joint
  have hid : (fun output : (α × ν) × τ => output) <$>
        (simulateQ left program).run.run (project state) =
      (simulateQ left program).run.run (project state) := by
    change id <$> (simulateQ left program).run.run (project state) = _
    exact id_map _
  rw [hid] at joint
  exact joint

end OracleComp
