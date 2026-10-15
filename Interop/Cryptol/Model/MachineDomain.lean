/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Adequacy
public import PolyFun.ITree.Domain
public import PolyFun.ITree.Execution

/-!
# The abstract machine through generic PolyFun semantics

The machine's guarded interaction tree can be executed with PolyFun's
resumption adapter. Its continuous-algebra interpretation equals the
independently defined compositional language semantics. This equality uses
both machine soundness and computational adequacy.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- The empty visible signature has a unique algebra. -/
@[expose] noncomputable def MachineState.algebra (r : ClosedTy) :
    PFunctor.Resumption.ContinuousAlgebra events (Computation r) := fun e => e.elim

/-- Interpret an unbounded machine execution through the generic ITree domain API. -/
@[expose] noncomputable def MachineState.treeDenote {r : ClosedTy} (state : MachineState r) :
    Computation r := ITree.denote Outcome.denote (algebra r) state.tree

/-- The machine interpretation satisfies the same transition equations. -/
theorem MachineState.treeDenote_step {r : ClosedTy} (state : MachineState r) :
    state.treeDenote = match state.step with
      | .inl result => result.denote
      | .inr next => next.treeDenote := by
  rw [treeDenote, ITree.denote_eq]
  simp only [tree, Control.Transition.tree, ITree.shape'_corec_apply]
  cases state.step <;> rfl

/-- The generic least interpretation is bounded by the machine invariant. -/
theorem MachineState.treeDenote_le {r : ClosedTy} (state : MachineState r) :
    state.treeDenote ≤ state.denote := by
  unfold treeDenote tree Control.Transition.tree
  rw [ITree.denote_corec]
  refine (ContinuousHom.fix_le _ (x := MachineState.denote) ?_) state
  intro s
  rw [denote_step s]
  cases hs : s.step <;> simp [ITree.corecDomainStep, hs]

/-- A finite execution determines the generic tree interpretation. -/
theorem MachineState.Executes.treeDenote {r : ClosedTy} {state : MachineState r}
    {result : Outcome r} (h : state.Executes result) : state.treeDenote = result.denote := by
  induction h with
  | done hs => rw [MachineState.treeDenote_step, hs]
  | next hs _ ih => rw [MachineState.treeDenote_step, hs]; exact ih

/-- The guarded PolyFun execution and the compositional semantics agree
for all closed terms, including divergent and higher-order terms. -/
theorem Expr.denote_eq_treeDenote {a : ClosedTy} (e : Expr [] a) :
    e.denote Environment.empty = e.start.treeDenote := by
  apply le_antisymm
  · have hr := e.closed_related
    generalize hd : e.denote Environment.empty = d at hr ⊢
    induction d using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe value =>
        cases value with
        | inl err =>
            have he := (hr : Evaluates e (.error err.value)).treeDenote
            rw [he]
            exact le_rfl
        | inr v =>
            obtain ⟨w, hw, _⟩ := hr
            have hs := hw.sound
            rw [hd] at hs
            rw [hs, hw.treeDenote]
  · exact e.start.treeDenote_le

end Interop.Cryptol
