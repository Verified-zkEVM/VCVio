/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Model.Examples
import Interop.Cryptol.Translation.Export
import Interop.Cryptol.Model.Observation
import Interop.Cryptol.Model.Polymorphic

/-!
# Model regression and public-API checks

These ordinary imports exercise laziness, semantic divergence, binding,
polymorphic instantiation, finite observations, and exact residual execution.
Executable fixtures are also compared against the pinned external runtime.
-/

public section

open Interop.Cryptol Interop.Cryptol.Examples OmegaCompletePartialOrder

example {Γ : List ClosedTy} {a : ClosedTy} (η : Environment Γ) :
    (Expr.diverge : Expr Γ a).denote η = ⊥ := by
  change ((Expr.var (.zero : Var (a :: Γ) a)).bodyDenote η).fix = ⊥
  exact le_antisymm (ContinuousHom.fix_le _ le_rfl) bot_le

example {a : ClosedTy} (arg : Expr [] a) :
    (Expr.app (.lam (.integer 7)) arg).denote Environment.empty = .value ⟨7⟩ := rfl

example (bad : ClosedExpr [] .integer) :
    (Expr.fst (.pair (.integer 9) bad)).denote Environment.empty = .value ⟨9⟩ := rfl

example : (.index naturals (.integer 4) : ClosedExpr [] .integer).denote
    Environment.empty = .value ⟨4⟩ := by
  apply Evaluates.sound (result := .ok (.integer 4))
  exact (MachineState.executes_iff_terminates _ _).mpr ⟨500, rfl⟩

example : (.index (.snd evenOdd) (.integer 2) : ClosedExpr [] .integer).denote
    Environment.empty = .value ⟨5⟩ := by
  apply Evaluates.sound (result := .ok (.integer 5))
  exact (MachineState.executes_iff_terminates _ _).mpr ⟨500, rfl⟩

example (fuel next : Nat) (state : MachineState .integer) :
    state.run (fuel + next) = MachineState.continueRun next (state.run fuel) :=
  state.run_add fuel next

example {Γ : List ClosedTy} {a : ClosedTy} (e : Resolved.Term Γ a) :
    e.rename (fun x => x) = e := IPFunctor.ScopedSignature.Term.rename_id e

example {Γ : List ClosedTy} {a : ClosedTy} (e : Resolved.Term Γ a) :
    e.subst (fun x => .pure x) = e := IPFunctor.ScopedSignature.Term.subst_id e

example {Γ : List ClosedTy} {a : ClosedTy} (e : Resolved.Term Γ a) :
    (Resolved.lower e).denote = Resolved.denote e := Resolved.lower_correct e

example (arguments : mapSchema.Instantiation) :
    Related ((polymorphicMap.instantiate arguments).denote Environment.empty)
      (polymorphicMap.instantiate arguments) := polymorphicMap.adequacy arguments

example : Export.stringLiteral "quote\" slash\\ line\n" =
    "\"quote\\\" slash\\\\ line\\n\"" := rfl

example {a : ClosedTy} (e : Expr [] a) (obs : Observation a .integer) (err : EvalError) :
    obs.denote (e.denote Environment.empty) = .error err ↔
      Evaluates (obs.apply e) (.error err) := obs.adequacy_error e err
