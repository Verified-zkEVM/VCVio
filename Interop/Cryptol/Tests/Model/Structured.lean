/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.Certified
import Interop.Cryptol.Model.Zero
import Interop.Cryptol.Model.ResolvedSequences

/-!
# Demand-sensitive structured primitives

Empty folds ignore their function and sequence. Structural zero supplies lazy
aggregates. Array arithmetic still demands both outer array constructors.
-/

public section

namespace Interop.Cryptol.Tests.Model.Structured

open OmegaCompletePartialOrder Interop.Cryptol

/-- An ignored fold argument may fail without preventing the returned accumulator. -/
theorem empty_fold_ignores_errors (z : Computation .integer) :
    Semantics.foldlPrefix (b := .integer) 0 0
      (.error (.user "function")) z (.error (.user "sequence")) = z :=
  Semantics.foldlPrefix_zero _ _ _ _

example (xs : Computation (.seq (.finite 3) .integer)) :
    Semantics.foldlPrefix 3 3
      (Semantics.function₂ (.ofFun (fun (_ : Computation .integer) =>
        .const (.value ⟨7⟩ : Computation .integer)))) ⊥ xs =
      (DomainResult.value ⟨7⟩ : Computation .integer) := rfl

example : Semantics.intLe (.error (.user "left")) (.error (.user "right")) =
    .error (.user "left") := rfl

example : Semantics.wordArrayArithmetic 0 8 .add
    (.error (.user "left")) (.value Fin.elim0) = .error (.user "left") := rfl

example : Semantics.wordArrayArithmetic 0 8 .add
    (.value Fin.elim0) (.error (.user "right")) = .error (.user "right") := rfl

example : DomainResult.applyContinuous (Semantics.zero (.arrow .integer .bit)) ⊥ =
    DomainResult.value ⟨false⟩ := rfl

example : Semantics.indexAt (Semantics.zero (.seq .infinite .integer)) 100000 =
    DomainResult.value ⟨0⟩ := rfl

example : (Expr.zero (.prod .bit (.seq (.finite 0) .integer)) : Expr [] _).denote
    Environment.empty = .value (.value ⟨false⟩, .value (fun _ => .value ⟨0⟩)) := by
  rw [Expr.denote_zero]
  rfl

example : Resolved.denote
    (Resolved.Term.map (.lam (.integer 7))
      (.error (.user "generator") : Resolved.Term [] (.seq (.finite 3) .integer)))
    Environment.empty = .value (fun _ => .value ⟨7⟩) := by
  rw [Resolved.denote_map]
  rfl

example : Resolved.denote (Resolved.Term.range (-2) 0 : Resolved.Term [] _)
    Environment.empty = .value (fun i : Fin 0 => .value ⟨-2 + (i.val : Int)⟩) :=
  Resolved.denote_range _ _ _

end Interop.Cryptol.Tests.Model.Structured
