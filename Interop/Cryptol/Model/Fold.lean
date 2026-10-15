/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.SequenceLaws

/-!
# Lazy finite left folds

The reference `foldl` selects the final entry of a lazy scan. A finite fold
therefore builds nested suspended applications. In particular, an empty fold
demands neither its function nor its sequence; a function may ignore its
accumulator or the selected element. No strictness is added to the core.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- Fold a prefix, retaining every accumulator and element as a suspended expression. -/
@[expose] def Expr.foldlPrefix {Γ : List ClosedTy} {a b : ClosedTy} {n : Nat}
    (f : Expr Γ (.arrow a (.arrow b a))) (z : Expr Γ a)
    (xs : Expr Γ (.seq (.finite n) b)) : Nat → Expr Γ a
  | 0 => z
  | k + 1 => .app (.app f (foldlPrefix f z xs k)) (.index xs (.integer k))

/-- The independent continuous meaning of the same finite demands. -/
@[expose] noncomputable def Semantics.foldlPrefix {a b : ClosedTy} (n : Nat) : Nat →
    Computation (.arrow a (.arrow b a)) →𝒄
      (Computation a →𝒄 (Computation (.seq (.finite n) b) →𝒄 Computation a))
  | 0 => .ofFun (fun _ => .ofFun (fun z => .ofFun (fun _ => z)))
  | k + 1 => .ofFun (fun f => .ofFun (fun z => .ofFun (fun xs =>
      DomainResult.applyContinuous
        (DomainResult.applyContinuous f (foldlPrefix n k f z xs))
        (indexAt xs k))))

/-- Folding zero elements leaves the seed suspended. -/
@[simp] theorem Semantics.foldlPrefix_zero {a b : ClosedTy} (n : Nat)
    (f : Computation (.arrow a (.arrow b a))) (z : Computation a)
    (xs : Computation (.seq (.finite n) b)) : foldlPrefix n 0 f z xs = z := rfl

/-- One more fold step applies the function to the preceding result and selected element. -/
theorem Semantics.foldlPrefix_succ {a b : ClosedTy} (n k : Nat)
    (f : Computation (.arrow a (.arrow b a))) (z : Computation a)
    (xs : Computation (.seq (.finite n) b)) :
    foldlPrefix n (k + 1) f z xs = DomainResult.applyContinuous
      (DomainResult.applyContinuous f (foldlPrefix n k f z xs)) (indexAt xs k) := rfl

/-- The core expansion preserves the partial meaning, without totality assumptions. -/
theorem Expr.denote_foldlPrefix {Γ : List ClosedTy} {a b : ClosedTy} {n : Nat}
    (f : Expr Γ (.arrow a (.arrow b a))) (z : Expr Γ a)
    (xs : Expr Γ (.seq (.finite n) b)) (k : Nat) (ρ : Environment Γ) :
    (foldlPrefix f z xs k).denote ρ =
      Semantics.foldlPrefix n k (f.denote ρ) (z.denote ρ) (xs.denote ρ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [foldlPrefix, denote_app, denote_index, denote_integer,
        Semantics.foldlPrefix_succ, ih, Semantics.indexAt]

end Interop.Cryptol
