/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Std.Tactic.Do
public import Std.WP
public import ToMathlib.Control.Monad.Fold

/-!
# The finite monadic family as a loop

`Fin.mOfFn n f` runs `f 0`, …, `f (n - 1)` in order and collects the results as a function. Its
`vcgen` rule carries an invariant on the results collected so far, indexed by their number, as
`Std.WP.Spec.mapM_list` carries one on the prefix of a list: the step at index `k` sees the
first `k` results and extends them by its own.
-/

public section

open Std.WP

universe u v w z

namespace Fin

/-- An invariant of `Fin.mOfFn`: an assertion on the first `k` results, for every `k`. `vcgen`'s
`invariants` clause fills it. -/
@[expose, spec_invariant_type, simp, grind =]
def MOfFnInvariant (α : Type u) (Pred : Type w) := (k : ℕ) → (Fin k → α) → Pred

variable {m : Type u → Type v} [Monad m] {Pred : Type w} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α : Type u}

/-- The loop rule of `Fin.mOfFn`: if the step at index `k`, from the first `k` results, ends with
them extended by its own, then the family, from no results, ends with all `n`. -/
@[spec]
theorem _root_.Std.WP.Spec.mOfFn (n : ℕ) (f : Fin n → m α) (inv : MOfFnInvariant α Pred)
    {epost : EPred}
    (hstep : ∀ (k : ℕ) (hk : k < n) (v : Fin k → α),
      ⦃ inv k v ⦄ f ⟨k, hk⟩ ⦃ fun a => inv (k + 1) (Fin.snoc v a); epost ⦄) :
    ⦃ inv 0 Fin.elim0 ⦄ Fin.mOfFn n f ⦃ fun v => inv n v; epost ⦄ := by
  induction n generalizing inv with
  | zero => exact Triple.pure _ Lean.Order.PartialOrder.rel_refl
  | succ n ih =>
    simp only [Fin.mOfFn]
    refine Triple.bind _ _ _ (hstep 0 (Nat.succ_pos n) Fin.elim0) fun a => ?_
    have h1 : (Fin.snoc (α := fun _ => α) Fin.elim0 a : Fin 1 → α) =
        Fin.cons (α := fun _ => α) a Fin.elim0 :=
      funext fun i => by obtain ⟨i, hi⟩ := i; obtain rfl : i = 0 := (by omega); rfl
    rw [h1]
    refine Triple.bind _ _ _
      (ih (fun i => f i.succ) (fun k w => inv (k + 1) (Fin.cons a w)) fun k hk w => ?_)
      fun rest => Triple.pure _ Lean.Order.PartialOrder.rel_refl
    simp only [Fin.cons_snoc_eq_snoc_cons]
    exact hstep (k + 1) (Nat.succ_lt_succ hk) (Fin.cons a w)

end Fin
