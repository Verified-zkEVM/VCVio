/-
Copyright (c) 2026 Nicolas Consigny, Alexander Hicks, Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Alexander Hicks, Matthias Meijers
-/

module
public import PolyFun.Control.Monad.Hom
import Lean.Elab.Tactic.Omega

/-!
# Position-dependent iteration

A chain calls its step function at consecutive natural-number positions, beginning at `start`.
The step function carries any address encoding or index shift. Both final-step and first-step
recurrences are available, so callback effects retain the same order under either view.
-/

public section

namespace VCVio.Algorithms.IndexedChain

universe u v w

/-- Run `steps` consecutive callbacks, starting at the supplied position. -/
@[expose] def chainM {H : Type u} {m : Type u → Type v} [Monad m]
    (step : Nat → H → m H) (start : Nat) : Nat → H → m H
  | 0, x => pure x
  | steps + 1, x => do
      let y ← chainM step start steps x
      step (start + steps) y

@[simp] theorem chainM_zero {H : Type u} {m : Type u → Type v} [Monad m]
    (step : Nat → H → m H) (start : Nat) (x : H) : chainM step start 0 x = pure x := rfl

/-- The final callback has position `start + steps`. -/
theorem chainM_succ {H : Type u} {m : Type u → Type v} [Monad m]
    (step : Nat → H → m H) (start steps : Nat) (x : H) :
    chainM step start (steps + 1) x = chainM step start steps x >>= step (start + steps) := rfl

/-- Splitting a chain preserves the sequence of effects and its final value. -/
theorem chainM_add {H : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (step : Nat → H → m H) (start first second : Nat) (x : H) :
    chainM step start (first + second) x =
      chainM step start first x >>= chainM step (start + first) second := by
  induction second with
  | zero => simp [chainM]
  | succ second ih => simp [chainM, ih, bind_assoc, Nat.add_assoc]

/-- The first callback has position `start`, followed by the remaining callbacks. -/
theorem chainM_succ_left {H : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (step : Nat → H → m H) (start steps : Nat) (x : H) :
    chainM step start (steps + 1) x =
      step start x >>= chainM step (start + 1) steps := by
  simpa [chainM, Nat.one_add] using chainM_add step start 1 steps x

/-- A monad morphism transports a chain when it transports every callback. -/
theorem chainM_natural {H : Type u} {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Monad n] (F : m →ᵐ n) (step₁ : Nat → H → m H) (step₂ : Nat → H → n H)
    (hstep : ∀ j x, F (step₁ j x) = step₂ j x) (start steps : Nat) (x : H) :
    F (chainM step₁ start steps x) = chainM step₂ start steps x := by
  induction steps with
  | zero => exact F.mmap_pure x
  | succ steps ih => simp only [chainM_succ, F.mmap_bind, ih, hstep]

/-- Callback agreement is needed only at the positions visited by this chain. -/
theorem chainM_congr {H : Type u} {m : Type u → Type v} [Monad m]
    (step₁ step₂ : Nat → H → m H) (start steps : Nat) (x : H)
    (hstep : ∀ j, start ≤ j → j < start + steps → ∀ y, step₁ j y = step₂ j y) :
    chainM step₁ start steps x = chainM step₂ start steps x := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [chainM_succ, chainM_succ, ih (by intros; apply hstep <;> omega)]
    congr 1
    funext y
    exact hstep _ (by omega) (by omega) y

/-- A bind-closed predicate holds for a chain when it holds for every visited callback. -/
theorem chainM_pred {H : Type u} {m : Type u → Type v} [Monad m]
    (Q : ∀ {α : Type u}, m α → Prop) (hpure : ∀ {α : Type u} (x : α), Q (pure x))
    (hbind : ∀ {α β : Type u} (oa : m α) (ob : α → m β),
      Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))
    (step : Nat → H → m H) (start : Nat) (x : H) :
    ∀ steps, (∀ j < steps, ∀ y, Q (step (start + j) y)) → Q (chainM step start steps x)
  | 0, _ => hpure _
  | steps + 1, h =>
    hbind _ _ (chainM_pred Q hpure hbind step start x steps
      (fun j hj => h j (by omega))) (fun y => h steps (by omega) y)

/-- Pure position-dependent iteration, using the identity interpretation of `chainM`. -/
@[expose] def chain {H : Type u} (step : Nat → H → H) (start steps : Nat) (x : H) : H :=
  chainM (m := Id) step start steps x

@[simp] theorem chain_zero {H : Type u} (step : Nat → H → H) (start : Nat) (x : H) :
    chain step start 0 x = x := rfl

/-- The pure chain's final callback. -/
theorem chain_succ {H : Type u} (step : Nat → H → H) (start steps : Nat) (x : H) :
    chain step start (steps + 1) x = step (start + steps) (chain step start steps x) := rfl

/-- Pure chain composition is the identity specialization of monadic composition. -/
theorem chain_add {H : Type u} (step : Nat → H → H) (start first second : Nat) (x : H) :
    chain step start (first + second) x =
      chain step (start + first) second (chain step start first x) :=
  chainM_add (m := Id) step start first second x

/-- Pure chains agree when callbacks agree on the visited positions. -/
theorem chain_congr {H : Type u} (step₁ step₂ : Nat → H → H) (start steps : Nat) (x : H)
    (hstep : ∀ j, start ≤ j → j < start + steps → ∀ y, step₁ j y = step₂ j y) :
    chain step₁ start steps x = chain step₂ start steps x :=
  chainM_congr (m := Id) step₁ step₂ start steps x hstep

end VCVio.Algorithms.IndexedChain
