/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Control.Basic

/-!
# `Fin`-indexed monadic sequencing

`Fin.mOfFn`: run a `Fin n`-indexed family of monadic computations in order and collect the
results as a function.
`Fintype.mPi` transports this construction to any finite index type.
-/

public section

universe u v w

/-- Monadic analog of `Fin.ofFn`: given `f : Fin n → m α`, runs each computation
in order and collects the results as a function `Fin n → α`. This is the
`Fin n → α` counterpart of Mathlib's `Vector.mOfFn`. -/
@[expose]
def Fin.mOfFn {m : Type u → Type v} [Monad m] {α : Type u} :
    (n : ℕ) → (Fin n → m α) → m (Fin n → α)
  | 0, _ => return Fin.elim0
  | n + 1, f => do
    let a ← f 0
    let rest ← Fin.mOfFn n (fun i ↦ f i.succ)
    return Fin.cons a rest

/-- Run a finite family of monadic computations and collect their results as a function. -/
@[expose]
noncomputable def Fintype.mPi {α : Type u} {m : Type u → Type v} [Monad m]
    {ι : Type} [Fintype ι] (f : ι → m α) : m (ι → α) :=
  (Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl α)) <$>
    Fin.mOfFn (Fintype.card ι) fun k ↦ f ((Fintype.equivFin ι).symm k)

/-- Sequence a successor-indexed family by pairing its head with its tail. -/
theorem Fin.mOfFn_succ_eq_map_pair {α : Type u} {m : Type u → Type v}
    [Monad m] [LawfulMonad m] (n : ℕ) (g : Fin (n + 1) → m α) :
    Fin.mOfFn (n + 1) g = (fun z : α × (Fin n → α) ↦ (Fin.cons z.1 z.2 : Fin (n + 1) → α)) <$>
      (do let a ← g 0; let rest ← Fin.mOfFn n fun i ↦ g i.succ; return (a, rest)) := by
  simp [Fin.mOfFn, monad_norm]

/-- Coordinate observations commute with finite monadic sequencing. -/
theorem Fin.mOfFn_map {α β : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (n : ℕ) (g : Fin n → m α) (f : Fin n → α → β) :
    (fun v i ↦ f i (v i)) <$> Fin.mOfFn n g = Fin.mOfFn n (fun i ↦ f i <$> g i) := by
  induction n with
  | zero =>
      simp only [Fin.mOfFn, map_pure]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [Fin.mOfFn, map_bind, bind_map_left, map_pure]
      apply bind_congr
      intro a
      rw [← ih]
      simp only [bind_map_left]
      apply bind_congr
      intro rest
      congr 1
      funext i
      exact Fin.cases rfl (fun _ ↦ rfl) i

/-- Coordinate observations commute with sequencing over a finite index type. -/
theorem Fintype.mPi_map {α β : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {ι : Type} [Fintype ι] (g : ι → m α) (f : ι → α → β) :
    (fun v i ↦ f i (v i)) <$> Fintype.mPi g = Fintype.mPi (fun i ↦ f i <$> g i) := by
  simp only [Fintype.mPi]
  rw [← Fin.mOfFn_map]
  simp only [Functor.map_map]
  congr 1
  funext w i
  simp [Function.comp_def, Equiv.arrowCongr]
