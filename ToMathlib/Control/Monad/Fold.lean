/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToCslib.Data.Fin.MOfFn
public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Control.Basic
public import PolyFun.Control.Monad.Hom

/-!
# `Fin`-indexed monadic sequencing

`Fin.mOfFn`: run a `Fin n`-indexed family of monadic computations in order and collect the
results as a function.
`Fintype.mPi` transports this construction to any finite index type; over an index type with one
element it is the computation at that element (`Fintype.mPi_unique`). Both commute with monad
morphisms (`MonadHom.mmap_mOfFn`, `MonadHom.mmap_mPi`).
-/

public section

universe u v w

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

/-- A finite family of computations over an index type with one element is the computation at
that element. -/
theorem Fintype.mPi_unique {α : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {ι : Type} [Fintype ι] [Unique ι] (g : ι → m α) :
    Fintype.mPi g = (fun a _ => a) <$> g default := by
  unfold Fintype.mPi
  generalize Fintype.equivFin ι = e
  have hn : Fintype.card ι = 1 := Fintype.card_unique
  revert e
  rw [hn]
  intro e
  simp only [Fin.mOfFn, map_bind, map_pure]
  rw [show e.symm 0 = default from Subsingleton.elim _ _, map_eq_bind_pure_comp]
  refine bind_congr fun a => ?_
  rw [pure_bind]
  congr 1
  funext i
  simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, Equiv.symm_symm]
  rw [show e i = 0 from Subsingleton.elim _ _]
  rfl

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

/-- Sequencing a finite family commutes with monad morphisms. -/
theorem MonadHom.mmap_mOfFn {m : Type u → Type v} {n : Type u → Type w} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (φ : m →ᵐ n) {α : Type u} :
    ∀ {k : ℕ} (f : Fin k → m α), φ (Fin.mOfFn k f) = Fin.mOfFn k fun i => φ (f i)
  | 0, f => by simp [Fin.mOfFn]
  | k + 1, f => by
      simp only [Fin.mOfFn, φ.mmap_bind, φ.mmap_pure]
      congr 1
      funext a
      have ih := MonadHom.mmap_mOfFn φ (fun i => f i.succ)
      simp only at ih
      rw [ih]

/-- Running a finite family of computations independently commutes with monad morphisms. -/
theorem MonadHom.mmap_mPi {m : Type u → Type v} {n : Type u → Type w} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (φ : m →ᵐ n) {α : Type u} {ι : Type} [Fintype ι] (f : ι → m α) :
    φ (Fintype.mPi f) = Fintype.mPi fun i => φ (f i) := by
  simp only [Fintype.mPi, MonadHom.mmap_map, MonadHom.mmap_mOfFn]
