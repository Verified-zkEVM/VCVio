/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import ToMathlib.Control.WriterT.Map
public import ToMathlib.Control.StateT

/-!
# Append writers accumulated in product state

The existing state transformer retains the service state and chronological emitted suffix.
-/

public section

universe u v

/-- Put the writer's emitted suffix after the initial log in a product state. -/
@[expose] def WriterT.appendToState
    {m : Type u → Type v} [Monad m] {σ ω α : Type u} [Append ω]
    (body : WriterT ω (StateT σ m) α) : StateT (σ × ω) m α :=
  StateT.mk fun initial =>
    (fun output => (output.1.1, (output.2, initial.2 ++ output.1.2))) <$>
      body.run.run initial.1

/-- A pure writer computation preserves both components of the product state. -/
theorem WriterT.appendToState_pure
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ ω α : Type u}
    [EmptyCollection ω] [Append ω] [LawfulAppend ω] (value : α) :
    WriterT.appendToState (pure value : WriterT ω (StateT σ m) α) = pure value := by
  apply StateT.ext
  intro initial
  simp [WriterT.appendToState]

/-- Writer sequencing appends its two emitted suffixes in the original order. -/
theorem WriterT.appendToState_bind
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ ω α β : Type u}
    [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (body : WriterT ω (StateT σ m) α) (next : α → WriterT ω (StateT σ m) β) :
    WriterT.appendToState (body >>= next) =
      (WriterT.appendToState body >>= fun value => WriterT.appendToState (next value)) := by
  apply StateT.ext
  intro initial
  simp only [WriterT.appendToState, StateT.run_mk, WriterT.run_bind', StateT.run_bind,
    StateT.run_map, map_bind, bind_map_left, Functor.map_map]
  apply bind_congr
  intro first
  simp only [Prod.map, id_eq, LawfulAppend.append_assoc]

/-- Append accumulation is a monad morphism into the existing product-state transformer. -/
@[expose] def WriterT.appendToStateHom
    {m : Type u → Type v} [Monad m] [LawfulMonad m] {σ ω : Type u}
    [EmptyCollection ω] [Append ω] [LawfulAppend ω] :
    WriterT ω (StateT σ m) →ᵐ StateT (σ × ω) m where
  toFun {_α} body := WriterT.appendToState body
  toFun_pure' := WriterT.appendToState_pure
  toFun_bind' := WriterT.appendToState_bind
