/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.Set.Functor

/-!
# Equations for the set monad wrapper

This file exposes the `pure`, `bind`, and `map` equations for `SetM` through
`SetM.run`. Keeping these equations at the wrapper boundary lets clients reason
about the monad without relying on reduction through its bundled instance.
-/

public section

universe u

namespace SetM

/-- Regard a set as a computation in the `SetM` wrapper. -/
@[expose] protected def ofSet {α : Type u} (s : Set α) : SetM α := s

@[simp]
lemma run_ofSet {α : Type u} (s : Set α) : SetM.run (SetM.ofSet s) = s := rfl

@[simp]
lemma liftM_self {α : Type u} (s : SetM α) : (liftM s : SetM α) = s :=
  monadLift_self s

@[simp]
lemma run_pure {α : Type u} (x : α) : SetM.run (pure x : SetM α) = {x} :=
  Set.pure_def x

@[simp]
lemma run_bind {α β : Type u} (s : SetM α) (f : α → SetM β) :
    SetM.run (s >>= f) = ⋃ x ∈ SetM.run s, SetM.run (f x) :=
  Set.bind_def

@[simp]
lemma run_map {α β : Type u} (f : α → β) (s : SetM α) :
    SetM.run (f <$> s) = f '' SetM.run s :=
  Set.fmap_eq_image f

end SetM
