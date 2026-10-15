/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.Finite.Basic
public import Interop.Cryptol.Model.Words

/-!
# Representation of native values in lazy domains

The relation is structural at data types. At function types it requires
preservation of represented arguments, including the returned result.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Finite

/-- Full representation at base types; functions preserve represented arguments. -/
@[expose] noncomputable def Represents : (a : Ty) → a.Native → Computation a.core → Prop
  | .bit, b, d => d = .value ⟨b⟩
  | .word _, x, d => d = .value (wordValue x)
  | .prod a b, x, d => ∃ dx dy, d = .value (dx, dy) ∧
      Represents a x.1 dx ∧ Represents b x.2 dy
  | .seq _ a, xs, d => ∃ ds, d = .value ds ∧ ∀ i, Represents a (xs i) (ds i)
  | .arrow a b, f, d => ∃ g : Computation a.core →𝒄 Computation b.core,
      d = .value g ∧ ∀ x dx, Represents a x dx → Represents b (f x) (g dx)

/-- Extending represented sequences retains every old coordinate and the new entry. -/
theorem Represents.snoc {a : Ty} {n : Nat} {xs : Fin n → a.Native} {x : a.Native}
    {ds : Fin n → Computation a.core} {d : Computation a.core}
    (hs : ∀ i, Represents a (xs i) (ds i)) (hx : Represents a x d) :
    Represents (.seq (n + 1) a) (Fin.snoc xs x) (.value (Fin.snoc ds d)) := by
  refine ⟨_, rfl, fun i => ?_⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using hx
  · simpa only [Fin.snoc_castSucc] using hs j

/-- Native and core environments agree at every variable. -/
@[expose] def EnvRepresents {Γ : List Ty} (ρ : Env Γ)
    (η : Environment (Γ.map Ty.core)) : Prop :=
  ∀ a v, Represents a (ρ a v) (η a.core (lowerVar v))

/-- Extending both environments preserves their relation. -/
theorem EnvRepresents.extend {Γ : List Ty} {a : Ty} {ρ : Env Γ}
    {η : Environment (Γ.map Ty.core)} (h : EnvRepresents ρ η)
    {x : a.Native} {dx : Computation a.core} (hx : Represents a x dx) :
    EnvRepresents (ρ.extend x) (η.extend dx) := by
  intro b v
  cases v with
  | zero => exact hx
  | succ v => exact h _ v

/-- The empty environments agree. -/
theorem envRepresents_empty : EnvRepresents Env.empty Environment.empty := by
  intro a v
  exact nomatch v

end Interop.Cryptol.Finite
