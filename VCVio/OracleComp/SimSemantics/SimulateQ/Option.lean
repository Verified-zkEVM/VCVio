/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Simulation into the `Option` monad

Success characterisations for `simulateQ` with an `Option`-valued query implementation: a
simulated `pure`, `bind`, `map` or `Vector.ofFnM` returns `some` exactly when every stage does,
at the components of the result. The transport `simulateQ_ofFnM`, which commutes `simulateQ`
with `Vector.ofFnM`, holds for every lawful target monad, and `Vector.ofFnM_eq_some_iff`
characterises `Vector.ofFnM` into `Option` on its own.
-/

public section

universe u v

namespace Vector

/-- `Vector.ofFnM` into `Option` succeeds exactly when every entry succeeds, at the entries of
the result. -/
theorem ofFnM_eq_some_iff {α : Type u} {n : ℕ} {f : Fin n → Option α} {v : Vector α n} :
    Vector.ofFnM f = some v ↔ ∀ i, f i = some v[i] := by
  induction n with
  | zero => simp [Vector.eq_empty (xs := v)]
  | succ n ih =>
    obtain ⟨as, a, rfl⟩ := Vector.exists_push (xs := v)
    simp [Vector.ofFnM_succ, Option.bind_eq_some_iff, ih, Fin.forall_fin_succ', Vector.push_eq_push]

end Vector

namespace OracleComp

variable {ι : Type v} {spec : OracleSpec ι} {α β : Type u}

/-- A simulated `bind` in `Option` succeeds exactly when the prefix succeeds and the
continuation succeeds at the prefix's value. -/
theorem simulateQ_bind_eq_some_iff (impl : QueryImpl spec Option) (oa : OracleComp spec α)
    (f : α → OracleComp spec β) {b : β} :
    simulateQ impl (oa >>= f) = some b ↔
      ∃ a, simulateQ impl oa = some a ∧ simulateQ impl (f a) = some b := by
  rw [simulateQ_bind]; exact Option.bind_eq_some_iff

/-- A simulated `pure a` in `Option` is `some b` exactly when `a = b`. -/
theorem simulateQ_pure_eq_some_iff (impl : QueryImpl spec Option) (a : α) {b : α} :
    simulateQ impl (pure a : OracleComp spec α) = some b ↔ a = b := by
  simp

/-- A simulated `map` in `Option` succeeds exactly when the computation succeeds at a preimage
of the result. -/
theorem simulateQ_map_eq_some_iff (impl : QueryImpl spec Option) (oa : OracleComp spec α)
    (g : α → β) {b : β} :
    simulateQ impl (g <$> oa) = some b ↔ ∃ a, simulateQ impl oa = some a ∧ g a = b := by
  rw [simulateQ_map, Option.map_eq_map, Option.map_eq_some_iff]

/-- `simulateQ` commutes with `Vector.ofFnM`, for every lawful target monad. -/
@[simp]
theorem simulateQ_ofFnM {r : Type u → Type*} [Monad r] [LawfulMonad r] (impl : QueryImpl spec r)
    {n : ℕ} (g : Fin n → OracleComp spec α) :
    simulateQ impl (Vector.ofFnM g) = Vector.ofFnM fun i => simulateQ impl (g i) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Vector.ofFnM_succ, ih]

/-- A simulated `Vector.ofFnM` in `Option` succeeds exactly when every component succeeds, at
the entries of the result. -/
theorem simulateQ_ofFnM_eq_some_iff (impl : QueryImpl spec Option) {n : ℕ}
    (g : Fin n → OracleComp spec α) {v : Vector α n} :
    simulateQ impl (Vector.ofFnM g) = some v ↔ ∀ i, simulateQ impl (g i) = some v[i] := by
  rw [simulateQ_ofFnM, Vector.ofFnM_eq_some_iff]

end OracleComp
