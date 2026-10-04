/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Monad.UniformTable

/-!
# Uniform tables with different answer spaces

A finite family of nonempty finite answer spaces supports independent resampling of any cell.
The laws preserve complete joint observations, including entries that a client has not read.
-/

public section

open MeasureTheory ProbabilityTheory

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]
  {D α : Type} {R : D → Type} [Finite D] [DecidableEq D]
  [∀ d, Finite (R d)] [∀ d, Nonempty (R d)]
  [∀ d, MeasurableSpace (R d)] [∀ d, MeasurableSingletonClass (R d)] [MeasurableSpace α]

/-- Resample one dependent table cell before any computation, preserving its output measure. -/
theorem evalDist_bind_bind_update_dependent (t : D) (value : m (R t)) (table : m (∀ d, R d))
    (hvalue : 𝒟[value] = uniformOn Set.univ) (htable : 𝒟[table] = uniformOn Set.univ)
    (f : (∀ d, R d) → m α) :
    𝒟[value >>= fun u => table >>= fun g => f (Function.update g t u)] = 𝒟[table >>= f] := by
  have hupdate : 𝒟[value >>= fun u => (fun g => Function.update g t u) <$> table] =
      𝒟[table] := by
    simp_rw [evalDist_bind_of_discrete, evalDist_map_of_discrete, hvalue, htable]
    exact uniformOn_univ_bind_map_update_dependent t
  have hbind : (value >>= fun u => table >>= fun g => f (Function.update g t u)) =
      (value >>= fun u => (fun g => Function.update g t u) <$> table) >>= f := by
    simp only [bind_assoc, bind_map_left]
  rw [hbind, evalDist_bind_of_discrete _ f, hupdate, ← evalDist_bind_of_discrete]

/-- Resampling a dependent table cell preserves every pure observation of the table. -/
theorem evalDist_bind_bind_update_map_dependent (t : D) (value : m (R t)) (table : m (∀ d, R d))
    (hvalue : 𝒟[value] = uniformOn Set.univ) (htable : 𝒟[table] = uniformOn Set.univ)
    (f : (∀ d, R d) → α) :
    𝒟[value >>= fun u => table >>= fun g => pure (f (Function.update g t u))] =
      𝒟[table >>= fun g => pure (f g)] :=
  evalDist_bind_bind_update_dependent t value table hvalue htable (fun g => pure (f g))
