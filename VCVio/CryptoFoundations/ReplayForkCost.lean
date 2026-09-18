/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.ReplayFork
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Query bounds for the actual replay fork

The first path executes the original program once. A selected occurrence executes only its
residual a second time. Predicate-targeted query bounds cover both executions, including
rejected forks, without charging pure cursor operations as oracle calls.
-/

public section

open OracleSpec
open PFunctor.FreeM PFunctor.FreeM.Cursor

namespace OracleComp

attribute [local implicit_reducible] PFunctor.FreeM.bind PFunctor.FreeM.map

variable {ι α : Type} {spec : OracleSpec ι}
variable (p : ι → Prop) [DecidablePred p]

private theorem free_map_bound {β : Type} (main : OracleComp spec α) (f : α → β) (N : ℕ) :
    IsQueryBoundP (PFunctor.FreeM.map f main) p N ↔ IsQueryBoundP main p N :=
  PFunctor.FreeM.isRollBound_map_iff _ _ _ _ _

private theorem queryBind_bound (t : ι) (k : spec.Range t → OracleComp spec α) (N : ℕ) :
    IsQueryBoundP (OracleComp.queryBind (spec := spec) t k) p N ↔
      (¬ p t ∨ 0 < N) ∧ ∀ u, IsQueryBoundP (k u) p (if p t then N - 1 else N) := Iff.rfl

/-- Retaining the typed path preserves a program's structural query bound. -/
theorem isQueryBoundP_withPath (main : OracleComp spec α) (N : ℕ) :
    IsQueryBoundP (withPath main) p N ↔ IsQueryBoundP main p N :=
  isQueryBoundP_iff_of_map_eq (PFunctor.FreeM.map_output_withPath main)

private theorem occurrence_residual_bound {main : OracleComp spec α} {target : ι} {n N : ℕ}
    (occ : Occurrence target main n) (h : IsQueryBoundP main p N) :
    IsQueryBoundP (OracleComp.queryBind target occ.resume) p N := by
  induction occ generalizing N with
  | here next => exact h
  | stepSame answer tail ih =>
    have hh := (queryBind_bound p _ _ N).mp h
    exact (ih (hh.2 answer)).mono (by split <;> omega)
  | stepOther hne answer tail ih =>
    have hh := (queryBind_bound p _ _ N).mp h
    exact (ih (hh.2 answer)).mono (by split <;> omega)

/-- Completing any retained occurrence uses no more queries than the original program. -/
theorem isQueryBoundP_occurrence_complete {main : OracleComp spec α} {target : ι} {n N : ℕ}
    (occ : Occurrence target main n) (h : IsQueryBoundP main p N) :
    IsQueryBoundP occ.complete p N := by
  have hr := occurrence_residual_bound p occ h
  change IsQueryBoundP (OracleComp.queryBind target _) p N
  rw [queryBind_bound] at hr ⊢
  refine ⟨hr.1, fun answer => ?_⟩
  rw [free_map_bound, isQueryBoundP_withPath]
  exact hr.2 answer

/-- The actual selected replay fork uses at most twice the source program's query budget.
The bound holds on every branch, including an absent selector or a rejected fork. -/
theorem isQueryBoundP_contextFork [spec.DecidableEq]
    (main : OracleComp spec α) (qb : ι → ℕ) (target : ι)
    (select : α → Option (Fin (qb target + 1))) (N : ℕ)
    (h : IsQueryBoundP main p N) :
    IsQueryBoundP (contextFork main qb target select) p (N + N) := by
  unfold contextFork contextForkWitness filterMapLocateAndForkSelected
    locateAndForkSelected locateAndForkBy
  simp only [free_map_bound]
  apply isQueryBoundP_bind ((isQueryBoundP_withPath p main N).mpr h)
  intro path _
  cases select (PFunctor.FreeM.output main path) with
  | none => simp
  | some k =>
    cases hloc : locateAt? target main path k.val with
    | none => simp [hloc]
    | some located =>
      simp only [hloc, free_map_bound, Located.fork_eq_map_complete]
      exact isQueryBoundP_occurrence_complete p located.occurrence h

end OracleComp
