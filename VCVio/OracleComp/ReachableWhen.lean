/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.Support
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import PolyFun.PFunctor.Free.WP

/-!
# Reachability with restricted oracle answers

`reachableWhen` interprets an oracle program using a specified set of possible answers for each
query. The public equations describe pure, query, bind, and monotone enlargement of answer sets.
-/

public section

open OracleSpec
open scoped OracleSpec.PrimitiveQuery

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β : Type v}

section supportWhen

/-- Outputs reachable when a query may return any response selected by `o`. -/
def reachableWhen (o : QueryImpl spec Set) (mx : OracleComp spec α) : Set α :=
  PFunctor.FreeM.reachableUnder (P := spec.toPFunctor)
    (fun (t : spec.Domain) (u : spec.Range t) ↦ u ∈ o t) mx

@[simp]
lemma reachableWhen_pure (o : QueryImpl spec Set) (x : α) :
    reachableWhen o (pure x : OracleComp spec α) = {x} := by
  simp [reachableWhen]

@[simp]
lemma reachableWhen_liftM (o : QueryImpl spec Set) (q : OracleQuery spec α) :
    reachableWhen o (liftM q : OracleComp spec α) = q.cont '' o q.input := by
  change (PFunctor.FreeM.liftObj q).reachableUnder
    (fun (t : spec.Domain) (u : spec.Range t) ↦ u ∈ o t) = q.cont '' o q.input
  exact (PFunctor.FreeM.reachableUnder_liftObj (P := spec.toPFunctor)
    (fun (t : spec.Domain) (u : spec.Range t) ↦ u ∈ o t) q)

lemma reachableWhen_query (o : QueryImpl spec Set) (t : spec.Domain) :
    reachableWhen o (query t : OracleComp spec _) = o t := by
  simp [OracleSpec.query]

@[simp]
lemma reachableWhen_bind (o : QueryImpl spec Set) (oa : OracleComp spec α)
    (ob : α → OracleComp spec β) :
    reachableWhen o (oa >>= ob) =
      ⋃ x ∈ reachableWhen o oa, reachableWhen o (ob x) := by
  exact PFunctor.FreeM.reachableUnder_bind _ oa ob

lemma reachableWhen_query_bind (o : QueryImpl spec Set) (t : spec.Domain)
    (next : spec.Range t → OracleComp spec α) :
    reachableWhen o ((query t : OracleComp spec _) >>= next) =
      ⋃ direction ∈ o t, reachableWhen o (next direction) := by
  simp

@[gcongr]
lemma reachableWhen_mono {o₁ o₂ : QueryImpl spec Set}
    (h : ∀ q, o₁ q ⊆ o₂ q) (oa : OracleComp spec α) :
    reachableWhen o₁ oa ⊆ reachableWhen o₂ oa := by
  exact PFunctor.FreeM.reachableUnder_mono (fun q u hu ↦ h q hu) oa

/-- Admitting every typed response recovers the free tree's attachment support. -/
theorem reachableWhen_univ_eq_support (oa : OracleComp spec α) :
    reachableWhen (fun _ ↦ Set.univ) oa = support oa := by
  simpa [reachableWhen, PFunctor.FreeM.reachable] using
    (PFunctor.FreeM.reachable_eq_support oa)

/-- The `SetM` interpretation of possible outputs under a query-response assignment. -/
@[deprecated "VCVio retiring support API: use reachableWhen" (since := "2026-09-14")]
def supportWhen (o : QueryImpl spec Set) (mx : OracleComp spec α) : Set α :=
  SetM.run (simulateQ (r := SetM) (fun t => SetM.ofSet (o t)) mx)

@[deprecated "VCVio retiring support API: use reachableWhen_pure" (since := "2026-09-14"), simp]
lemma supportWhen_pure (o : QueryImpl spec Set) (x : α) :
    supportWhen o (pure x : OracleComp spec α) = {x} := by
  unfold supportWhen
  rw [simulateQ_pure, SetM.run_pure]

@[deprecated "VCVio retiring support API: use reachableWhen_query_bind"
  (since := "2026-09-14")]
lemma supportWhen_query_bind (o : QueryImpl spec Set) (q : spec.Domain)
    (oa : spec.Range q → OracleComp spec α) :
    supportWhen o ((query q : OracleComp spec _) >>= oa) =
      ⋃ x ∈ o q, supportWhen o (oa x) := by
  unfold supportWhen
  rw [simulateQ_bind, simulateQ_spec_query, SetM.run_bind, SetM.run_ofSet]

/-- Reachable outputs of a bind are the reachable outputs of the continuation over reachable
outputs of the first computation. -/
@[deprecated "VCVio retiring support API: use reachableWhen_bind" (since := "2026-09-14"), simp]
lemma supportWhen_bind (o : QueryImpl spec Set) (oa : OracleComp spec α)
    (ob : α → OracleComp spec β) :
    supportWhen o (oa >>= ob) = ⋃ x ∈ supportWhen o oa, supportWhen o (ob x) := by
  unfold supportWhen
  rw [simulateQ_bind, SetM.run_bind]

/-- Membership form of [`OracleComp.supportWhen_bind`]. -/
@[deprecated "VCVio retiring support API: use reachableWhen_bind" (since := "2026-09-14")]
lemma mem_supportWhen_bind_iff (o : QueryImpl spec Set) (oa : OracleComp spec α)
    (ob : α → OracleComp spec β) (y : β) :
    y ∈ supportWhen o (oa >>= ob) ↔
      ∃ x ∈ supportWhen o oa, y ∈ supportWhen o (ob x) := by
  simp [supportWhen_bind]

/-- Enlarging the set of possible oracle outputs only enlarges the reachable output set. -/
@[deprecated "VCVio retiring support API: use reachableWhen_mono" (since := "2026-09-14"),
  gcongr]
lemma supportWhen_mono {o₁ o₂ : QueryImpl spec Set}
    (h : ∀ q, o₁ q ⊆ o₂ q) (oa : OracleComp spec α) :
    supportWhen o₁ oa ⊆ supportWhen o₂ oa := by
  intro y hy
  induction oa using OracleComp.inductionOn generalizing y with
  | pure x =>
      simpa [supportWhen_pure] using hy
  | query_bind q oa ih =>
      simp only [supportWhen_query_bind, Set.mem_iUnion, exists_prop] at hy ⊢
      rcases hy with ⟨u, hu, hy⟩
      exact ⟨u, h q hu, ih u hy⟩

/-- The `SetM` interpretation agrees with operation-indexed reachability. -/
@[deprecated "VCVio retiring support API: use reachableWhen" (since := "2026-09-15")]
theorem supportWhen_eq_reachableWhen (o : QueryImpl spec Set) (oa : OracleComp spec α) :
    supportWhen o oa = reachableWhen o oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q next ih =>
      simp only [supportWhen_query_bind, reachableWhen_bind, reachableWhen_query, ih]

end supportWhen

end OracleComp
