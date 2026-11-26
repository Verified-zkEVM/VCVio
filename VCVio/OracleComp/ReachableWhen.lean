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

section reachableWhen

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

@[gcongr only]
lemma reachableWhen_mono {o₁ o₂ : QueryImpl spec Set}
    (h : ∀ q, o₁ q ⊆ o₂ q) (oa : OracleComp spec α) :
    reachableWhen o₁ oa ⊆ reachableWhen o₂ oa := by
  exact PFunctor.FreeM.reachableUnder_mono (fun q u hu ↦ h q hu) oa

/-- Admitting every typed response recovers the free tree's attachment support. -/
theorem reachableWhen_univ_eq_support (oa : OracleComp spec α) :
    reachableWhen ⟨fun _ ↦ Set.univ⟩ oa = support oa := by
  simpa [reachableWhen, PFunctor.FreeM.reachable] using
    (PFunctor.FreeM.reachable_eq_support oa)

end reachableWhen

end OracleComp
