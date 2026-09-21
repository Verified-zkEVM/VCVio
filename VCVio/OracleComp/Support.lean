/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.OracleComp
public import VCVio.EvalDist.Monad.Support
public import PolyFun.PFunctor.Free.Support

/-!
# Possible outputs of oracle programs

Oracle-facing equations for PolyFun's native attachment semantics. Possible outputs are
structural: this API imposes no probabilistic interpretation or positivity assumption on answers.
-/

public section

universe u v w

open OracleSpec
open scoped OracleSpec.PrimitiveQuery

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β : Type w}

@[simp, grind =] lemma support_liftM (q : OracleQuery spec α) :
    support (liftM q : OracleComp spec α) = Set.range q.cont := by
  exact PFunctor.FreeM.support_liftObj (P := spec.toPFunctor) q

@[grind =] lemma support_query (t : spec.Domain) :
    support (query t : OracleComp spec _) = Set.univ := by
  rw [support_liftM]; exact Set.range_id

/-- Mapping a free oracle tree maps its reachable outputs. -/
lemma support_freeM_map (f : α → β) (mx : OracleComp spec α) :
    support (PFunctor.FreeM.map f mx) = f '' support mx := by
  exact PFunctor.FreeM.support_map f mx

lemma mem_support_liftM_iff (q : OracleQuery spec α) (u : α) :
    u ∈ support (liftM q : OracleComp spec α) ↔ ∃ t, q.cont t = u := by
  rw [support_liftM]; exact Set.mem_range

lemma mem_support_query (t : spec.Domain) (u : spec.Range t) :
    u ∈ support (query t : OracleComp spec _) := by
  rw [support_query]; trivial

/-- An oracle computation has a reachable output when every query has an answer. -/
theorem support_nonempty [∀ t, Nonempty (spec.Range t)] (mx : OracleComp spec α) :
    (support mx).Nonempty :=
  PFunctor.FreeM.support_nonempty mx

alias support_liftM_query := support_query

/-- Support-aware bind congruence: if two continuations agree on all elements in the support
    of `mx`, the resulting bind computations are equal. -/
theorem bind_congr_of_forall_mem_support (mx : OracleComp spec α) {f g : α → OracleComp spec β}
    (h : ∀ x ∈ support mx, f x = g x) : mx >>= f = mx >>= g :=
  MonadAttach.bind_congr_of_forall_mem_support mx h

@[grind .]
lemma support_finite [∀ t, Finite (spec.Range t)] (mx : OracleComp spec α) : (support mx).Finite :=
  PFunctor.FreeM.support_finite mx


section finSupport

variable {α : Type v} [∀ t, Fintype (spec.Range t)]

/-- Finite version of support for when oracles have a finite set of possible outputs.
NOTE: we can't use `simulateQ` because `Finset` lacks a `Monad` instance. -/
instance : HasEvalFinset (fun α : Type v ↦ OracleComp spec α) where
  finSupport {α} _ mx := OracleComp.construct (C := fun _ ↦ Finset α)
    (fun x => {x}) (fun _ _ r => Finset.univ.biUnion r) mx
  coe_finSupport {α} _ mx := by
    induction mx using OracleComp.inductionOn with
    | pure x => simp
    | query_bind t mx h => simp [h]

@[simp, grind =] lemma finSupport_liftM [DecidableEq α] (q : OracleQuery spec α) :
    finSupport (liftM q : OracleComp spec α) = Finset.univ.image q.cont := by grind

lemma finSupport_query (t : spec.Domain) [DecidableEq (spec.Range t)] :
    finSupport (query t : OracleComp spec _) = Finset.univ := by grind

lemma mem_finSupport_liftM_iff [DecidableEq α] (q : OracleQuery spec α) (x : α) :
    x ∈ finSupport (liftM q : OracleComp spec α) ↔ ∃ t, q.cont t = x := by simp

lemma mem_finSupport_query (t : spec.Domain) [DecidableEq (spec.Range t)] (u : spec.Range t) :
    u ∈ finSupport (query t : OracleComp spec _) := by grind

end finSupport

end OracleComp
