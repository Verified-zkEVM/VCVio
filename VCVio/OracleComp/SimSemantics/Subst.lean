/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Substituting oracle programs for queries

`OracleComp.subst impl oa` replaces every query `t` of `oa` with the target program `impl t`.
Its result type may lie in any universe. Because `simulateQ impl` runs in a single monad
`r : Type v → Type w` that also answers the queries, its result type lies in the answer universe
`v`. `subst` needs no such restriction: `OracleComp target` is a free monad, and its bind changes
universes. A program whose result holds data larger than its answers, such as a
query log over a large index type, runs through `subst`.

When the result type lies in the answer universe, `subst` is `simulateQ`
(`OracleComp.subst_eq_simulateQ`). The equations `subst_freeM_bind` and `subst_freeM_map` state
naturality across universes; `subst_bind` and `subst_map` are their monadic forms in one universe.
-/

public section

universe u v w w' u' v'

namespace OracleComp

variable {ι : Type u} {κ : Type u'} {spec : OracleSpec.{u, v} ι}
  {target : OracleSpec.{u', v'} κ}

/-- Replace each query `t` of a program with the target program `impl t`. The result type lies
in any universe. -/
@[expose]
def subst (impl : QueryImpl spec (OracleComp target)) {α : Type w} :
    OracleComp spec α → OracleComp target α
  | PFunctor.FreeM.pure x => PFunctor.FreeM.pure x
  | PFunctor.FreeM.liftBind t k => PFunctor.FreeM.bind (impl t) fun u => subst impl (k u)

variable (impl : QueryImpl spec (OracleComp target))

@[simp]
theorem subst_pure {α : Type w} (x : α) :
    subst impl (pure x : OracleComp spec α) = pure x := rfl

theorem subst_queryBind {α : Type w} (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    subst impl (queryBind t k) = PFunctor.FreeM.bind (impl t) fun u => subst impl (k u) := rfl

/-- Substitution commutes with bind, also when the two result types lie in different
universes. -/
theorem subst_freeM_bind {α : Type w} {β : Type w'} (oa : OracleComp spec α)
    (ob : α → OracleComp spec β) :
    subst impl (PFunctor.FreeM.bind oa ob) =
      PFunctor.FreeM.bind (subst impl oa) fun x => subst impl (ob x) := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
    change PFunctor.FreeM.bind (impl t) (fun u => subst impl (PFunctor.FreeM.bind (k u) ob)) =
      PFunctor.FreeM.bind (PFunctor.FreeM.bind (impl t) fun u => subst impl (k u))
        fun x => subst impl (ob x)
    rw [PFunctor.FreeM.bind_assoc]
    simp only [ih]

/-- Substitution commutes with mapping the output, also when the source and target output types
lie in different universes. -/
theorem subst_freeM_map {α : Type w} {β : Type w'} (f : α → β) (oa : OracleComp spec α) :
    subst impl (PFunctor.FreeM.map f oa) = PFunctor.FreeM.map f (subst impl oa) := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
    change PFunctor.FreeM.bind (impl t) (fun u => subst impl (PFunctor.FreeM.map f (k u))) =
      PFunctor.FreeM.map f (PFunctor.FreeM.bind (impl t) fun u => subst impl (k u))
    rw [PFunctor.FreeM.map_bind]
    simp only [ih]

@[simp]
theorem subst_bind {α β : Type w} (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    subst impl (oa >>= ob) = subst impl oa >>= fun x => subst impl (ob x) :=
  subst_freeM_bind impl oa ob

@[simp]
theorem subst_map {α β : Type w} (f : α → β) (oa : OracleComp spec α) :
    subst impl (f <$> oa) = f <$> subst impl oa :=
  subst_freeM_map impl f oa

/-- When the result type lies in the answer universe, substitution is `simulateQ`. -/
theorem subst_eq_simulateQ {α : Type v} (oa : OracleComp spec α) :
    subst impl oa = simulateQ impl oa := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
    change PFunctor.FreeM.bind (impl t) (fun u => subst impl (k u)) =
      simulateQ impl (liftM (spec.query t) >>= k)
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, ih]
    rfl

end OracleComp
