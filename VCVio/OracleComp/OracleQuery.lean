/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.OracleSpec

/-!
# Oracle Queries

This file defines `OracleQuery`, the single-query functor induced by an `OracleSpec`.
-/

@[expose] public section

universe u v w z

open OracleSpec

/-- Functor to represent queries to oracles specified by an `OracleSpec ι`,
defined to be the object type of the corresponding `PFunctor`.
In particular an element of `OracleQuery spec α` consists of an input value `t : spec.Domain`,
and a continuation `f : spec.Range t → α` specifying what to do with the result.
See `OracleSpec.query` for the case when the continuation `f` just returns the query result. -/
@[reducible]
def OracleQuery {ι : Type u} (spec : OracleSpec.{u, v} ι) :
    Type w → Type (max u v w) :=
  PFunctor.Obj spec.toPFunctor

@[reducible, match_pattern] protected def OracleQuery.mk {ι α} {spec : OracleSpec ι}
    (t : spec.Domain) (f : spec.Range t → α) : OracleQuery spec α := PFunctor.Obj.mk t f

namespace OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- Query an oracle on in input `t` to get a result in the corresponding `range t`.

Marked `protected`: the bare identifier `query` resolves to `HasQuery.query`
(exported in `VCVio.OracleComp.HasQuery.Basic`), which yields a value in the
ambient monad and lets Lean recover `spec` from the expected type without an
ascription. Use `spec.query t` or `OracleSpec.query t` when you specifically
want the primitive single-query syntax `OracleQuery spec (spec.Range t)`. -/
protected def query (t : spec.Domain) : OracleQuery spec (spec.Range t) :=
  OracleQuery.mk t id

protected lemma query_def (t : spec.Domain) :
    OracleSpec.query t = OracleQuery.mk t id := rfl

end OracleSpec

/-! ### Primitive `query` notation

`OracleSpec.query` is `protected` so the bare identifier `query` resolves to
`HasQuery.query` (exported in `VCVio.OracleComp.HasQuery.Basic`) for
ergonomic monadic use. Files that work *structurally* on the primitive
single-query syntax `OracleQuery spec _` (e.g. `liftM (query t)`,
`(query t).cont`, induction on `query_bind`) can opt back into the
primitive interpretation of bare `query` with a single line:

```
open scoped OracleSpec.PrimitiveQuery
```

The notation is `scoped` to this namespace, so it never leaks past a file
boundary; you must explicitly opt in. -/
namespace OracleSpec.PrimitiveQuery

/-- Inside `open scoped OracleSpec.PrimitiveQuery`, the bare identifier
`query` aliases the primitive single-query syntax `OracleSpec.query`. -/
scoped notation "query" => OracleSpec.query

end OracleSpec.PrimitiveQuery

namespace OracleQuery

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- The oracle input used in an oracle query. -/
@[inline, reducible]
def input {α} (q : OracleQuery spec α) : spec.Domain := PFunctor.Obj.fst q

@[simp] lemma input_mk {α} (t : spec.Domain) (f : spec.Range t → α) :
    input (OracleQuery.mk t f) = t := rfl

alias input_apply := input_mk

@[simp] lemma input_map {α β} (q : OracleQuery spec α) (f : α → β) :
    (f <$> q).input = q.input := rfl

@[simp] lemma input_map' {α β} (q : OracleQuery spec α) (f : α → β) :
    OracleQuery.input (PFunctor.map spec.toPFunctor f q) = q.input := rfl

/-- The continuation used for the result of an oracle query. -/
@[inline, reducible]
def cont {α} (q : OracleQuery spec α) : spec.Range q.input → α := PFunctor.Obj.snd q

@[simp] lemma cont_mk {α} (t : spec.Domain) (f : spec.Range t → α) :
    cont (OracleQuery.mk t f) = f := rfl

alias cont_apply := cont_mk

@[simp] lemma cont_map {α β} (q : OracleQuery spec α) (f : α → β) :
    (f <$> q).cont = f ∘ q.cont := rfl

@[simp] lemma cont_map' {α β} (q : OracleQuery spec α) (f : α → β) :
    OracleQuery.cont (PFunctor.map spec.toPFunctor f q) = f ∘ q.cont := rfl

/-- Two oracles queries are equal if they query for the same input and run
extensionally equal continuation on the results of the query. -/
@[ext] lemma ext {α} {q q' : OracleQuery spec α}
    (h : q.input = q'.input) (h' : q.cont ≍ q'.cont) : q = q' := by
  cases q using PFunctor.Obj.rec with
  | mk t f =>
    cases q' using PFunctor.Obj.rec with
    | mk t' f' =>
      change t = t' at h
      subst t'
      exact congrArg (OracleQuery.mk t) (eq_of_heq h')

/-- Version of `OracleQuery.ext` that avoids using `HEq` when the inputs are the same. -/
lemma ext' {α} (t : spec.Domain) {cont cont' : spec.Range t → α}
    (h : cont = cont') : (OracleQuery.mk t cont : OracleQuery spec α) = OracleQuery.mk t cont' := by
  exact congrArg (OracleQuery.mk t) h

/-- If an oracle exists and the output type is non-empty then the type of queries is non-empty. -/
instance {α} [Inhabited ι] [Inhabited α] : Inhabited (OracleQuery spec α) :=
  ⟨OracleQuery.mk default (fun _ ↦ default)⟩

/-- If there are no oracles available then the type of queries is empty. -/
instance {α} [h : IsEmpty ι] : IsEmpty (OracleQuery spec α) :=
  ⟨fun q ↦ PFunctor.Obj.rec (fun t _ ↦ h.false t) q⟩

/-- If there is at most one oracle and output, then there is at most one query. -/
instance {α} [h : Subsingleton ι] [h' : Subsingleton α] : Subsingleton (OracleQuery spec α) where
  allEq q q' := by
    cases q using PFunctor.Obj.rec with
    | mk t cont =>
      cases q' using PFunctor.Obj.rec with
      | mk t' cont' =>
        obtain rfl := h.allEq t t'
        exact OracleQuery.ext' t (Subsingleton.allEq cont cont')

@[simp] lemma input_query (t : spec.Domain) : (OracleSpec.query t).input = t := rfl
@[simp] lemma cont_query (t : spec.Domain) : (OracleSpec.query t).cont = id := rfl

@[simp] lemma fst_query (t : spec.Domain) : PFunctor.Obj.fst (OracleSpec.query t) = t := rfl
@[simp] lemma snd_query (t : spec.Domain) : PFunctor.Obj.snd (OracleSpec.query t) = id := rfl

@[simp] lemma cont_map_query_input {α} (q : OracleQuery spec α) :
    q.cont <$> (OracleSpec.query q.input) = q := rfl

@[simp] lemma cont_map_query_input' {α} (q : OracleQuery spec α) :
    PFunctor.map spec.toPFunctor q.cont (OracleSpec.query q.input) = q := rfl

@[simp] lemma query_eq_mk_iff (t : spec.Domain) (cont : spec.Range t → spec.Range t) :
    OracleSpec.query t = OracleQuery.mk t cont ↔ cont = id := by
  simp [OracleQuery.ext_iff, eq_comm]

@[simp] lemma mk_eq_query_iff (t : spec.Domain) (cont : spec.Range t → spec.Range t) :
    OracleQuery.mk t cont = OracleSpec.query t ↔ cont = id := by
  simp [OracleQuery.ext_iff, eq_comm]

end OracleQuery
