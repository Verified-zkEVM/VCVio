/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.HasQuery.Basic
public import VCVio.OracleComp.ProbComp
public import PolyFun.Control.Monad.Hom

/-!
# Morphisms of `HasQuery` Monads

This module contains the heavier `HasQuery` naturality layer.
It imports `ProbComp` and monad homomorphisms, so files that only need the
basic query capability should import `VCVio.OracleComp.HasQuery.Basic`
instead.

Use this module for proofs that a monad morphism preserves oracle queries, for composing such
morphisms through `QueryHom.id` and `QueryHom.comp`, or for interpreting free oracle syntax through
the ambient query capability with `QueryHom.ofSimulateQ`. The separate `PreservesProbCompLift`
predicate records commutation with the canonical lift of public randomness.
-/

@[expose] public section

universe u v w x y z

namespace HasQuery

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}
  {m : Type v → Type w} [Monad m] [HasQuery spec m]
  {n : Type v → Type x} [Monad n] [HasQuery spec n]

/-- A `QueryHom spec m n` is a monad morphism `m →ᵐ n` that also preserves the distinguished
oracle-query capability for `spec`. This is the right notion of morphism for proving that a
construction generic over `HasQuery spec` is natural in the chosen oracle semantics. -/
structure QueryHom (spec : OracleSpec.{u, v} ι)
    (m : Type v → Type w) [Monad m] [HasQuery spec m]
    (n : Type v → Type x) [Monad n] [HasQuery spec n]
    extends m →ᵐ n where
  map_query' (t : spec.Domain) :
    toFun _ (HasQuery.query (spec := spec) (m := m) t) =
      HasQuery.query (spec := spec) (m := n) t

/-- A monad morphism preserves public randomness when it commutes with the distinguished lifting
of plain probabilistic computations into the ambient monad. -/
def PreservesProbCompLift
    {m : Type → Type w} [Monad m] [MonadLiftT ProbComp m]
    {n : Type → Type x} [Monad n] [MonadLiftT ProbComp n]
    (F : m →ᵐ n) : Prop :=
  ∀ {α : Type} (oa : ProbComp α), F (liftM oa : m α) = (liftM oa : n α)

@[simp]
lemma map_query (F : QueryHom spec m n) (t : spec.Domain) :
    F.toMonadHom (HasQuery.query (spec := spec) (m := m) t) =
      HasQuery.query (spec := spec) (m := n) t :=
  F.map_query' t

namespace QueryHom

variable {o : Type v → Type y} [Monad o] [HasQuery spec o]

/-- The identity monad morphism, bundled with its preservation of oracle queries. -/
def id (spec : OracleSpec.{u, v} ι) (m : Type v → Type w) [Monad m] [HasQuery spec m] :
    QueryHom spec m m where
  toMonadHom := MonadHom.id m
  map_query' _ := rfl

@[simp]
lemma id_toMonadHom : (id spec m).toMonadHom = MonadHom.id m := rfl

@[simp, grind =]
lemma id_apply {α : Type v} (mx : m α) : (id spec m).toMonadHom mx = mx := rfl

/-- Compose query-preserving monad morphisms, applying `F` first and then `G`. -/
protected def comp (G : QueryHom spec n o) (F : QueryHom spec m n) : QueryHom spec m o where
  toMonadHom := G.toMonadHom.comp F.toMonadHom
  map_query' t := by simp

@[simp]
lemma comp_toMonadHom (G : QueryHom spec n o) (F : QueryHom spec m n) :
    (G.comp F).toMonadHom = G.toMonadHom.comp F.toMonadHom := rfl

@[simp, grind =]
lemma comp_apply {α : Type v} (G : QueryHom spec n o) (F : QueryHom spec m n) (mx : m α) :
    (G.comp F).toMonadHom mx = G.toMonadHom (F.toMonadHom mx) := rfl

@[simp, grind =]
lemma comp_id (F : QueryHom spec m n) : F.comp (id spec m) = F := by
  rfl

@[simp, grind =]
lemma id_comp (F : QueryHom spec m n) : (id spec n).comp F = F := by
  rfl

@[grind =]
lemma comp_assoc {p : Type v → Type z} [Monad p] [HasQuery spec p]
    (H : QueryHom spec o p) (G : QueryHom spec n o) (F : QueryHom spec m n) :
    (H.comp G).comp F = H.comp (G.comp F) := by
  rfl

/-- Interpret free oracle syntax through the query capability already installed in `m`.

This is the query-preserving monad morphism induced by the free-monad fold. It does not assert a
parametricity theorem for arbitrary direct-style programs: its source is specifically
`OracleComp spec`, and its handler is definitionally the ambient `HasQuery` operation. -/
def ofSimulateQ [LawfulMonad m] : QueryHom spec (OracleComp spec) m where
  toMonadHom := simulateQ' (HasQuery.toQueryImpl (spec := spec) (m := m))
  map_query' t := by simp

@[simp]
lemma ofSimulateQ_apply [LawfulMonad m] {α : Type v} (oa : OracleComp spec α) :
    (ofSimulateQ (spec := spec) (m := m)).toMonadHom oa =
      simulateQ (HasQuery.toQueryImpl (spec := spec) (m := m)) oa := rfl

end QueryHom

end HasQuery
