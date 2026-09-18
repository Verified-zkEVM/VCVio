/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Composition of oracle implementations

The free-monad fold composes implementations by its universal naturality law. Composition
preserves the target monad's effects and needs no probabilistic interpretation.
-/

public section

open OracleSpec OracleComp

universe u v

namespace QueryImpl

section compose

variable {m : Type u → Type v} [Monad m]
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {α β γ : Type u}

/-- Given an implementation of `spec` in terms of a new set of oracles `spec'`,
and an implementation of `spec'` in terms of arbitrary `m`, implement `spec` in terms of `m`. -/
@[expose]
def compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec')) :
    QueryImpl spec m :=
  fun t => simulateQ so' (so t)

infixl : 65 " ∘ₛ " => QueryImpl.compose

@[simp]
lemma apply_compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec'))
    (t : spec.Domain) : (so' ∘ₛ so) t = simulateQ so' (so t) := rfl

@[simp]
lemma simulateQ_compose [LawfulMonad m] (so' : QueryImpl spec' m)
    (so : QueryImpl spec (OracleComp spec'))
    (oa : OracleComp spec α) : simulateQ (so' ∘ₛ so) oa = simulateQ so' (simulateQ so oa) := by
  exact (PFunctor.FreeM.liftM_natural so (simulateQ' so') oa).symm

@[simp]
lemma compose_id' [LawfulMonad m] (so : QueryImpl spec m) :
    so ∘ₛ QueryImpl.id' spec = so := by ext x; simp

end compose

end QueryImpl
