/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Nonzero-Universe Consumer Canaries

Oracle interfaces whose queries and responses live above `Type 0` are ordinary downstream
usage: a protocol whose messages are polynomials, vectors, or field elements over a
universe-polymorphic carrier lands there immediately. The public simulation-composition
laws must therefore apply at that generality — a law that holds only at `Type 0` forces a
consumer to restate it locally, which is not a reusable API.

Each example below routes a query or a computation through a sum handler at a response
universe `uQuery` with *distinct* index universes, mirroring the `spec + (spec₁ + spec₂)`
layout that oracle-reduction verifiers elaborate to. The `simp`-driven examples additionally
check that the routing lemmas still fire automatically at that generality.

Companion to `VCVioTest.PFunctorFacade`, which pins the `PFunctor`/`OracleSpec` façade.
-/

public section

namespace VCVioTest.UniversePolymorphism

universe uι₁ uι₂ uι₃ uQuery uTarget

variable {ι₁ : Type uι₁} {ι₂ : Type uι₂} {ι₃ : Type uι₃}
  {spec₁ : OracleSpec.{uι₁, uQuery} ι₁} {spec₂ : OracleSpec.{uι₂, uQuery} ι₂}
  {spec₃ : OracleSpec.{uι₃, uQuery} ι₃}
  {target : Type uQuery → Type uTarget} [Monad target] [LawfulMonad target]
  {α : Type uQuery}

/-! ## Two-way routing through `QueryImpl.add` -/

example (impl₁ : QueryImpl spec₁ target) (impl₂ : QueryImpl spec₂ target)
    (x : OracleComp spec₁ α) :
    simulateQ (impl₁ + impl₂) (liftM x : OracleComp (spec₁ + spec₂) α) = simulateQ impl₁ x :=
  QueryImpl.simulateQ_add_liftM_left impl₁ impl₂ x

example (impl₁ : QueryImpl spec₁ target) (impl₂ : QueryImpl spec₂ target)
    (x : OracleComp spec₂ α) :
    simulateQ (impl₁ + impl₂) (liftM x : OracleComp (spec₁ + spec₂) α) = simulateQ impl₂ x :=
  QueryImpl.simulateQ_add_liftM_right impl₁ impl₂ x

-- query-level routing, the rung the computation-level laws are built from
example (impl₁ : QueryImpl spec₁ target) (impl₂ : QueryImpl spec₂ target) (t : spec₁.Domain) :
    simulateQ (impl₁ + impl₂)
        (liftM (spec₁.query t) : OracleComp (spec₁ + spec₂) _) = impl₁ t :=
  QueryImpl.simulateQ_add_liftM_query_left impl₁ impl₂ t

example (impl₁ : QueryImpl spec₁ target) (impl₂ : QueryImpl spec₂ target) (t : spec₂.Domain) :
    simulateQ (impl₁ + impl₂)
        (liftM (spec₂.query t) : OracleComp (spec₁ + spec₂) _) = impl₂ t :=
  QueryImpl.simulateQ_add_liftM_query_right impl₁ impl₂ t

/-! ## Two-way routing through `QueryImpl.addLift`, with components in different monads -/

example {source₁ source₂ : Type uQuery → Type uTarget}
    [Monad source₁] [LawfulMonad source₁] [MonadLiftT source₁ target]
    [LawfulMonadLiftT source₁ target] [MonadLiftT source₂ target]
    (impl₁ : QueryImpl spec₁ source₁) (impl₂ : QueryImpl spec₂ source₂)
    (x : OracleComp spec₁ α) :
    simulateQ (QueryImpl.addLift impl₁ impl₂ : QueryImpl (spec₁ + spec₂) target)
        (liftM x : OracleComp (spec₁ + spec₂) α) =
      (liftM (simulateQ impl₁ x) : target α) :=
  QueryImpl.simulateQ_addLift_liftM_left impl₁ impl₂ x

example {source₁ source₂ : Type uQuery → Type uTarget}
    [Monad source₁] [MonadLiftT source₁ target]
    [Monad source₂] [LawfulMonad source₂] [MonadLiftT source₂ target]
    [LawfulMonadLiftT source₂ target]
    (impl₁ : QueryImpl spec₁ source₁) (impl₂ : QueryImpl spec₂ source₂)
    (x : OracleComp spec₂ α) :
    simulateQ (QueryImpl.addLift impl₁ impl₂ : QueryImpl (spec₁ + spec₂) target)
        (liftM x : OracleComp (spec₁ + spec₂) α) =
      (liftM (simulateQ impl₂ x) : target α) :=
  QueryImpl.simulateQ_addLift_liftM_right impl₁ impl₂ x

/-! ## Three-way `spec + (spec₁ + spec₂)` routing — the `simOracle2` verifier layout -/

example {source₀ source : Type uQuery → Type uTarget}
    [MonadLiftT source₀ target] [Monad source] [LawfulMonad source]
    [MonadLiftT source target] [LawfulMonadLiftT source target]
    (impl : QueryImpl spec₁ source₀) (impl₂ : QueryImpl spec₂ source)
    (impl₃ : QueryImpl spec₃ source) (x : OracleComp spec₂ α) :
    simulateQ (QueryImpl.addLift impl (QueryImpl.add impl₂ impl₃)
        : QueryImpl (spec₁ + (spec₂ + spec₃)) target)
      (liftM (liftM x : OracleComp (spec₂ + spec₃) α) :
        OracleComp (spec₁ + (spec₂ + spec₃)) α) =
      (liftM (simulateQ impl₂ x) : target α) :=
  QueryImpl.simulateQ_addLift_add_liftM_left impl impl₂ impl₃ x

example {source₀ source : Type uQuery → Type uTarget}
    [MonadLiftT source₀ target] [Monad source] [LawfulMonad source]
    [MonadLiftT source target] [LawfulMonadLiftT source target]
    (impl : QueryImpl spec₁ source₀) (impl₂ : QueryImpl spec₂ source)
    (impl₃ : QueryImpl spec₃ source) (x : OracleComp spec₃ α) :
    simulateQ (QueryImpl.addLift impl (QueryImpl.add impl₂ impl₃)
        : QueryImpl (spec₁ + (spec₂ + spec₃)) target)
      (liftM (liftM x : OracleComp (spec₂ + spec₃) α) :
        OracleComp (spec₁ + (spec₂ + spec₃)) α) =
      (liftM (simulateQ impl₃ x) : target α) :=
  QueryImpl.simulateQ_addLift_add_liftM_right impl impl₂ impl₃ x

-- a query lifted from an inner component routes by `simp` alone at a nonzero universe
example (impl : QueryImpl spec₁ target) (impl₂ : QueryImpl spec₂ target)
    (impl₃ : QueryImpl spec₃ target) (t : spec₃.Domain) :
    simulateQ (impl + (impl₂ + impl₃))
      (liftM (spec₃.query t) : OracleComp (spec₁ + (spec₂ + spec₃)) (spec₃.Range t)) =
      impl₃ t := by
  simp

end VCVioTest.UniversePolymorphism
