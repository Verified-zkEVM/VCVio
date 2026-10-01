/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Control.Monad.Support.WP
public import Std.WP
public import VCVio.ProgramLogic.Unary.HoarePropTriple

/-!
# Structural weakest preconditions

The structural core `WPMonad` interpretation quantifies over every structurally reachable
output of `OracleComp spec`, independently of a probability interpretation. It is the global
instance of `OracleComp`, as core's own `Prop`-valued instances are for its monads: a triple
`⦃ pre ⦄ oa ⦃ post ⦄` with no scope open says that every possible output satisfies `post`. The
expectation readings are selected by their scopes (`OracleComp.Lower`, `OracleComp.Upper`).

`wp_iff_forall_support` states it against the structural support. Probability-one coherence
additionally needs the uniform, finite-support assumptions stated in `Unary/WP/Coherence.lean`.
-/

@[expose] public section

universe u

open Std.WP

namespace OracleComp.Necessary

variable {ι : Type u} {spec : OracleSpec ι}
variable {α β : Type}

/-- Core weakest preconditions for all structurally reachable outputs: the global reading of
`OracleComp`, which needs no probability interpretation. -/
noncomputable instance instWP :
    Std.WP.WPMonad (OracleComp spec) Prop EStack⟨⟩ :=
  MonadAttach.toWPMonadDemonic

/-- Structural weakest preconditions hold precisely on every possible output. -/
theorem wp_iff_forall_support (oa : OracleComp spec α) (post : α → Prop) :
    Std.WP.wp oa post Lean.Order.bot ↔ ∀ a ∈ support oa, post a :=
  Iff.rfl

/-- A lifted primitive query may return any answer. This is the form `vcgen` reaches from
`liftM (OracleSpec.query t)` once it unfolds the `MonadLiftT` chain. -/
@[spec]
theorem Spec.monadLift_query (t : spec.Domain) (post : spec.Range t → Prop)
    {epost : EStack⟨⟩} :
    Triple (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
      OracleComp spec (spec.Range t)) (∀ u, post u) post epost :=
  ⟨fun h u _ => h u⟩

-- `query t` is `liftM (OracleSpec.query t)` in every monad with queries, so `vcgen` reaches the
-- lifted form in `OracleComp` and through its transformers alike.
attribute [spec] HasQuery.instOfMonadLift_query

end OracleComp.Necessary
