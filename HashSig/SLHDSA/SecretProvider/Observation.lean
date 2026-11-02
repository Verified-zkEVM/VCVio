/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SecretProvider
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Interpreting effectful FORS providers

One ambient handler interprets the leaf, node and secret-provider programs of the canonical
FORS component. The equations retain all effects of that handler. Additive writer instrumentation
therefore preserves the complete signature, chronological cost and final state, with arbitrary
initial state and a cost monoid that need not commute.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA

/-- Interpret every effectful callback of the canonical FORS signing component together. -/
theorem simulateQ_forsSignWithSecret {p : Params} (core : CorePrimitives p)
    {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (handler : QueryImpl spec m)
    (leaf : Adrs → core.Y → OracleComp spec core.Y)
    (node : Adrs → core.Y → core.Y → OracleComp spec core.Y)
    (secret : Adrs → OracleComp spec core.Y) (md : List Byte) (address : Adrs) :
    simulateQ handler (forsSignWithSecret core leaf node secret md address) =
      forsSignWithSecret core (fun a y => simulateQ handler (leaf a y))
        (fun a left right => simulateQ handler (node a left right))
        (fun a => simulateQ handler (secret a)) md address :=
  forsSignWithSecret_natural core (simulateQ' handler)
    leaf (fun a y => simulateQ handler (leaf a y))
    node (fun a left right => simulateQ handler (node a left right))
    secret (fun a => simulateQ handler (secret a))
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) md address

/-- Retain the entire signature, ordered cost and final state of effectful FORS execution. -/
theorem simulateQ_forsSignWithSecret_withAddCost_run {p : Params} (core : CorePrimitives p)
    {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} [Monad m] [LawfulMonad m]
    {Cache C : Type} [AddMonoid C]
    (handler : QueryImpl spec (StateT Cache m)) (cost : spec.Domain → C)
    (leaf : Adrs → core.Y → OracleComp spec core.Y)
    (node : Adrs → core.Y → core.Y → OracleComp spec core.Y)
    (secret : Adrs → OracleComp spec core.Y) (md : List Byte) (address : Adrs) (initial : Cache) :
    ((simulateQ (handler.withAddCost cost)
      (forsSignWithSecret core leaf node secret md address)).runAdd).run initial =
    ((forsSignWithSecret core
      (fun a y => simulateQ (handler.withAddCost cost) (leaf a y))
      (fun a left right => simulateQ (handler.withAddCost cost) (node a left right))
      (fun a => simulateQ (handler.withAddCost cost) (secret a)) md address).runAdd).run initial :=
  congrArg (fun program => program.runAdd.run initial)
    (simulateQ_forsSignWithSecret core (handler.withAddCost cost) leaf node secret md address)

end SLHDSA
