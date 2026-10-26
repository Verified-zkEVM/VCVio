/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SecretProvider.Observation
public import HashSig.SLHDSA.Security.Target

/-!
# Observing the oracle-backed FORS provider

`oracleSecret` asks the public tweakable hash at its actual address and encoded secret seed.
Interpreting the canonical FORS component retains these provider calls together with the public
leaf and node hashes. The stateful cost equation retains the entire signature, accumulated cost
and final state; the cost wraps the handler, so a cache hit remains an observed call.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.Security

/-- The oracle-backed provider makes its literal tweakable-hash query. -/
theorem simulateQ_oracleSecret {vp : ValidatedParams} (core : CorePrimitives vp.params)
    (equiv : core.SkSeed ≃ core.Y) (pk : core.PkSeed) (sk : core.SkSeed) (address : Adrs)
    {m : Type → Type*} [Monad m] [LawfulMonad m] (handler : QueryImpl (publicHashSpec core) m) :
    simulateQ handler (oracleSecret core equiv pk sk address :
      OracleComp (publicHashSpec core) core.Y) =
        handler (.thash pk (core.adrsToKey address) [equiv sk]) := by
  simp only [oracleSecret, PublicHash.f, simulateQ_HasQuery_query]

/-- Interpret the actual provider, leaf hashes and node hashes of FORS through one handler. -/
theorem simulateQ_forsSignWithSecretM_oracleSecret {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (equiv : core.SkSeed ≃ core.Y)
    (pk : core.PkSeed) (sk : core.SkSeed) (md : List Byte) (address : Adrs)
    {m : Type → Type*} [Monad m] [LawfulMonad m] (handler : QueryImpl (publicHashSpec core) m) :
    simulateQ handler (forsSignWithSecretM core (oracleSecret core equiv pk sk)
      md pk address : OracleComp (publicHashSpec core) (ForsSigCore vp.params core)) =
    forsSignWithSecret core
      (fun a y => simulateQ handler (PublicHash.f core pk a y))
      (fun a left right => simulateQ handler (PublicHash.h core pk a left right))
      (fun a => simulateQ handler (oracleSecret core equiv pk sk a)) md address :=
  SLHDSA.simulateQ_forsSignWithSecret core handler
    (PublicHash.f core pk) (PublicHash.h core pk) (oracleSecret core equiv pk sk) md address

/-- Observe all actual provider/hash traffic, ordered cost and arbitrary final cache/state. -/
theorem simulateQ_forsSignWithSecretM_oracleSecret_withAddCost_run {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (equiv : core.SkSeed ≃ core.Y)
    (pk : core.PkSeed) (sk : core.SkSeed) (md : List Byte) (address : Adrs)
    {m : Type → Type*} [Monad m] [LawfulMonad m] {Cache C : Type} [AddMonoid C]
    (handler : QueryImpl (publicHashSpec core) (StateT Cache m))
    (cost : (publicHashSpec core).Domain → C) (initial : Cache) :
    ((simulateQ (handler.withAddCost cost)
      (forsSignWithSecretM core (oracleSecret core equiv pk sk) md pk address :
        OracleComp (publicHashSpec core) (ForsSigCore vp.params core))).runAdd).run initial =
    ((forsSignWithSecret core
      (fun a y => simulateQ (handler.withAddCost cost) (PublicHash.f core pk a y))
      (fun a left right => simulateQ (handler.withAddCost cost) (PublicHash.h core pk a left right))
      (fun a => simulateQ (handler.withAddCost cost) (oracleSecret core equiv pk sk a))
      md address).runAdd).run initial :=
  SLHDSA.simulateQ_forsSignWithSecret_withAddCost_run core handler cost
    (PublicHash.f core pk) (PublicHash.h core pk) (oracleSecret core equiv pk sk) md address initial

end SLHDSA.Security
