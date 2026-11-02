/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.ProviderObservation
public import HashSig.SLHDSA.Security.ByteModel
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Actual provider effects at two approved SHAKE parameter sets

These clients interpret the production oracle-backed secret provider, leaf hash and node hash
together. The 128s observer records a chronological event word; the 192f observer counts every
component query. Both retain the complete signature and final cache, including provider calls
and cache hits. These component observations are separate from adversary/shared security budgets
and assert no security theorem for a different provider model. The 192f client uses its own
`shakeCore`/`publicHashSpec` carriers, independently of the full 30-byte shared 128s ROM.
-/

public section

open OracleSpec OracleComp SLHDSA SLHDSA.Security

namespace SLHDSA.Examples.ForsProvider

local notation "vp128" => FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams
local notation "core128" => shakeCore vp128
local notation "vp192" => FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams
local notation "core192" => shakeCore vp192

/-- Assign each SHAKE-128s component query its singleton chronological event word. -/
@[expose] def chronological128s (input : (publicHashSpec core128).Domain) :
    FreeAddMonoid ((publicHashSpec core128).Domain) := .of input

/-- Assign unit cost to every SHAKE-192f component query. -/
@[expose] def count192f (_input : (publicHashSpec core192).Domain) : Nat := 1

/-- One handler preserves actual 128s provider/hash order, signature and final cache jointly. -/
theorem chronological128s_observer
    (pk : (core128).PkSeed) (sk : (core128).SkSeed) (md : List Byte) (address : Adrs)
    {m : Type → Type*} [Monad m] [LawfulMonad m] {Cache : Type}
    (handler : QueryImpl (publicHashSpec core128) (StateT Cache m)) (initial : Cache) :
    ((simulateQ (handler.withAddCost chronological128s)
      (forsSignWithSecretM core128 (oracleSecret core128 (Equiv.refl _) pk sk) md pk address :
        OracleComp (publicHashSpec core128) (ForsSigCore (vp128).params core128))).runAdd).run
      initial =
    ((forsSignWithSecret core128
      (fun a y => simulateQ (handler.withAddCost chronological128s) (PublicHash.f core128 pk a y))
      (fun a left right => simulateQ (handler.withAddCost chronological128s)
        (PublicHash.h core128 pk a left right))
      (fun a => simulateQ (handler.withAddCost chronological128s)
        (oracleSecret core128 (Equiv.refl _) pk sk a)) md address).runAdd).run initial :=
  simulateQ_forsSignWithSecretM_oracleSecret_withAddCost_run core128 (Equiv.refl _)
    pk sk md address handler chronological128s initial

/-- Actual 192f component-query cost includes the interpreted provider and retains final state. -/
theorem counted192f_observer
    (pk : (core192).PkSeed) (sk : (core192).SkSeed) (md : List Byte) (address : Adrs)
    {m : Type → Type*} [Monad m] [LawfulMonad m] {Cache : Type}
    (handler : QueryImpl (publicHashSpec core192) (StateT Cache m)) (initial : Cache) :
    ((simulateQ (handler.withAddCost count192f)
      (forsSignWithSecretM core192 (oracleSecret core192 (Equiv.refl _) pk sk) md pk address :
        OracleComp (publicHashSpec core192) (ForsSigCore (vp192).params core192))).runAdd).run
      initial =
    ((forsSignWithSecret core192
      (fun a y => simulateQ (handler.withAddCost count192f) (PublicHash.f core192 pk a y))
      (fun a left right => simulateQ (handler.withAddCost count192f)
        (PublicHash.h core192 pk a left right))
      (fun a => simulateQ (handler.withAddCost count192f)
        (oracleSecret core192 (Equiv.refl _) pk sk a)) md address).runAdd).run initial :=
  simulateQ_forsSignWithSecretM_oracleSecret_withAddCost_run core192 (Equiv.refl _)
    pk sk md address handler count192f initial

end SLHDSA.Examples.ForsProvider
