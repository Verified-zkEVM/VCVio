/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import StructuralRecovery
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.QueryBudget
import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.Equality

/-!
# Constant wire clients at the verifier cap

Every fixed candidate gives a structurally query-free adversary. The actual shared game
therefore satisfies its signing lifetime and its existing universal verifier-work cap.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.SecurityDelta

open SLHDSA.SHAKE128s

/-- A wire adversary returning a supplied candidate without any query. -/
@[expose] def constantClient (ctx : Security.PureContext)
    (candidate : List Byte × List Byte) :
    StrongUnforgeableAdversary (Bridge.wireAlgorithm ctx) where
  main _ := pure candidate

/-- Every candidate has zero structural direct and signing queries. -/
theorem constantClient_bound (ctx : Security.PureContext) (candidate : List Byte × List Byte) :
    (constantClient ctx candidate).RomQueryBound 0 0 := by
  intro pk
  exact ⟨isQueryBoundP_pure _ _ _, isQueryBoundP_pure _ _ _⟩

/-- The transformed actual game obeys the selected joint cap of 3929. -/
theorem constantClient_joint (ctx : Security.PureContext) (candidate : List Byte × List Byte) :
    (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork
      (Bridge.fixedContextAdversary ctx (constantClient ctx candidate)) 3929 := by
  simpa only [Nat.zero_add, Bridge.verifierCap_eq] using
    (Bridge.hasQueryBound_fixedContext ctx (constantClient ctx candidate)
      (constantClient_bound ctx candidate))

/-- The transformed client obeys the original signing lifetime. -/
theorem constantClient_lifetime (ctx : Security.PureContext)
    (candidate : List Byte × List Byte) :
    Game.WithinSigningLimit FIPS205.scheme
      (Bridge.fixedContextAdversary ctx (constantClient ctx candidate)) :=
  Bridge.withinSigningLimit_fixedContext ctx (constantClient ctx candidate)
    (constantClient_bound ctx candidate) (by decide)

/-- The wire client and its external adaptation have exactly the same success probability. -/
theorem constantClient_advantage (ctx : Security.PureContext)
    (candidate : List Byte × List Byte) :
    strongUnforgeableAdvantage (Security.shakeRuntime FIPS205.params)
        (constantClient ctx candidate) =
      (Game.securityGame FIPS205.scheme).advantage ()
        (Bridge.fixedContextAdversary ctx (constantClient ctx candidate)) :=
  Bridge.strongUnforgeableAdvantage_eq_fixedContext ctx (constantClient ctx candidate)

end SLHDSA.SecurityDelta

#print axioms SLHDSA.SecurityDelta.constantClient_bound
#print axioms SLHDSA.SecurityDelta.constantClient_joint
#print axioms SLHDSA.SecurityDelta.constantClient_lifetime
#print axioms SLHDSA.SecurityDelta.constantClient_advantage
