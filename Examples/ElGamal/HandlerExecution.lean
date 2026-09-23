/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.ElGamal.ComputationalComplexity
public import PolyFun.PFunctor.Free.HandlerMachine

/-!
# Bounded dispatch for the ElGamal reduction

The three-query open reduction executes through one dependent handler dispatcher. The caller
is suspended during each handler and resumes with its actual answer. A uniform handler query
bound derives completion in `3 * (inner + 2)` transitions, counting entry and return dispatch.
Erasure preserves the full inner oracle interaction, so it also recovers the established
probabilistic reduction when the ports are closed with an adversary and a fair coin.

These are operational transition bounds. Encoded group operations and backend machine costs
require separate quantitative realization certificates.
-/

public section

open OracleComp PFunctor.FreeM MonadAttach
open PFunctor.FreeM.HandlerMachine

namespace elGamalAsymmEnc

variable {G State : Type} [AddCommGroup G]
  {ι : Type} {spec : OracleSpec ι}

/-- Execute the reduction's dependent handlers with enough fuel for three bounded calls. -/
@[expose] def executeHandlers
    (impl : QueryImpl (oneTimeINDCPASpec G G State (G × G) + coinSpec) (OracleComp spec))
    (inner : ℕ) (g A B T : G) :=
  runPrefix impl (3 * (inner + 2))
    (.caller (IND_CPA_OneTime_DDHReduction_openOracle (State := State) g A B T))

/-- Every response branch of the bounded dispatcher returns a Boolean. -/
theorem executeHandlers_complete
    (impl : QueryImpl (oneTimeINDCPASpec G G State (G × G) + coinSpec) (OracleComp spec))
    (inner : ℕ) (himpl : ∀ a, IsTotalQueryBound (impl a) inner) (g A B T : G) :
    AllOutputs (fun out => ∃ value, out.phase = Phase.caller (PFunctor.FreeM.pure value))
      (executeHandlers impl inner g A B T) :=
  runPrefix_complete impl _ 3 inner
    (IND_CPA_OneTime_DDHReduction_openOracle_isTotalQueryBound g A B T) himpl

/-- Erasing the completed dispatcher recovers the same ordered inner oracle program. -/
theorem executeHandlers_result
    (impl : QueryImpl (oneTimeINDCPASpec G G State (G × G) + coinSpec) (OracleComp spec))
    (inner : ℕ) (himpl : ∀ a, IsTotalQueryBound (impl a) inner) (g A B T : G) :
    (fun out => result out.phase) <$> executeHandlers impl inner g A B T =
      some <$> simulateQ impl
        (IND_CPA_OneTime_DDHReduction_openOracle (State := State) g A B T) := by
  exact map_result_runPrefix impl _ 3 inner
    (IND_CPA_OneTime_DDHReduction_openOracle_isTotalQueryBound g A B T) himpl

section Closed

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Module F G] [SampleableType G] {gen : G}

/-- Executing the adversary and fair-coin handlers yields the original ElGamal reduction,
including its adaptive sampling behavior. -/
theorem executeHandlers_reduction
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (elGamalAsymmEnc F G gen))
    (inner : ℕ)
    (himpl : ∀ a, IsTotalQueryBound
      ((oneTimeINDCPAImpl (gen := gen) adv + oneTimeDDHFairCoinImpl) a) inner)
    (g A B T : G) :
    (fun out => result out.phase) <$>
        executeHandlers (oneTimeINDCPAImpl (gen := gen) adv + oneTimeDDHFairCoinImpl)
          inner g A B T =
      some <$> IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv g A B T := by
  rw [executeHandlers_result _ inner himpl,
    IND_CPA_OneTime_DDHReduction_openOracle_eval]

end Closed

end elGamalAsymmEnc
