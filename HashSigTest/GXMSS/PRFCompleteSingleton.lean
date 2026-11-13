/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.PRFDerivedUnforgeability
public import HashSigTest.GXMSS.PRFIdealization

/-!
# Original-domain singleton complete PRF endpoint

The height-zero singleton code has a nonmaximum output and no two distinct codewords. Its actual
altered-OTS adversary applies to the three-law native complete endpoint with one consumed epoch.
-/

public section
namespace GXMSS.PRFCompleteSingletonProbe
open OracleComp OracleSpec GXMSS.PRFDerived.Unforgeability

/-- Captured evaluator keys on the original three-family input domain. -/
@[expose] def prf : PRFScheme Bool (GXMSS.PRFDerived.Query Unit Unit 0 1) Bool where
  keygen := (fun i : Fin 3 => decide (i = 0)) <$> ($ᵗ Fin 3)
  eval key _ := key

/-- Whole native idealization requires only the three complete sampling laws. -/
theorem interaction [DecidableEq (GXMSS.PRFDerived.Query Unit Unit 0 1)] :
    IdealInteractionCorrespondence ActiveSecurityProbe.hash ActiveSecurityProbe.encoding
      PRFIdealizationProbe.projection.toComplete 1 ActiveSecurityProbe.adversary := by
  exact ideal_interaction_correspondence ActiveSecurityProbe.hash ActiveSecurityProbe.encoding
    PRFIdealizationProbe.projection.toComplete 1 ActiveSecurityProbe.adversary
    PRFIdealizationProbe.seed_law PRFIdealizationProbe.start_law PRFIdealizationProbe.retry_law

/-- The sharp native endpoint applies although the paper two-codeword premise is false. -/
theorem singleton_core_bound [DecidableEq (GXMSS.PRFDerived.Query Unit Unit 0 1)] :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.PRFDerived.scheme prf.keygen ActiveSecurityProbe.hash ActiveSecurityProbe.encoding
        prf.eval PRFIdealizationProbe.projection.toComplete 1)
      ProbCompRuntime.probComp ActiveSecurityProbe.adversary ≤
      strongUnforgeabilityBound ActiveSecurityProbe.hash ActiveSecurityProbe.encoding prf
        PRFIdealizationProbe.projection.toComplete 1 1 (by decide) (by decide)
        ActiveSecurityProbe.adversary := by
  exact strong_unforgeability_reduction_bound ActiveSecurityProbe.hash ActiveSecurityProbe.encoding
    prf PRFIdealizationProbe.projection.toComplete 1 1 (by decide) (by decide)
    ActiveSecurityProbe.singleton_nonmaximum ActiveSecurityProbe.adversary
    ActiveSecurityProbe.one_request PRFIdealizationProbe.seed_law
    PRFIdealizationProbe.start_law PRFIdealizationProbe.retry_law

/-- Height zero charges one seed, one start and one retry, with no frontier call. -/
theorem three_function_queries :
    IsQueryBoundP (randgenPRFReduction ActiveSecurityProbe.hash ActiveSecurityProbe.encoding
      PRFIdealizationProbe.projection.toComplete 1 ActiveSecurityProbe.adversary)
      (fun query => query.isRight = true) 3 := by
  exact randgenPRFReduction_functionQuery_bound ActiveSecurityProbe.hash
    ActiveSecurityProbe.encoding PRFIdealizationProbe.projection.toComplete 1 1
    ActiveSecurityProbe.adversary ActiveSecurityProbe.one_request

end GXMSS.PRFCompleteSingletonProbe
