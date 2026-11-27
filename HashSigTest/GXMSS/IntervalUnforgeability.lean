/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Unforgeability
public import HashSigTest.GXMSS.ActiveSecurity

/-!
# Interval endpoint and exact coefficient controls

The singleton nonmaximum encoding reaches the complete interval endpoint through the actual
all-request adversary. Full-range height-three coefficients are 48/144 and relax to 64/256.
An interior inclusive interval checks that selector loss follows active length.
-/

public section
namespace GXMSS.IntervalUnforgeabilityProbe
open ENNReal GXMSS.IntervalMerkle GXMSS.Interval.Unforgeability
open SyncSignatureUnforgeability

/-- The interval theorem applies to a singleton code with no two-codeword witness. -/
theorem singleton_endpoint :
    strongAdvantage (GXMSS.Interval.scheme ActiveSecurityProbe.hash ActiveSecurityProbe.encoding
      1 ActiveSecurityProbe.whole) ProbCompRuntime.probComp ActiveSecurityProbe.adversary ≤
      strongUnforgeabilityBound ActiveSecurityProbe.hash ActiveSecurityProbe.encoding 1 1
        ActiveSecurityProbe.whole (by decide) (by decide) ActiveSecurityProbe.adversary := by
  exact strong_unforgeability_reduction_bound _ _ 1 1 _ (by decide) (by decide)
    ActiveSecurityProbe.singleton_nonmaximum _ ActiveSecurityProbe.one_request

/-- Exact positive-position coefficients and their relaxed values remain distinct. -/
theorem full_coefficients :
    GXMSS.Interval.activeChainPositionCount (Interval.full 3) 2 2 = 48 ∧
      GXMSS.Interval.activeChainPositionCount (Interval.full 3) 2 2 * (2 ^ 2 - 1) = 144 ∧
      (Interval.full 3).length * 2 * 2 ^ 2 = 64 ∧
      (Interval.full 3).length * 2 * (2 ^ 2) ^ 2 = 256 := by decide

/-- A proper interval includes both endpoints in the selector factor. -/
def interior : Interval 3 := ⟨2, 5, by decide⟩

/-- Interior and height-zero intervals retain their exact inclusive lengths. -/
theorem endpoint_coefficients :
    GXMSS.Interval.activeChainPositionCount interior 2 2 = 24 ∧
      GXMSS.Interval.activeChainPositionCount interior 2 2 * (2 ^ 2 - 1) = 72 ∧
      interior.length * 2 * 2 ^ 2 = 32 ∧
      interior.length * 2 * (2 ^ 2) ^ 2 = 128 ∧
      GXMSS.Interval.activeChainPositionCount (Interval.full 0) 2 2 = 6 := by decide

end GXMSS.IntervalUnforgeabilityProbe
