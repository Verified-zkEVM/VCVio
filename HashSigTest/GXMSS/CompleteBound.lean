/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Unforgeability

/-! # Exact and relaxed complete-tree coefficients

At height three with two chains and four chain positions, the exact positive-position
coefficients are 48 for preimage resistance and 144 for undetectability. The separate
power-of-two relaxation uses 64 and 256.
-/

public section

namespace GXMSS.CompleteBoundTest

open ENNReal Unforgeability

/-- Evaluating the numerical bound isolates each exact and relaxed chain coefficient. -/
theorem coefficients :
    reductionBound 3 2 2 0 0 0 0 0 1 = 48 ∧
    reductionBound 3 2 2 0 0 0 0 1 0 = 144 ∧
    powerOfTwoReductionBound 3 2 2 0 0 0 0 0 1 = 64 ∧
    powerOfTwoReductionBound 3 2 2 0 0 0 0 1 0 = 256 := by
  norm_num [reductionBound, powerOfTwoReductionBound]

end GXMSS.CompleteBoundTest
