/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure

/-!
# Discrete compatibility scope for `ProbComp`

Opening `ProbComp.DiscreteCompatibility` gives the finite-distribution evaluation adapter
precedence, so explicitly scoped compatibility proofs evaluate `ProbComp` through its discrete
distribution. Native measure proofs do not open this scope.
-/

public section

namespace ProbComp.DiscreteCompatibility

-- Give the existing finite adapter precedence in explicitly scoped compatibility proofs.
scoped[ProbComp.DiscreteCompatibility] attribute [instance 1000]
  instEvalDistSemanticsOfMonadLiftTSPMF

end ProbComp.DiscreteCompatibility
