/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound.Exact

/-!
# Exact structural query counts

`ExactQueryCount computation count` certifies that every response branch of the free
computation makes the same number of oracle calls. It specializes the generic counting
predicate to the small oracle and result types used by the concrete SLH-DSA proof.
-/

public section

namespace SLHDSA.SHAKE128s.Generic

/-- A common query count on all response branches of a free oracle computation. -/
abbrev ExactQueryCount {ι : Type} {spec : OracleSpec ι} {α : Type} :
    OracleComp spec α → Nat → Prop :=
  OracleComp.QueryBound.ExactQueryCount

namespace ExactQueryCount

export OracleComp.QueryBound.ExactQueryCount (pure query bind map)

end ExactQueryCount

end SLHDSA.SHAKE128s.Generic
