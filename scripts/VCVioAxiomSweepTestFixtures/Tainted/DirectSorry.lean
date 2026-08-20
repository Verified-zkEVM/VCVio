/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-! # Direct and transitive `sorryAx` fixtures for axiomsweep -/

public section

namespace VCVioAxiomSweepTestFixtures.Tainted

opaque directSorry : Nat := sorryAx Nat true

def transitiveSorry : Nat := directSorry

end VCVioAxiomSweepTestFixtures.Tainted
