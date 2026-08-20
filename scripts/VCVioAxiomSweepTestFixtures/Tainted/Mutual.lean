/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-! # Mutual-inductive fixpoint fixture for axiomsweep -/

public section

namespace VCVioAxiomSweepTestFixtures.Tainted

axiom mutualAxiom : True

mutual
  inductive MutualLeft : Type where
    | fromRight : MutualRight → MutualLeft
    | tainted : True.intro = mutualAxiom → MutualLeft

  inductive MutualRight : Type where
    | fromLeft : MutualLeft → MutualRight
end

end VCVioAxiomSweepTestFixtures.Tainted
