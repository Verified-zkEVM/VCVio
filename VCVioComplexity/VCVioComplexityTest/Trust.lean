/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVioComplexityTest.SecondOrderModulus

/-!
# Trust probes for the concrete complexity track

The guarded kernel reports below permit only Lean's standard extensionality, quotient, and choice
principles. They fail if a representative public result acquires additional trust.
-/

@[expose] public section

open PFunctor OracleComp.Complexity
open VCVioComplexity.Backend.TuringMachine

local instance : stepClass.HasProd := hasProd
local instance : stepClass.HasSum := hasSum
local instance : stepClass.HasOption := hasOption

/-! ## Short report aliases -/

namespace CT

theorem coin : IsPPTBy quantitativeStepClass coinBoundary oneCoinOracleProgram :=
  oneCoin_isPPTBy

noncomputable def poly := Primitive.unitIdentityPolynomial.toPolyRealizerFromTime

theorem moduli : IsOraclePPTBy quantitativeStepClass coinBoundary
    VCVioComplexityTest.SecondOrderModulus.twoResponseModelContract oneCoinProgram :=
  VCVioComplexityTest.SecondOrderModulus.oneCoin_isOraclePPTBy_twoResponseModels

end CT

/--
info: 'CT.coin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CT.coin

/--
info: 'CT.poly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CT.poly

/--
info: 'CT.moduli' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CT.moduli
