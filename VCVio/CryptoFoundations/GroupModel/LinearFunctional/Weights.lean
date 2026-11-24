/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.BigOperators.Field


/-! # Signing gaps of weighted targets

Weights describe a message's target as a linear combination of independently sampled bases.
`gapCoeff` is the difference between a target's weights and the weights of the signing queries
that represent it, coordinate by coordinate. It needs no finite message type, probability
interpretation or query bound.
-/

public section

namespace GroupModel.LinearFunctional

/-- The difference between the target's weights and the represented signing-query weights. -/
@[expose] def gapCoeff {F M ι Q : Type*} [Ring F] [Fintype Q]
    (w : ι → M → F) (m : M) (messages : Q → M) (coeff : Q → F) (i : ι) : F :=
  w i m - ∑ q, coeff q * w i (messages q)

end GroupModel.LinearFunctional
