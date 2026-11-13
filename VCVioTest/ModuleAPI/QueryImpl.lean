/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic

/-!
# Query implementations and ordinary function types

`QueryImpl spec m` is reducibly the function type `(t : spec.Domain) → m (spec.Range t)`, so an
instance stated for it is a candidate for every ordinary function type into a monad. Importing
query implementations must not change the default value of such a type. (Core's
`instInhabitedForallOfMonad` already makes `pure` the default of `α → m α`; the examples use
other shapes.)
-/

public section

namespace VCVioTest.ModuleAPI.QueryImpl

example : (default : ℕ → Option Bool) 0 = none := rfl

example : (default : Bool → List ℕ) true = [] := rfl

end VCVioTest.ModuleAPI.QueryImpl
