/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Data.Fintype.Pi

/-! # The respelling that a name test cannot see

The same instance as `Hazard.Plain`, at the same type, with the instance the elaborator was
going to use written out instead of inferred. Nothing here names `Finset.univ` or
`Fintype.piFinset`, so an entry-point name test accepts it; what gives it away is that
`Pi.instFintype` is *typed* `Fintype _`, which is the second disjunct of the gate's name
clause. The two spellings build the same enumeration in the same module initialiser.
-/

public section

namespace VCVioInitSweepTestFixtures.Hazard.Named

/-- A bundle of carriers; the `Fintype` is demanded for a field. -/
structure Primitives where
  Y : Type

/-- An eight-element carrier: the fixture reproduces the *shape*, not the size. -/
@[expose] def bundle : Primitives := { Y := Fin 3 → Bool }

/-- The hazard, named rather than inferred. -/
instance : Fintype bundle.Y := Pi.instFintype

end VCVioInitSweepTestFixtures.Hazard.Named
