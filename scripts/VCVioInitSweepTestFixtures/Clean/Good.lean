/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finite.Prod

/-! # The spelling that is not a hazard

`Fintype.ofFinite` takes the `Prop`-valued `Finite` argument, so the instance is
noncomputable and the elaborator creates no compiled auxiliary at all: only a `_proof_`.
Nothing here is evaluated when the module is loaded, which is the whole point.
-/

public section

namespace VCVioInitSweepTestFixtures.Clean.Good

/-- A bundle of carriers, mirroring the shape the hazard was written in: the `Fintype`
instance is demanded for a *field*, not for a syntactically visible type. -/
structure Primitives where
  Y : Type

/-- An eight-element carrier. The fixtures are deliberately tiny because the gate is a shape
check and a larger one would only cost build time: the sweep reads oleans and never executes
a swept module's initialisation function, so it could not be exhausted by the hazard it
detects (`scripts/InitSweep.lean` records the link line and the absence of
`precompileModules` that make that true). -/
@[expose] def bundle : Primitives := { Y := Fin 3 → Bool }

/-- The shipped spelling. Named so the test can assert that it is *not* flagged even
though its value names `Fintype.ofFinite`: the name test alone would flag it, and the
compiled-code clause is what saves it. -/
noncomputable instance : Fintype bundle.Y :=
  @Fintype.ofFinite _ (inferInstanceAs (Finite (Fin 3 → Bool)))

end VCVioInitSweepTestFixtures.Clean.Good
