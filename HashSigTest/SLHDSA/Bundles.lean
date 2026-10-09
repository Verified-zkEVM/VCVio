/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Concrete.FIPS

/-!
# The cores of the SHAKE and FIPS SHA-2 bundles

The core primitives of the SHAKE bundle `Concrete.shakePrimitives` and of the FIPS SHA-2 bundle
`Concrete.sha2Primitives`, indexed by validated parameters, as the SLH-DSA test modules use them.
-/

public section

namespace SLHDSA.BundleTest

/-- The core of the SHAKE bundle at validated parameters `vp`. -/
abbrev shakeCore (vp : ValidatedParams) : CorePrimitives vp.params :=
  (Concrete.shakePrimitives vp.params).core

/-- The core of the FIPS SHA-2 bundle at validated parameters `vp`. -/
abbrev sha2Core (vp : ValidatedParams) : CorePrimitives vp.params :=
  (Concrete.sha2Primitives vp.params).core

end SLHDSA.BundleTest
