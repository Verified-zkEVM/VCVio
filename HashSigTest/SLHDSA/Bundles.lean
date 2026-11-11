/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteModel

/-!
# The cores of the SHAKE and FIPS SHA-2 bundles

The core primitives of the SHAKE bundle `Concrete.shakePrimitives` and of the FIPS SHA-2 bundle
`Concrete.sha2Primitives`, indexed by validated parameters, as the SLH-DSA test modules use them.
The SHAKE core is the library's `Security.shakeCore`, exported here so that a module opening both
namespaces names one constant.
-/

public section

namespace SLHDSA.BundleTest

export Security (shakeCore)

/-- The core of the FIPS SHA-2 bundle at validated parameters `vp`. -/
abbrev sha2Core (vp : ValidatedParams) : CorePrimitives vp.params :=
  (Concrete.sha2Primitives vp.params).core

end SLHDSA.BundleTest
