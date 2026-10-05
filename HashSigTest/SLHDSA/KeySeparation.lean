/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.KeySeparation

/-!
# The FIPS SHA-2 bundles are not key-separated at every address

`CorePrimitives.KeySeparated` quantifies over every address. The FIPS SHA-2 bundles
`Concrete.sha2Primitives` send an address outside the checked `ADRSc` domain to the all-zero key,
which is also the key of the all-zero address, of type `0`. A `WOTS_PRF` address at layer `300`,
whose layer does not fit `ADRSc`'s one-byte layer field, therefore shares its key with
`Adrs.zero`, so no FIPS SHA-2 bundle is key-separated (`not_keySeparated_sha2Primitives`). Key
separation for these bundles holds only on the checked domain.
-/

public section

namespace SLHDSA.KeySeparationTest

/-- No FIPS SHA-2 bundle is key-separated at every address: the `WOTS_PRF` address at layer
`300` and the all-zero address share the all-zero key. -/
theorem not_keySeparated_sha2Primitives (p : Params) :
    ¬ (Concrete.sha2Primitives p).core.KeySeparated := by
  intro h
  refine h { wotsSkAdrs Adrs.zero 0 with layer := 300 } Adrs.zero (.inl rfl) (by decide) ?_
  simp only [Primitives.core, Concrete.sha2Primitives]
  unfold Concrete.sha2AdrsKey
  rw [show Adrs.compressSha2Checked { wotsSkAdrs Adrs.zero 0 with layer := 300 } =
    .error (.outOfRange 1 300) by decide]
  exact Vector.toList_inj.mp (by decide +kernel)

end SLHDSA.KeySeparationTest
