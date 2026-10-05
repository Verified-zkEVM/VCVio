/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.KeyDiscipline

/-!
# The key discipline at the FIPS SHA-2 bundles

`CorePrimitives.KeySeparated` quantifies over every address, in range or not. The FIPS SHA-2 key
`Concrete.sha2AdrsKey` sends an address outside the checked `ADRSc` domain to the type-tagged
`Concrete.sha2FallbackKey`. A `WOTS_PRF` address at layer `300`, whose layer does not fit `ADRSc`'s
one-byte layer field, is such an address: its key is the fallback key of a secret-key type
(`sha2AdrsKey_wotsPrf_layer300`), which is neither the all-zero key nor the key of the all-zero
address, of type `0` (`sha2AdrsKey_wotsPrf_layer300_ne_zero`). The statements below pin the
resulting discharges: key separation at every FIPS SHA-2 bundle, and the key discipline at every
FIPS 205 parameter set, at the limited SHA2-128-24 profile and at the compatibility bundle.
-/

public section

namespace SLHDSA.KeySeparationTest

open Concrete

/-- A `WOTS_PRF` address whose layer does not fit the one-byte `ADRSc` layer field. -/
def wotsPrfLayer300 : Adrs := { wotsSkAdrs Adrs.zero 0 with layer := 300 }

/-- The checked compression rejects it. -/
theorem compressSha2Checked_wotsPrfLayer300 :
    wotsPrfLayer300.compressSha2Checked = .error (.outOfRange 1 300) := by decide

/-- Its SHA-2 key is the fallback key of a secret-key type: the all-zero string with `8` at the type
byte. -/
theorem sha2AdrsKey_wotsPrf_layer300 :
    sha2AdrsKey wotsPrfLayer300 = sha2FallbackKey 5 ∧
      (sha2FallbackKey 5).toList = List.replicate 9 0 ++ [8] ++ List.replicate 12 0 :=
  ⟨sha2AdrsKey_of_compressSha2Checked_eq_error compressSha2Checked_wotsPrfLayer300, by decide⟩

/-- Its SHA-2 key is neither the all-zero key nor the key of the all-zero address. -/
theorem sha2AdrsKey_wotsPrf_layer300_ne_zero :
    sha2AdrsKey wotsPrfLayer300 ≠ zeroBytes 22 ∧
      sha2AdrsKey wotsPrfLayer300 ≠ sha2AdrsKey Adrs.zero := by
  rw [sha2AdrsKey_wotsPrf_layer300.1]
  exact ⟨fun h => absurd (congrArg Vector.toList h) (by decide),
    sha2AdrsKey_eq_compressed Adrs.zero (by decide) (by decide) (by decide) ▸
      fun h => absurd (congrArg Vector.toList h) (by decide)⟩

/-- Every FIPS SHA-2 bundle is key-separated. -/
example (p : Params) : (sha2Primitives p).core.KeySeparated := keySeparated_sha2Primitives p

/-- Every FIPS 205 parameter set's approved bundle satisfies the key discipline. -/
example (ps : FipsParameterSet) :
    (approvedPrimitives ps).core.KeyDiscipline ps.validatedParams :=
  keyDiscipline_approvedPrimitives ps

/-- The FIPS SHA-2 bundle at the limited SHA2-128-24 profile satisfies the key discipline. -/
example : (sha2Primitives slhdsaSha2_128_24).core.KeyDiscipline
    (LimitedParameterSet.validatedParams .SLHDSA_SHA2_128_24) :=
  keyDiscipline_limited .SLHDSA_SHA2_128_24

/-- The compatibility bundle satisfies the key discipline. -/
example : shaPrimitives.core.KeyDiscipline
    (LimitedParameterSet.validatedParams .SLHDSA_SHA2_128_24) :=
  keyDiscipline_shaPrimitives

end SLHDSA.KeySeparationTest
