/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.AddressDiscipline
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Concrete.Instance
import HashSig.SLHDSA.Security.AddressKeys

/-!
# Key separation of the concrete SLH-DSA bundles

`CorePrimitives.KeySeparated` says that no address of type at most `4` shares its oracle key with
a secret-key address. A bundle whose oracle key encodes the address type injectively satisfies
it at every address:

* `Concrete.keySeparated_shakePrimitives`: the SHAKE bundles, whose oracle key is the full
  32-byte address with its four-byte type block;
* `Concrete.keySeparated_shaPrimitives`: the SLH-DSA-SHA2-128-24 compatibility bundle, whose
  oracle key is the compressed address `ADRSc` with its one-byte type block.

The FIPS SHA-2 bundles `Concrete.sha2Primitives` send every address outside the checked `ADRSc`
domain to the all-zero key, the key of an address of type `0`, so they are not key-separated at
every address.
-/

public section

namespace SLHDSA

/-- Equal big-endian encodings of one width encode equal values below the width's bound. -/
private theorem eq_of_toBytesBE_eq {x y w : ℕ} (hx : x < 256 ^ w) (hy : y < 256 ^ w)
    (h : Adrs.toBytesBE x w = Adrs.toBytesBE y w) : x = y := by
  have h' := congrArg toInt h
  simp only [Adrs.toBytesBE] at h'
  rwa [toInt_toByte _ _ hx, toInt_toByte _ _ hy] at h'

/-- A secret-key address has type `5` or `6`. -/
private theorem Adrs.IsSecretKey.type_eq {a : Adrs} (ha : a.IsSecretKey) :
    a.type = 5 ∨ a.type = 6 := ha

namespace Concrete

/-- The SHAKE bundles are key-separated: their oracle key is the full 32-byte address, whose type
block separates the secret-key types from the types at most `4`. -/
theorem keySeparated_shakePrimitives (p : Params) : (shakePrimitives p).core.KeySeparated := by
  intro a b ha hb h
  have hbytes : a.toBytes = b.toBytes := by
    have h' := congrArg Vector.toList h
    simpa only [Primitives.core, shakePrimitives, Adrs.toVector, Vector.toList_mk,
      List.toList_toArray] using h'
  have := eq_of_toBytesBE_eq (w := 4) (by rcases ha.type_eq with h | h <;> rw [h] <;> norm_num)
    (by omega) (Security.toBytes_blocks hbytes).2.2.1
  rcases ha.type_eq with h | h <;> omega

/-- The SLH-DSA-SHA2-128-24 compatibility bundle is key-separated: its oracle key is the
compressed address `ADRSc`, whose one-byte type block separates the secret-key types from the
types at most `4`. -/
theorem keySeparated_shaPrimitives : shaPrimitives.core.KeySeparated := by
  intro a b ha hb h
  have hbytes : a.compressSha2 = b.compressSha2 := by
    rw [← shaAdrsKey_toList, ← shaAdrsKey_toList]
    exact congrArg Vector.toList h
  have := eq_of_toBytesBE_eq (w := 1) (by rcases ha.type_eq with h | h <;> rw [h] <;> norm_num)
    (by omega) (Security.compressSha2_blocks hbytes).2.2.1
  rcases ha.type_eq with h | h <;> omega

end Concrete

end SLHDSA
