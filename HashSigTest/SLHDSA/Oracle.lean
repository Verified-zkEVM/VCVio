/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Oracle

/-!
# Producer canaries for the SLH-DSA public-hash syntax

These examples pin the random-oracle query identity.  They reject implementations that erase the
function tag, public seed, full address, or left/right ordering.
-/

public section

namespace SLHDSA.PublicHashTest

abbrev Q := PublicHashQuery Nat Nat

example :
    (PublicHashQuery.f 0 Adrs.zero 7 : Q) ≠ PublicHashQuery.f 1 Adrs.zero 7 := by
  decide

example :
    (PublicHashQuery.h 0 Adrs.zero 3 5 : Q) ≠
      PublicHashQuery.h 0 (Adrs.zero.setLayerAddress 1) 3 5 := by
  decide

example :
    (PublicHashQuery.h 0 Adrs.zero 3 5 : Q) ≠ PublicHashQuery.h 0 Adrs.zero 5 3 := by
  decide

example :
    (PublicHashQuery.f 0 Adrs.zero 7 : Q) ≠ PublicHashQuery.h 0 Adrs.zero 7 7 := by
  decide

example :
    (PublicHashQuery.tl 0 Adrs.zero [3, 5] : Q) ≠ PublicHashQuery.tl 0 Adrs.zero [5, 3] := by
  decide

example :
    (PublicHashQuery.tl 0 Adrs.zero [3] : Q) ≠ PublicHashQuery.tl 0 Adrs.zero [3, 0] := by
  decide

end SLHDSA.PublicHashTest
