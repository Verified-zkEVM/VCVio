/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Algorithms.CRC

/-! # CRC register checks and ordinary-import chunking laws -/

public section

open VCVio.Algorithms.Crc

namespace Cryptol.Tests.CRC

/-- The ASCII check string `123456789`. -/
def message : List (BitVec 8) := [49, 50, 51, 52, 53, 54, 55, 56, 57]

/-- Foundation's CCITT-FALSE parameter values. -/
def ccitt : Parameters 16 := ⟨0x1021, 0xffff, false, false, 0⟩
/-- Foundation's IEEE-802.3 parameter values. -/
def ethernet : Parameters 32 := ⟨0x04c11db7, 0xffffffff, true, true, 0xffffffff⟩

set_option maxRecDepth 10000

example : checksum ccitt message = 0x29b1 := by decide
example : checksum ethernet message = 0xcbf43926 := by decide

example {width : Nat} (p : Parameters width) (state : BitVec width)
    (xs ys : List (BitVec 8)) :
    updateResult p state (xs ++ ys) = updateResult p (updateResult p state xs).state ys :=
  updateResult_append p state xs ys

-- A nonsymmetric mask distinguishes XOR-before-reflection from the opposite order.
example : finalize (⟨7, 0, false, true, 1⟩ : Parameters 8) 0 = 128 := by decide

-- Feeding a finalized checksum back as running state does change the next result.
example : update ethernet (updateResult ethernet ethernet.initial [49]).state [50] ≠
    update ethernet (updateResult ethernet ethernet.initial [49]).crc [50] := by decide

end Cryptol.Tests.CRC
