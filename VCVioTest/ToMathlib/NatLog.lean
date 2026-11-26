/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.Data.Nat.Log

/-!
# Rounding up to a power of two

`Nat.pow_clog_le_mul_add_one` is attained at `n = 0`, where the `+ 1` is needed, and rounding up
can exceed `n`.
-/

public section

namespace VCVioTest.NatLog

example (n : ℕ) : 2 ^ Nat.clog 2 n ≤ 2 * n + 1 := Nat.pow_clog_le_mul_add_one 2 n

example : 2 ^ Nat.clog 2 0 = 2 * 0 + 1 := by simp

example : ¬ 2 ^ Nat.clog 2 0 ≤ 2 * 0 := by simp

example : 2 ^ Nat.clog 2 5 = 8 := by decide

example : ¬ 2 ^ Nat.clog 2 5 ≤ 5 := by decide

end VCVioTest.NatLog
