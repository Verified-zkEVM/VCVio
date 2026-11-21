/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Data.Nat.Log

/-!
# Rounding up to a power

`Nat.pow_clog_le_mul_add_one`: rounding `n` up to a power of `b` costs less than a factor of `b`,
`b ^ ⌈log_b n⌉ ≤ b * n + 1`. The `+ 1` is needed only at `n = 0`, where `b ^ 0 = 1`.
-/

public section

namespace Nat

/-- Rounding up to a power of `b` costs less than a factor of `b`: `b ^ ⌈log_b n⌉ ≤ b * n + 1`. -/
theorem pow_clog_le_mul_add_one (b n : ℕ) : b ^ clog b n ≤ b * n + 1 := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · rcases Nat.lt_or_ge 1 b with hb | hb
    · obtain ⟨c, hc⟩ := Nat.exists_eq_add_one_of_ne_zero (clog_pos hb hn).ne'
      have h := pow_pred_clog_lt_self b hn
      rw [hc, Nat.pred_succ] at h
      rw [hc, Nat.pow_succ']
      exact (Nat.mul_le_mul_left b h.le).trans (Nat.le_succ _)
    · rw [clog_of_left_le_one hb, Nat.pow_zero]
      omega
  · rw [clog_of_right_le_one hn, Nat.pow_zero]
    omega

end Nat
