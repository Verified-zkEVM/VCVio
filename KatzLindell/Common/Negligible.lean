/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.Asymptotics.Negligible

/-!
# Katz–Lindell §3.1: Negligible Functions

Pedagogical bridge between the textbook definition of negligible functions and the
library's `negligible` (superpolynomial decay): Definition 3.5 of Katz and Lindell,
*Introduction to Modern Cryptography*, phrased with an explicit threshold `N`, together
with the closure properties of Proposition 3.7 as instances of the library lemmas.
-/

namespace KatzLindell

open ENNReal Filter

/-- **Katz–Lindell Definition 3.5**: `f` is negligible iff for every polynomial `p`
there exists a threshold `N` beyond which `f n` is below `1 / p n`. (The textbook's
strict `<` is equivalent to `≤` here since both sides quantify over all polynomials.) -/
theorem negligible_iff_forall_polynomial_exists_bound {f : ℕ → ℝ≥0∞} :
    negligible f ↔
      ∀ p : Polynomial ℕ, ∃ N, ∀ n > N, f n ≤ (↑(p.eval n) : ℝ≥0∞)⁻¹ := by
  rw [negligible_iff_forall_polynomial_eventually_le]
  refine forall_congr' fun p => ?_
  rw [Filter.eventually_atTop]
  exact ⟨fun ⟨N, hN⟩ => ⟨N, fun n hn => hN n hn.le⟩,
    fun ⟨N, hN⟩ => ⟨N + 1, fun n hn => hN n (by omega)⟩⟩

/-! ### Katz–Lindell Proposition 3.7

Closure properties of negligible functions: sums and polynomial multiples of negligible
functions are negligible. Both are direct instances of the library's closure lemmas. -/

-- Proposition 3.7 (1): the sum of two negligible functions is negligible.
example {f g : ℕ → ℝ≥0∞} (hf : negligible f) (hg : negligible g) :
    negligible (f + g) :=
  negligible_add hf hg

-- Proposition 3.7 (2): a polynomial multiple of a negligible function is negligible.
example {f : ℕ → ℝ≥0∞} (hf : negligible f) (p : Polynomial ℕ) :
    negligible fun n => ↑(p.eval n) * f n :=
  negligible_polynomial_mul hf p

end KatzLindell
