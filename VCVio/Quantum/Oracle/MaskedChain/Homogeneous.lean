/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.Homogeneous
public import VCVio.Quantum.Oracle.MaskedChain.Bounds

/-!
# Trace-homogeneous masked-chain bounds

The programmed-oracle endpoint bound holds for every fixed base function and public mask
tuple. Scaling it by the input trace supports branchwise analysis of query-bounded
preprocessing: each branch contributes its own mass, and these masses can be summed.
The bound here excludes the birthday error from coupling to the real challenge.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Quantum.MaskedChain

/-- Guessing and online hybrid errors in the mask-first experiment, before the classical
collision error for the real challenge is added. -/
@[expose]
noncomputable def patchedRecoveryBound (G : Type) [Fintype G] (q k : ℕ) : ℝ≥0∞ :=
  (Fintype.card G : ℝ≥0∞)⁻¹ + 4 * ∑ h ∈ Finset.range q,
    ((k : ℝ≥0∞) * ((q - h : ℕ) : ℝ≥0∞) / Fintype.card G) ^ (2⁻¹ : ℝ)

/-- The real-challenge bound adds exactly one birthday error to its mask-first bound. -/
theorem recoveryBound_eq_patchedRecoveryBound_add_collision (G : Type) [Fintype G]
    (q k : ℕ) :
    recoveryBound G q k = patchedRecoveryBound G q k +
      (((q + 2).choose 2 : ℕ) : ℝ≥0∞) / Fintype.card G := by
  unfold recoveryBound patchedRecoveryBound
  ac_rfl

universe u v
variable {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G]
  {L : LocalSig.{u, v}}

/-- The mask-first success probability scales with the successful input mass.
The base function and masks are fixed; the online family and input may depend on that base
function, while the averaged hidden vertices remain independent of them. -/
theorem averageHybridSuccess_zero_le_mul_mass {q : ℕ} (I : L.Interp)
    (adv : OnlineAdversary L G q) (H : G → G) (masks : Fin (q + 1) → G) (k : ℕ)
    (hq : ∀ puzzle, (adv.run puzzle).IsTotalQueryBound q)
    (hk : ∀ puzzle, (adv.run puzzle).IsWidthBound k) :
    averageHybridSuccess I adv H masks 0 ≤
      adv.initialState.mass * patchedRecoveryBound G q k := by
  let normalized : OnlineAdversary L G q :=
    { adv with initialState := adv.initialState.normalize }
  have he : averageHybridSuccess I adv H masks 0 =
      adv.initialState.mass * averageHybridSuccess I normalized H masks 0 := by
    unfold averageHybridSuccess
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro vertices _
    unfold hybridSuccess
    rw [QuantumRuntime.evalDistMap_apply_eq_mass_mul_normalize]
    change _ * (adv.initialState.mass * _) = adv.initialState.mass * (_ * _)
    ring
  rw [he]
  apply mul_le_mul le_rfl _ bot_le bot_le
  exact (averageHybridSuccess_le_last I normalized H masks k hk).trans
    (add_le_add (averageHybridSuccess_last_le I normalized H masks hq) le_rfl)

end Quantum.MaskedChain
