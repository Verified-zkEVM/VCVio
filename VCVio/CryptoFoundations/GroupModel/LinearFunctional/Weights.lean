/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.BigOperators.Field

import Mathlib.Tactic.Ring

-- Enumeration entry points inspected by the per-module initialization sweep.
import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Pi

/-! # Weighted linear targets and signature simulation

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). Weights describe a message's target as a linear
combination of independently sampled bases. The algebra does not require finite messages,
probability interpretations, or a query bound.
-/

public section

namespace GroupModel.LinearFunctional

/-- The scalar target obtained by combining a table with the message's weights. -/
@[expose] def targetScalar {F M ι : Type*} [Semiring F] [Fintype ι]
    (w : ι → M → F) (ρ : ι → F) (m : M) : F := ∑ i, ρ i * w i m

/-- The difference between the target's weights and the represented signing-query weights. -/
@[expose] def gapCoeff {F M ι Q : Type*} [Ring F] [Fintype Q]
    (w : ι → M → F) (m : M) (messages : Q → M) (coeff : Q → F) (i : ι) : F :=
  w i m - ∑ q, coeff q * w i (messages q)

/-- Honest signing of a weighted combination of public bases. -/
@[expose] def realSign {F M ι G : Type*} [Semiring F] [Fintype ι]
    [AddCommMonoid G] [Module F G] (w : ι → M → F) (α : F)
    (H : ι → G) (m : M) : G := α • ∑ i, w i m • H i

/-- Signing from a challenge point and a known scalar table. -/
@[expose] def simSign {F M ι G : Type*} [Semiring F] [Fintype ι]
    [AddCommMonoid G] [Module F G] (w : ι → M → F) (X : G)
    (ρ : ι → F) (m : M) : G := targetScalar w ρ m • X

/-- Scalar programming gives the honest signature without requiring the secret scalar. -/
theorem simSign_eq_realSign {F M ι G : Type*} [CommSemiring F] [Fintype ι]
    [AddCommMonoid G] [Module F G] (w : ι → M → F) (g : G)
    (α : F) (ρ : ι → F) (m : M) :
    simSign w (α • g) ρ m = realSign w α (fun i => ρ i • g) m := by
  simp only [simSign, realSign, targetScalar, Finset.smul_sum, smul_smul,
    Finset.sum_mul, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => by congr 1; ring

/-- The scalar verification gap is the functional with coordinates `gapCoeff`. -/
theorem targetScalar_sub_sum {F M ι Q : Type*} [CommRing F] [Fintype ι] [Fintype Q]
    (w : ι → M → F) (ρ : ι → F) (m : M) (messages : Q → M) (coeff : Q → F) :
    targetScalar w ρ m - ∑ q, coeff q * targetScalar w ρ (messages q) =
      ∑ i, gapCoeff w m messages coeff i * ρ i := by
  simp only [targetScalar, gapCoeff, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => by ring

end GroupModel.LinearFunctional
