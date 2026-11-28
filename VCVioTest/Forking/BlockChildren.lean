/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.BlockChildren
public import Mathlib.Data.Fin.VecNotation

/-!
# Regression checks for the block step with probabilistic children

**Distinct indices are needed.** With three coin flips, reading index `0` twice is not drawing it
twice: the second can give `[true, false]` and the first cannot. So the hypothesis of
`Fintype.mPi_map_list` that the indices are distinct is not vacuous.

**The eager lemma at a dependent product.** `Rewinding.blockChildren_eager_table` is instantiated at
challenges with a first coordinate over `Fin 5` and a second over `Fin 3`, with the neighbour pools
of a concrete centre, so its instance arguments are synthesized at a dependent product.

**The cost clause.** Children that each cost one call give the block step an expected cost of at
most `1 + 2 + 1 = 4`, the size of a star.

**The success clause forces success.** A child that succeeds on the challenges whose first
coordinate is not `4` succeeds with probability `ε = 12/15`, above the error `κ = 2/5 + 1/3 = 11/15`
of thresholds `(3, 2)`. `prEvent_child_le_blockChildStep` then forces the block step to succeed
with positive probability.
-/

public section

open OracleComp Rewinding CoordinateWise

open scoped ENNReal

namespace BlockChildrenTest

/-- Three independent coin flips. -/
noncomputable def coins : Fin 3 → ProbComp Bool := fun _ => $ᵗ Bool

/-- Reading index `0` twice is not drawing it twice: distinct indices are needed. -/
example : ¬ (((fun T => [0, 0].map T) <$> Fintype.mPi coins) =ᵈ [0, 0].mapM coins) := by
  intro h
  have h1 : [true, false] ∈ support ([0, 0].mapM coins) := by simp [coins]
  rw [← support_eq_of_evalDistEq h] at h1
  simp at h1

/-- The first coordinate ranges over `Fin 5`, the second over `Fin 3`. -/
abbrev alph : Fin 2 → Type
  | 0 => Fin 5
  | 1 => Fin 3

instance : ∀ u, DecidableEq (alph u)
  | 0 => inferInstanceAs (DecidableEq (Fin 5))
  | 1 => inferInstanceAs (DecidableEq (Fin 3))

instance : ∀ u, Fintype (alph u)
  | 0 => inferInstanceAs (Fintype (Fin 5))
  | 1 => inferInstanceAs (Fintype (Fin 3))

instance : ∀ u, Nonempty (alph u)
  | 0 => inferInstanceAs (Nonempty (Fin 5))
  | 1 => inferInstanceAs (Nonempty (Fin 3))

noncomputable instance : SampleableType ((u : Fin 2) → alph u) :=
  SampleableType.piOfFintype alph

/-- Thresholds `(3, 2)`. -/
def k : Fin 2 → ℕ := ![3, 2]

/-- The centre `(1, 2)`. -/
def c₀ : (u : Fin 2) → alph u
  | 0 => (1 : Fin 5)
  | 1 => (2 : Fin 3)

/-- A child that succeeds on the challenges whose first coordinate is not `4`, at cost `1`. -/
noncomputable def child (c : (u : Fin 2) → alph u) : ProbComp (Option Unit × ℕ) :=
  pure (if (c 0 : Fin 5).val ≠ 4 then some () else none, 1)

/-- The eager lemma at the neighbour pools of `c₀`. -/
example : (blockChildren (fun n => StateT.lift (ProbComp.uniformFin n)) (chargedChild child) k c₀
      (neighbourPool c₀)).run 0 =ᵈ
    (do
      let T ← Fintype.mPi child
      (blockChildren (fun n => StateT.lift (ProbComp.uniformFin n)) (tableChild ∘ T) k c₀
        (neighbourPool c₀)).run 0) :=
  blockChildren_eager_table child k c₀ (neighbourPool c₀) (nodup_neighbourPool c₀)
    (fun _ _ _ h h' => eq_of_mem_neighbourPool h h') (centre_notMem_neighbourPool c₀) 0

/-- Twelve of the fifteen challenges have a first coordinate other than `4`. -/
theorem card_accept : (Finset.univ.filter fun c : (u : Fin 2) → alph u =>
    (c 0 : Fin 5).val ≠ 4).card = 12 := by
  decide +kernel

/-- The child succeeds with probability `12/15`. -/
theorem prEvent_child :
    Pr{let z ← (do let c ← $ᵗ ((u : Fin 2) → alph u); child c)}[z.1.isSome] = 12 / 15 := by
  simp only [child, bind_pure_comp, Functor.map_map, SampleableType.prEvent_uniformSample]
  have hcard : Fintype.card ((u : Fin 2) → alph u) = 15 := by decide +kernel
  have hfilter : (Finset.univ.filter fun c : (u : Fin 2) → alph u =>
      ((if (c 0 : Fin 5).val ≠ 4 then some () else none : Option Unit)).isSome = true) =
      Finset.univ.filter fun c : (u : Fin 2) → alph u => (c 0 : Fin 5).val ≠ 4 := by
    ext c
    by_cases h : (c 0 : Fin 5).val ≠ 4 <;> simp [h]
  rw [hfilter, card_accept, hcard]
  norm_num

/-- With `ε = 12/15` above `κ = 11/15`, the block step succeeds with positive probability. -/
example : Pr{let z ← blockChildStep child k}[z.1.isSome] ≠ 0 := by
  intro hp
  have h := prEvent_child_le_blockChildStep child k
  rw [prEvent_child, hp, mul_zero, add_zero, Fin.sum_univ_two] at h
  have h5 : Fintype.card (alph 0) = 5 := by decide
  have h3 : Fintype.card (alph 1) = 3 := by decide
  simp only [k, h5, h3, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have h1 : ((3 - 1 : ℕ) : ℝ≥0∞) / ((5 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have h2 : ((2 - 1 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  rw [← ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) (by simp))
    (ENNReal.add_ne_top.mpr ⟨h1, h2⟩), ENNReal.toReal_add h1 h2, ENNReal.toReal_div,
    ENNReal.toReal_div, ENNReal.toReal_div] at h
  norm_num at h

/-- Children that each cost one call give the block step an expected cost of at most `4`. -/
example : Rewinding.expectedCalls (blockChildStep child k) ≤ 4 := by
  refine (expectedCalls_blockChildStep_le child k).trans (le_of_eq ?_)
  simp only [child, Rewinding.expectedCalls_pure, Nat.cast_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Fin.sum_univ_two, k]
  have hcard : (Fintype.card ((u : Fin 2) → alph u) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.div_self hcard (ENNReal.natCast_ne_top _)]
  norm_num

end BlockChildrenTest
