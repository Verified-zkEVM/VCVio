/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVioFoxglove.Tactic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Goal corpus for `vcgen` with Foxglove

Each goal is closed by a bare `vcgen`, unless marked as a negative (`fail_if_success`). The
families follow the routes of `VCVioFoxglove.Tactic`:

* **Leaf laws:** Foxglove laws of VCVio's samplers.
* **Independence:** Foxglove independence of a sample and an independent sampler, and of
  post-processed components.
* **Events:** VCVio event goals decided by independence.
* **Delegated:** VCVio goals that the Foxglove routes leave to VCVio's `vcgen`.
* **Negatives:** dependent draws, where independence must not be claimed.
-/

open OracleComp OracleSpec Foxglove Interp
open scoped ENNReal

namespace VCVioFoxgloveTest.Corpus

/-! ## Leaf laws -/

example : ⊢ wp ($ᵗ Bool : ProbComp Bool) ⦃X, X ~ PMF.uniformOfFintype' Bool⦄ := by vcgen

example : ⊢ wp ($ᵗ (Fin 5) : ProbComp (Fin 5)) ⦃X, X ~ PMF.uniformOfFintype' (Fin 5)⦄ := by
  vcgen

example (n : ℕ) :
    ⊢ wp (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
      ⦃X, X ~ PMF.uniformOfFintype' (Fin (n + 1))⦄ := by
  vcgen

example (x : Fin 3) : ⊢ wp (pure x : ProbComp (Fin 3)) ⦃X, X ~ δ x⦄ := by vcgen

/-! ## Independence -/

/-- Two independent fair coins. -/
noncomputable def twoCoins : ProbComp (Bool × Bool) := do
  let a ← $ᵗ Bool
  let b ← $ᵗ Bool
  pure (a, b)

/-- A fair coin and an independent uniform `Fin 3`. -/
noncomputable def coinAndFin : ProbComp (Bool × Fin 3) := do
  let a ← $ᵗ Bool
  let b ← $ᵗ (Fin 3)
  pure (a, b)

example : ⊢ wp twoCoins ⦃X, (Prod.fst ∘ X) ~ PMF.uniformOfFintype' Bool ∗
    (Prod.snd ∘ X) ~ PMF.uniformOfFintype' Bool⦄ := by
  unfold twoCoins; vcgen

example : ⊢ wp coinAndFin ⦃X, (Prod.fst ∘ X) ~ PMF.uniformOfFintype' Bool ∗
    (Prod.snd ∘ X) ~ PMF.uniformOfFintype' (Fin 3)⦄ := by
  unfold coinAndFin; vcgen

example (f : Bool → ProbComp (Fin 3)) (hf : 𝒟[f true] = 𝒟[f false]) :
    ⊢ wp (do
        let a ← ($ᵗ Bool : ProbComp Bool)
        let b ← f a
        pure (a, b))
      ⦃X, (Prod.fst ∘ X) ~ PMF.uniformOfFintype' Bool ∗
        (Prod.snd ∘ X) ~ lawPMF (BernoulliInterpretable.interp (f default))⦄ := by
  vcgen

/-! ## Events -/

-- `ProbComp.evalDist_decide_eq_uniformBool_half`, 31 lines by hand
example (f : Bool → ProbComp Bool) (heq : 𝒟[f true] = 𝒟[f false]) :
    𝒟[do let b ← ($ᵗ Bool); let b' ← f b; return decide (b = b')] {true} = 1 / 2 := by
  vcgen

-- the guess of an independent draw
example (mx : ProbComp Bool) :
    𝒟[do let b ← ($ᵗ Bool); let b' ← mx; return decide (b = b')] {true} = 1 / 2 := by
  vcgen

-- a guess of a uniform `Fin 4` value, from a sampler whose law does not depend on it
example (g : Fin 4 → ProbComp (Fin 4)) (hg : ∀ a, 𝒟[g a] = 𝒟[g default]) :
    𝒟[do let a ← ($ᵗ (Fin 4)); let b ← g a; return decide (a = b)] {true} = 4⁻¹ := by
  vcgen

-- events of independent components multiply
example (p : Bool → Prop) (q : Fin 3 → Prop) :
    Pr{let x ← coinAndFin}[p x.1 ∧ q x.2]
      = Pr{let x ← coinAndFin}[p x.1] * Pr{let x ← coinAndFin}[q x.2] := by
  unfold coinAndFin; vcgen

-- the output measure of two independent draws is the product
example : 𝒟[twoCoins] = (PMF.uniformOfFintype' Bool ⊗ PMF.uniformOfFintype' Bool).toMeasure := by
  unfold twoCoins; vcgen

/-! ## Delegated to VCVio's `vcgen` -/

example : Pr{let b ← $ᵗ Bool}[(b || true) = true] = 1 := by vcgen

example : (4⁻¹ : ℝ≥0∞) ≤ Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b && c) = true] := by
  vcgen
  norm_num [ENNReal.div_eq_inv_mul, Finset.filter_insert, Finset.filter_singleton,
    ← ENNReal.mul_inv]

/-! ## Negatives -/

/-- A coin and itself: the two components are not independent. -/
noncomputable def coinTwice : ProbComp (Bool × Bool) := do
  let a ← $ᵗ Bool
  pure (a, a)

-- the Foxglove attempt (an independent guess, `1 / 2`) fails and is rolled back, and VCVio's
-- `vcgen` proves the true value
example : Pr{let x ← coinTwice}[x.1 = x.2] = 1 := by
  unfold coinTwice; vcgen

-- and the false value is not proved
example : True := by
  fail_if_success
    have : Pr{let x ← coinTwice}[x.1 = x.2] = 1 / 2 := by unfold coinTwice; vcgen
  trivial

end VCVioFoxgloveTest.Corpus
