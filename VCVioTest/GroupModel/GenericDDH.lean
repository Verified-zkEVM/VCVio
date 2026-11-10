/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericDDH
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

/-!
# A generic DDH comparison

The adversary adds the two challenge handles and compares their sum with the target.
This uses one group operation and one free equality query. Over the field with 101 elements
the generic DDH bound at `q = 1` is `45/101`, below one. Over the field with five elements the
real experiment accepts with probability exactly `4/25`: the target `x₀x₁` equals `x₀ + x₁` at
four of the twenty-five challenge pairs.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace GroupModel

/-- Comparing the target with the sum of the challenges uses one group operation;
the generic DDH bound at `q = 1` over the field with 101 elements evaluates to `45/101`. -/
theorem ddh_generic_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by norm_num⟩
    let A : OracleComp (genSpec (ZMod 101) groupSig) Bool := do
      let sum ← (genSpec (ZMod 101) groupSig).query (.inl (.add () 1 2))
      (genSpec (ZMod 101) groupSig).query (.inl (.eq () 3 sum))
    DiffieHellman.ddhAdvantage (1 : ZMod 101) (DDHAdversary.ofGeneric A) ≤
      (45 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by norm_num⟩
  dsimp only
  apply (ddhAdvantage_ofGeneric_le (1 : ZMod 101) one_ne_zero _ 1 ?_).trans
  · exact le_of_eq (by norm_num [ZMod.card, Nat.choose])
  · exact ⟨by decide, fun _ => ⟨Or.inl (by intro h; cases h), fun _ => trivial⟩⟩

/-- Over the field with five elements the same adversary accepts the real DDH triple with
probability exactly `4/25`. -/
theorem ddh_generic_zmod_five_real_exact :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let A : OracleComp (genSpec (ZMod 5) groupSig) Bool := do
      let sum ← (genSpec (ZMod 5) groupSig).query (.inl (.add () 1 2))
      (genSpec (ZMod 5) groupSig).query (.inl (.eq () 3 sum))
    Pr{let b ← DiffieHellman.ddhRealExperiment (1 : ZMod 5)
        (DDHAdversary.ofGeneric A)}[b = true] = (4 / 25 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro A
  have hrun (X Y T : ZMod 5) :
      DDHAdversary.ofGeneric (G := ZMod 5) A 1 X Y T = pure (decide (T = X + Y)) := rfl
  have hpair (p : ZMod 5 → ZMod 5 → Prop) [DecidableRel p] :
      Pr{let a ← $ᵗ (ZMod 5); let b ← $ᵗ (ZMod 5)}[p a b] =
        Pr{let ab ← $ᵗ (ZMod 5 × ZMod 5)}[p ab.1 ab.2] := by
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp [prEvent_norm]
  have hc : (Finset.univ.filter fun ab : ZMod 5 × ZMod 5 =>
      (ab.1 * ab.2) • (1 : ZMod 5) = ab.1 • 1 + ab.2 • 1).card = 4 := by decide
  simp only [DiffieHellman.ddhRealExperiment, hrun, prEvent_norm, decide_eq_true_eq]
  rw [hpair (fun a b => (a * b) • (1 : ZMod 5) = a • 1 + b • 1),
    SampleableType.prEvent_uniformSample, hc]
  simp [ZMod.card]

end GroupModel
