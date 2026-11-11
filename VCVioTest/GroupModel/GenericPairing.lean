/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericPairing
public import Mathlib.Algebra.Field.ZMod

/-!
# Numerical Type 3 powers discrete-logarithm tests

The adversary pairs its two challenge handles, pairs the two generator handles, compares the
products in the target group and guesses `1` on equality and `0` otherwise. It reads the
challenge only through the pairing query, so its success pins how `PairingDLog.Adversary.ofGeneric`
lays out the powers: over the field with five elements, with `q₁ = q₂ = 1`, it wins exactly when
the exponent is `0` or `1`, with probability `2/5`, while every constant guess wins with
probability `1/5`. Over the field with 101 elements the `(1, 1)`-DLog bound for the same
adversary is `13/101`.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace GroupModel

/-- Two target appends and no source appends give the bound `13/101` for the `(1, 1)`-DLog
experiment with multiplication as its pairing. -/
theorem pairing_dlog_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    let A : OracleComp (genSpec (ZMod 101) pairingSig) (ZMod 101) := do
      let _ ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 1 1))
      let _ ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 0 0))
      let same : Bool ← (genSpec (ZMod 101) pairingSig).query (.inl (.eq .gₜ 0 1))
      pure (if same then 1 else 0)
    Pr{let b ← (PairingDLog.experiment (1 : ZMod 101) 1
      (PairingDLog.Adversary.ofGeneric (q₁ := 1) (q₂ := 1)
        (LinearMap.mul (ZMod 101) (ZMod 101)) A))}[b = true] ≤ (13 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  dsimp only
  apply (PairingDLog.experiment_ofGeneric_le
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : ZMod 101) ≠ 0))
    1 1 _ 0 0 2 ?_ ?_ ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  all_goals exact ⟨by decide, fun _ => ⟨by decide, fun _ => ⟨by decide, fun _ => trivial⟩⟩⟩

/-- Over the field with five elements the same adversary wins with probability exactly `2/5`:
the products agree exactly when the exponent squares to one, and the guesses `1` and `0` are
right at the exponents `1` and `0`. -/
theorem pairing_dlog_zmod_five_exact :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let A : OracleComp (genSpec (ZMod 5) pairingSig) (ZMod 5) := do
      let _ ← (genSpec (ZMod 5) pairingSig).query (.inl (.bil () 1 1))
      let _ ← (genSpec (ZMod 5) pairingSig).query (.inl (.bil () 0 0))
      let same : Bool ← (genSpec (ZMod 5) pairingSig).query (.inl (.eq .gₜ 0 1))
      pure (if same then 1 else 0)
    Pr{let b ← (PairingDLog.experiment (1 : ZMod 5) 1
      (PairingDLog.Adversary.ofGeneric (q₁ := 1) (q₂ := 1)
        (LinearMap.mul (ZMod 5) (ZMod 5)) A))}[b = true] = (2 / 5 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro A
  have hrun (x : ZMod 5) :
      PairingDLog.Adversary.ofGeneric (q₁ := 1) (q₂ := 1) (LinearMap.mul (ZMod 5) (ZMod 5)) A
          (fun i => x ^ (i : ℕ) • (1 : ZMod 5)) (fun j => x ^ (j : ℕ) • (1 : ZMod 5)) =
        pure (if x * x = 1 then 1 else 0) := by
    change (pure (if decide ((pairingReal (LinearMap.mul (ZMod 5) (ZMod 5))).bil ()
        (x ^ 1 • (1 : ZMod 5) : ZMod 5) (x ^ 1 • (1 : ZMod 5) : ZMod 5) =
        (pairingReal (LinearMap.mul (ZMod 5) (ZMod 5))).bil ()
          (x ^ 0 • (1 : ZMod 5) : ZMod 5) (x ^ 0 • (1 : ZMod 5) : ZMod 5)) = true
        then (1 : ZMod 5) else 0) : ProbComp (ZMod 5)) = _
    erw [pairingReal_bil_apply, pairingReal_bil_apply]
    congr 1
    revert x
    decide
  have hc : (Finset.univ.filter fun x : ZMod 5 =>
      (if x * x = 1 then (1 : ZMod 5) else 0) = x).card = 2 := by decide
  simp only [PairingDLog.experiment, hrun, pure_bind, prEvent_norm, decide_eq_true_eq]
  rw [SampleableType.prEvent_uniformSample, hc]
  simp [ZMod.card]

end GroupModel
