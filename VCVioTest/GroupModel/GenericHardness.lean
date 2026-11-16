/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericHardness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

/-!
# Concrete generic adversaries for discrete logarithms and Diffie–Hellman

The discrete-logarithm adversary uses free comparisons with the generator and the zero default.
It needs no group operations and wins with probability exactly `3/5` over the field with five
elements, below the generic bound `4/5` and above the `1/5` of a blind guess, so the bound's
collision term cannot be dropped. The non-generic adversary that returns its challenge wins with
probability `1`, so the bound depends on genericity. The computational Diffie–Hellman adversary
adds the two challenges; over the field with 101 elements its bound is `12/101`.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace GroupModel

/-- Comparing the challenge with the generator and zero costs no group operations; the
resulting discrete-logarithm adversary has success probability at most `4/5`. -/
theorem dlog_generic_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let A : OracleComp (genSpec (ZMod 5) groupSig) (ZMod 5) := do
      let one : Bool ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () 1 0))
      let zero : Bool ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () 1 2))
      pure (if one = true then 1 else if zero = true then 0 else 2)
    Pr{let b ← DiffieHellman.dlogExperiment (1 : ZMod 5) (DLogAdversary.ofGeneric A)}[b = true] ≤
      (4 / 5 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  dsimp only
  apply (dlogExperiment_ofGeneric_le (1 : ZMod 5) one_ne_zero _ 0 ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => ⟨by decide, fun _ => trivial⟩⟩

/-- The same adversary wins with probability exactly `3/5`: it answers the challenges `1` and
`0` from its comparisons and guesses `2` otherwise. -/
theorem dlog_generic_zmod_five_exact :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let A : OracleComp (genSpec (ZMod 5) groupSig) (ZMod 5) := do
      let one : Bool ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () 1 0))
      let zero : Bool ← (genSpec (ZMod 5) groupSig).query (.inl (.eq () 1 2))
      pure (if one = true then 1 else if zero = true then 0 else 2)
    Pr{let b ← DiffieHellman.dlogExperiment (1 : ZMod 5) (DLogAdversary.ofGeneric A)}[b = true] =
      (3 / 5 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro A
  have hrun (x : ZMod 5) :
      DLogAdversary.ofGeneric (G := ZMod 5) A 1 (x • 1) =
        pure (if x = 1 then 1 else if x = 0 then 0 else 2) := by
    have hx : x • (1 : ZMod 5) = x := by simp
    rw [hx]
    change (pure (if decide (x = 1) = true then 1 else if decide (x = 0) = true then 0 else 2) :
      ProbComp (ZMod 5)) = _
    simp
  have hc : (Finset.univ.filter fun x : ZMod 5 =>
      (if x = 1 then (1 : ZMod 5) else if x = 0 then 0 else 2) = x).card = 3 := by decide
  simp only [DiffieHellman.dlogExperiment, hrun, pure_bind, prEvent_norm, decide_eq_true_eq]
  rw [SampleableType.prEvent_uniformSample, hc]
  simp [ZMod.card]

/-- The non-generic adversary that returns its challenge wins with probability `1`. -/
theorem dlog_read_challenge :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    Pr{let b ← DiffieHellman.dlogExperiment (1 : ZMod 5)
        (fun _ X => pure X : DiffieHellman.DLogAdversary (ZMod 5) (ZMod 5))}[b = true] = 1 := by
  simp [DiffieHellman.dlogExperiment]

/-- Adding the two challenges costs one group operation; the generic CDH bound evaluates to
`12/101` over the field with 101 elements. -/
theorem cdh_generic_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by norm_num⟩
    let A : OracleComp (genSpec (ZMod 101) groupSig) Handle :=
      (genSpec (ZMod 101) groupSig).query (.inl (.add () 1 2))
    Pr{let b ← DiffieHellman.cdhExperiment (1 : ZMod 101) (CDHAdversary.ofGeneric A)}[b = true] ≤
      (12 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by norm_num⟩
  dsimp only
  apply (cdhExperiment_ofGeneric_le (1 : ZMod 101) one_ne_zero _ 1 ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => trivial⟩

end GroupModel
