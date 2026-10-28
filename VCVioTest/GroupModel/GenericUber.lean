/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericUberDecisional
public import Mathlib.Algebra.Field.ZMod

/-! # Numerical computational and decisional uber bounds

The lists `[1, X]`, `[1, X]`, `[]` have target accessible span `span {1, X, X²}`.
The target `X³` is independent. One pairing and one equality query give computational
success at most `11/101` and decisional advantage at most `27/101` over `ZMod 101`.
-/

public section

open OracleComp OracleSpec MvPolynomial
open scoped ENNReal

namespace GroupModel

private theorem cubic_not_mem {F : Type} [Field F] :
    (X (0 : Fin 1) ^ 3 : MvPolynomial (Fin 1) F) ∉
      accessibleSpan pairingSig (uberTable [1, X 0] [1, X 0] []) .gₜ := by
  intro h
  rw [accessibleSpan_pairingSig] at h
  have hd : ∀ p ∈ pairingSpan (uberTable [1, X 0] [1, X 0] ([] : List (MvPolynomial (Fin 1) F)))
      .gₜ, p.totalDegree ≤ 2 := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      rcases hp with hp | ⟨a, ha, b, hb, rfl⟩
      · exact False.elim (List.not_mem_nil hp)
      · have ha : a = 1 ∨ a = X 0 := by simpa [uberTable] using ha
        have hb : b = 1 ∨ b = X 0 := by simpa [uberTable] using hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
          norm_num [← pow_two, totalDegree_X_pow]
    | zero => simp
    | add p q _ _ hp hq => exact (totalDegree_add _ _).trans (max_le hp hq)
    | smul c p _ hp => exact (totalDegree_smul_le c p).trans hp
  have hh := hd _ h
  norm_num only [totalDegree_X_pow] at hh

private theorem table_degreeLE {F : Type} [Field F] (d : ℕ) :
    DegreeLE (fun | .g₁ => 1 | .g₂ => 1 | .gₜ => d)
      (uberTable [1, X 0] [1, X 0] ([] : List (MvPolynomial (Fin 1) F))) := by
  intro s p hp
  cases s with
  | g₁ | g₂ =>
    have hp : p = 1 ∨ p = X 0 := by simpa [uberTable] using hp
    rcases hp with rfl | rfl <;> simp
  | gₜ => exact False.elim (List.not_mem_nil hp)

/-- One pairing and one equality query give computational uber success at most `11/101`.
The adversary compares the pairing of the two `X` entries with the zero default,
returning that default handle when the comparison succeeds. -/
theorem uber_computational_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    letI : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
      fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
    let A : OracleComp (genSpec (ZMod 101) pairingSig) Handle := do
      let t : Handle ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 1 1))
      let b : Bool ← (genSpec (ZMod 101) pairingSig).query (.inl (.eq .gₜ t (t + 1)))
      pure (if b then t + 1 else t)
    Pr{let b ← (Uber.computationalExperiment (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1
      [1, X (0 : Fin 1)] [1, X 0] [] (X 0 ^ 3)
      (Uber.ComputationalAdversary.ofGeneric (LinearMap.mul (ZMod 101) (ZMod 101)) A))}[
        b = true] ≤ (11 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
    fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
  dsimp only
  apply (Uber.experiment_ofGeneric_le
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1 one_ne_zero one_ne_zero
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : ZMod 101) ≠ 0))
    [1, X 0] [1, X 0] [] (X 0 ^ 3) cubic_not_mem
    (degreeClosed_pairingSig 1 1 2) (table_degreeLE 2)
    _ (n := fun | .g₁ => 0 | .g₂ => 0 | .gₜ => 1) ?_ 3 (by simp)).trans
  · norm_num [ZMod.card, Nat.choose]
  · intro s
    cases s <;>
      exact ⟨by decide, fun _ => ⟨(by left; intro h; cases h), fun _ => trivial⟩⟩

/-- One pairing and one equality query give decisional uber advantage at most `27/101`.
The adversary compares the appended challenge with the pairing of the two `X` entries. -/
theorem uber_decisional_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    letI : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
      fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
    let A : OracleComp (genSpec (ZMod 101) pairingSig) Bool := do
      let t : Handle ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 1 1))
      (genSpec (ZMod 101) pairingSig).query (.inl (.eq .gₜ t 0))
    Uber.advantage (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1
      [1, X (0 : Fin 1)] [1, X 0] [] (X 0 ^ 3)
      (Uber.DecisionalAdversary.ofGeneric (LinearMap.mul (ZMod 101) (ZMod 101)) A) ≤
        (27 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let : ∀ s, DecidableEq (PFam (ZMod 101) (ZMod 101) (ZMod 101) s) :=
    fun s => by cases s <;> exact inferInstanceAs (DecidableEq (ZMod 101))
  dsimp only
  apply (Uber.advantage_ofGeneric_le
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1 one_ne_zero one_ne_zero
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : ZMod 101) ≠ 0))
    [1, X 0] [1, X 0] [] (X 0 ^ 3) cubic_not_mem
    (degreeClosed_pairingSig 1 1 3) (degreeClosed_pairingSig 1 1 2)
    (table_degreeLE 3) (table_degreeLE 2) (by simp) (by decide)
    _ (n := fun | .g₁ => 0 | .g₂ => 0 | .gₜ => 1) ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · intro s
    cases s <;>
      exact ⟨by decide, fun _ => ⟨(by left; intro h; cases h), fun _ => trivial⟩⟩

end GroupModel
