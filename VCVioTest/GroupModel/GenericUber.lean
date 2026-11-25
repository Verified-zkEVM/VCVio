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

private theorem table_degreeLE {F : Type} [Field F] (d : ℕ) :
    DegreeLE (fun | .g₁ => 1 | .g₂ => 1 | .gₜ => d)
      (uberTable [1, X 0] [1, X 0] ([] : List (MvPolynomial (Fin 1) F))) := by
  intro s p hp
  cases s with
  | g₁ | g₂ =>
    have hp : p = 1 ∨ p = X 0 := by simpa [uberTable] using hp
    rcases hp with rfl | rfl <;> simp
  | gₜ => exact False.elim (List.not_mem_nil hp)

private theorem cubic_not_mem {F : Type} [Field F] :
    (X (0 : Fin 1) ^ 3 : MvPolynomial (Fin 1) F) ∉
      accessibleSpan pairingSig (uberTable [1, X 0] [1, X 0] []) .gₜ :=
  not_mem_accessibleSpan_of_lt_totalDegree (degreeClosed_pairingSig 1 1 2) (table_degreeLE 2)
    (by simp [totalDegree_X_pow])

/-- One pairing and one equality query give computational uber success at most `11/101`.
The adversary compares the pairing of the two `X` entries with the zero default,
returning that default handle when the comparison succeeds. -/
theorem uber_computational_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    let A : OracleComp (genSpec (ZMod 101) pairingSig) Handle := do
      let t : Handle ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 1 1))
      let b : Bool ← (genSpec (ZMod 101) pairingSig).query (.inl (.eq .gₜ t (t + 1)))
      pure (if b then t + 1 else t)
    Pr{let b ← (Uber.computationalExperiment (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1
      [1, X (0 : Fin 1)] [1, X 0] [] (X 0 ^ 3)
      (Uber.ComputationalAdversary.ofGeneric (LinearMap.mul (ZMod 101) (ZMod 101)) A))}[
        b = true] ≤ (11 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  dsimp only
  apply (Uber.computationalExperiment_ofGeneric_le
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1
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
    let A : OracleComp (genSpec (ZMod 101) pairingSig) Bool := do
      let t : Handle ← (genSpec (ZMod 101) pairingSig).query (.inl (.bil () 1 1))
      (genSpec (ZMod 101) pairingSig).query (.inl (.eq .gₜ t 0))
    Uber.advantage (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1
      [1, X (0 : Fin 1)] [1, X 0] [] (X 0 ^ 3)
      (Uber.DecisionalAdversary.ofGeneric (LinearMap.mul (ZMod 101) (ZMod 101)) A) ≤
        (27 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  dsimp only
  apply (Uber.advantage_ofGeneric_le
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : ZMod 101) ≠ 0))
    [1, X 0] [1, X 0] [] (X 0 ^ 3) cubic_not_mem
    (degreeClosed_pairingSig 1 1 3) (degreeClosed_pairingSig 1 1 2)
    (table_degreeLE 3) (table_degreeLE 2) (by simp) (by decide)
    _ (n := fun | .g₁ => 0 | .g₂ => 0 | .gₜ => 1) ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · intro s
    cases s <;>
      exact ⟨by decide, fun _ => ⟨(by left; intro h; cases h), fun _ => trivial⟩⟩

/-- One pairing of the first `P` entry with the second `R` entry. Its handle is the first one after
the entries of `Q`. -/
def productAdversary : OracleComp (genSpec (ZMod 5) pairingSig) Handle :=
  (genSpec (ZMod 5) pairingSig).query (.inl (.bil () 0 1))

/-- The exact success of `productAdversary` on a target outside the accessible span: it returns
`x²`, so it recovers `x⁴` exactly when `x² = x⁴`, at `0`, `1` and `4`. Swapping the two source
lists, ignoring `Q` or rejecting every answer changes this value. -/
theorem uber_computational_zmod_five_exact :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    Pr{let b ← (Uber.computationalExperiment (LinearMap.mul (ZMod 5) (ZMod 5)) 1 1
      [1, X (0 : Fin 1)] [1, X 0 ^ 2] [X 0] (X 0 ^ 4)
      (Uber.ComputationalAdversary.ofGeneric (LinearMap.mul (ZMod 5) (ZMod 5))
        productAdversary))}[b = true] = (3 / 5 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc : (Finset.univ.filter fun x : Fin 1 → ZMod 5 => x 0 ^ 2 = x 0 ^ 4).card = 3 := by
    decide
  have hrun (x : ZMod 5) :
      Uber.ComputationalAdversary.ofGeneric (LinearMap.mul (ZMod 5) (ZMod 5)) productAdversary
        [1, x] [1, x ^ 2] [x] = pure (x ^ 2 : ZMod 5) := by
    change (pure ((pairingReal (LinearMap.mul (ZMod 5) (ZMod 5))).bil ()
      (1 : ZMod 5) (x ^ 2 : ZMod 5)) : ProbComp (ZMod 5)) = _
    erw [pairingReal_bil_apply]
    simp
  simp only [Uber.computationalExperiment, List.map_cons, List.map_nil, MvPolynomial.eval_X,
    map_one, map_pow, LinearMap.mul_apply', smul_eq_mul, mul_one, hrun, pure_bind, prEvent_norm,
    decide_eq_true_eq]
  rw [SampleableType.prEvent_uniformSample, hc]
  simp [ZMod.card]

/-- A target inside the accessible span is recovered with probability one: `productAdversary`
returns `x²`, so the bound needs a target outside the span. -/
theorem uber_computational_zmod_five_inside :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    (X (0 : Fin 1) ^ 2 : MvPolynomial (Fin 1) (ZMod 5)) ∈
        accessibleSpan pairingSig (uberTable [1, X 0] [1, X 0 ^ 2] [X 0]) .gₜ ∧
      Pr{let b ← (Uber.computationalExperiment (LinearMap.mul (ZMod 5) (ZMod 5)) 1 1
        [1, X (0 : Fin 1)] [1, X 0 ^ 2] [X 0] (X 0 ^ 2)
        (Uber.ComputationalAdversary.ofGeneric (LinearMap.mul (ZMod 5) (ZMod 5))
          productAdversary))}[b = true] = 1 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  constructor
  · rw [accessibleSpan_pairingSig]
    exact Submodule.subset_span (Or.inr ⟨1, by simp [uberTable], X 0 ^ 2, by simp [uberTable],
      by simp⟩)
  · have hrun (x : ZMod 5) :
        Uber.ComputationalAdversary.ofGeneric (LinearMap.mul (ZMod 5) (ZMod 5)) productAdversary
          [1, x] [1, x ^ 2] [x] = pure (x ^ 2 : ZMod 5) := by
      change (pure ((pairingReal (LinearMap.mul (ZMod 5) (ZMod 5))).bil ()
        (1 : ZMod 5) (x ^ 2 : ZMod 5)) : ProbComp (ZMod 5)) = _
      erw [pairingReal_bil_apply]
      simp
    simp only [Uber.computationalExperiment, List.map_cons, List.map_nil, MvPolynomial.eval_X,
      map_one, map_pow, LinearMap.mul_apply', smul_eq_mul, mul_one, hrun, pure_bind, prEvent_norm,
      decide_eq_true_eq]
    simp

/-- The bound is attained: with no supplied elements and no queries, guessing the zero element
recovers the target `x` exactly when `x = 0`, and the theorem gives `1/5`. -/
theorem uber_computational_zmod_five_attained :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    Pr{let b ← (Uber.computationalExperiment (LinearMap.mul (ZMod 5) (ZMod 5)) 1 1
      [] [] [] (X (0 : Fin 1))
      (Uber.ComputationalAdversary.ofGeneric (LinearMap.mul (ZMod 5) (ZMod 5))
        (pure 0)))}[b = true] = (1 / 5 : ℝ≥0∞) ∧
    Pr{let b ← (Uber.computationalExperiment (LinearMap.mul (ZMod 5) (ZMod 5)) 1 1
      [] [] [] (X (0 : Fin 1))
      (Uber.ComputationalAdversary.ofGeneric (LinearMap.mul (ZMod 5) (ZMod 5))
        (pure 0)))}[b = true] ≤ ((1 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod 5) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc : (Finset.univ.filter fun x : Fin 1 → ZMod 5 => 0 = x 0).card = 1 := by decide
  have hrun : Uber.ComputationalAdversary.ofGeneric (LinearMap.mul (ZMod 5) (ZMod 5))
      (pure 0) [] [] [] = pure (0 : ZMod 5) := rfl
  constructor
  · simp only [Uber.computationalExperiment, List.map_nil, MvPolynomial.eval_X,
      LinearMap.mul_apply', smul_eq_mul, mul_one, hrun, pure_bind, prEvent_norm,
      decide_eq_true_eq]
    rw [SampleableType.prEvent_uniformSample, hc]
    simp [ZMod.card]
  · have hd : DegreeLE (fun _ : PSort => 0)
        (uberTable ([] : List (MvPolynomial (Fin 1) (ZMod 5))) [] []) := by
      intro s p hp
      cases s <;> exact False.elim (List.not_mem_nil hp)
    have hD : pairingSig.DegreeClosed (fun _ : PSort => 0) :=
      (pairingSig_degreeClosed_iff _).mpr (by simp)
    refine (Uber.computationalExperiment_ofGeneric_le (LinearMap.mul (ZMod 5) (ZMod 5)) 1 1
      (by simp) [] [] [] (X 0)
      (not_mem_accessibleSpan_of_lt_totalDegree hD hd (by simp)) hD hd (pure 0)
      (n := fun _ => 0) (fun s => by simp) 1 (by simp)).trans (by simp)

-- The same target is outside the accessible span at `pairingSig` and inside it at
-- `pairingIsoSig`, where `ψ` carries the second source list into the first source group.
example {F : Type} [Field F] :
    (X (0 : Fin 1) ^ 2 : MvPolynomial (Fin 1) F) ∉
        accessibleSpan pairingSig (uberTable [1] [1, X 0] []) .gₜ ∧
      (X (0 : Fin 1) ^ 2 : MvPolynomial (Fin 1) F) ∈
        accessibleSpan pairingIsoSig (uberTable [1] [1, X 0] []) .gₜ := by
  have hd : DegreeLE (fun | .g₁ => 0 | .g₂ => 1 | .gₜ => 1)
      (uberTable ([1] : List (MvPolynomial (Fin 1) F)) [1, X 0] []) := by
    intro s p hp
    cases s with
    | g₁ => simp [uberTable] at hp; simp [hp]
    | g₂ =>
      have hp : p = 1 ∨ p = X 0 := by simpa [uberTable] using hp
      rcases hp with rfl | rfl <;> simp
    | gₜ => exact False.elim (List.not_mem_nil hp)
  refine ⟨not_mem_accessibleSpan_of_lt_totalDegree (degreeClosed_pairingSig 0 1 1) hd
    (by simp [totalDegree_X_pow]), ?_⟩
  have hc := accessibleSpan_spanClosed (σ := pairingIsoSig)
    (uberTable ([1] : List (MvPolynomial (Fin 1) F)) [1, X 0] [])
  have hX : (X 0 : MvPolynomial (Fin 1) F) ∈ accessibleSpan pairingIsoSig
      (uberTable ([1] : List (MvPolynomial (Fin 1) F)) [1, X 0] []) .g₂ :=
    mem_accessibleSpan _ _ _ (by simp [uberTable])
  rw [pow_two]
  exact hc.2 () _ _ (hc.1 () hX) hX

end GroupModel
