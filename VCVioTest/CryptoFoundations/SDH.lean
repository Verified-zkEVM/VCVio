/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.SDH
public import Mathlib.Algebra.Field.ZMod

/-!
# Strong Diffie–Hellman experiments against unbounded adversaries

The reference string `SDH.srs` publishes `τ • g₁`. An adversary without resource bounds tries
every scalar `s` against `s • g₁` and recovers the trapdoor whenever `g₁ ≠ 0`. With the
trapdoor in hand it wins the `t`-SDH experiment with probability one, and also the ARSDH
experiment once the field has room for an output set that avoids the trapdoor. A bound on the
success of every adversary below one is therefore false for both experiments: a meaningful
assumption must restrict the adversary class.

The adversaries receive powers through degree `D + 1`, so that `τ • g₁` is part of the first
source group's reference string for every `D`. Over `ZMod 5`, the search recovers a concrete
trapdoor by evaluation.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace SDH

variable {F G₁ G₂ : Type} [Field F] [Fintype F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁] [AddCommGroup G₂] [Module F G₂]

/-- Exhaustive search for the trapdoor: the sum of the scalars `s` with `s • g₁ = P 1`. On a
reference string with `g₁ ≠ 0`, the trapdoor is the only such scalar. -/
def searchTrapdoor (g₁ : G₁) {D : ℕ} (P : Fin (D + 2) → G₁) : F :=
  ∑ s ∈ Finset.univ.filter (fun s : F => s • g₁ = P 1), s

/-- The exhaustive search recovers the trapdoor from a reference string with `g₁ ≠ 0`. -/
theorem searchTrapdoor_srs (g₁ : G₁) (hg₁ : g₁ ≠ 0) (g₂ : G₂) (τ : F) (D : ℕ) :
    searchTrapdoor g₁ (srs g₁ g₂ τ (D + 1)).1 = τ := by
  have h : Finset.univ.filter (fun s : F => s • g₁ = (srs g₁ g₂ τ (D + 1)).1 1) = {τ} := by
    ext s
    rw [Finset.mem_filter, Finset.mem_singleton, srs_fst]
    simp only [Fin.val_one, pow_one, smul_left_inj hg₁, Finset.mem_univ, true_and]
  rw [searchTrapdoor, h, Finset.sum_singleton]

/-- Over `ZMod 5` with `g₁ = 1`, the search recovers the trapdoor `3`. -/
theorem searchTrapdoor_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    searchTrapdoor (F := ZMod 5) (1 : ZMod 5) (srs (1 : ZMod 5) (1 : ZMod 5) (3 : ZMod 5) 1).1 =
      3 := by
  decide

end SDH

namespace TSDH

variable {F G₁ G₂ : Type} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

/-- Recovers the trapdoor `τ` by exhaustive search and returns the offset `1 - τ` with `g₁`,
which equals `(τ + (1 - τ))⁻¹ • g₁`. -/
def searchAdversary [DecidableEq G₁] (g₁ : G₁) (D : ℕ) : Adversary F G₁ G₂ (D + 1) :=
  fun P _ => pure (1 - SDH.searchTrapdoor g₁ P, g₁)

/-- The exhaustive-search adversary wins the `t`-SDH experiment with probability one. -/
theorem experiment_searchAdversary [DecidableEq G₁] (g₁ : G₁) (hg₁ : g₁ ≠ 0) (g₂ : G₂)
    (D : ℕ) :
    Pr{let b ← experiment g₁ g₂ (searchAdversary (F := F) (G₂ := G₂) g₁ D)}[b = true] = 1 := by
  apply prEvent_eq_one_of_forall_mem_support
  simp only [experiment, searchAdversary, SDH.searchTrapdoor_srs g₁ hg₁]
  simp

/-- No bound below one holds for the `t`-SDH success of every adversary when `g₁ ≠ 0`. -/
theorem not_forall_experiment_le (g₁ : G₁) (hg₁ : g₁ ≠ 0) (g₂ : G₂) (D : ℕ) {ε : ℝ≥0∞}
    (hε : ε < 1) :
    ¬ ∀ A : Adversary F G₁ G₂ (D + 1), Pr{let b ← experiment g₁ g₂ A}[b = true] ≤ ε := by
  classical
  intro h
  have hA := h (searchAdversary g₁ D)
  rw [experiment_searchAdversary g₁ hg₁ g₂ D] at hA
  exact (not_le_of_gt hε) hA

/-- Over `ZMod 5`, the exhaustive-search adversary wins the degree-two `t`-SDH experiment with
probability one. -/
theorem experiment_searchAdversary_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    Pr{let b ← (experiment (1 : ZMod 5) (1 : ZMod 5)
      (searchAdversary (F := ZMod 5) (G₂ := ZMod 5) (1 : ZMod 5) 1))}[b = true] = 1 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact experiment_searchAdversary _ one_ne_zero _ _

end TSDH

namespace ARSDH

/-- A set of `D + 2` scalars other than `τ`, chosen classically; arbitrary when the field has
too few elements. -/
noncomputable def avoidingSet {F : Type} [Fintype F] [DecidableEq F] (D : ℕ) (τ : F) :
    Finset F :=
  Classical.epsilon fun S : Finset F => S ⊆ Finset.univ.erase τ ∧ S.card = D + 2

/-- With at least `D + 3` scalars, `avoidingSet D τ` has `D + 2` elements and omits `τ`. -/
theorem avoidingSet_spec {F : Type} [Fintype F] [DecidableEq F] {D : ℕ}
    (hF : D + 3 ≤ Fintype.card F) (τ : F) :
    (avoidingSet D τ).card = D + 2 ∧ τ ∉ avoidingSet D τ := by
  have h : ∃ S : Finset F, S ⊆ Finset.univ.erase τ ∧ S.card = D + 2 := by
    apply Finset.exists_subset_card_eq
    rw [Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ]
    omega
  have hs := Classical.epsilon_spec h
  exact ⟨hs.2, fun hτ => (Finset.mem_erase.mp (hs.1 hτ)).1 rfl⟩

variable {F G₁ G₂ : Type} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

/-- Recovers the trapdoor `τ` by exhaustive search, chooses `D + 2` scalars `S` other than `τ`,
and returns `g₁` with its quotient by `∏ s ∈ S, (τ - s)`. -/
noncomputable def searchAdversary [DecidableEq G₁] (g₁ : G₁) (D : ℕ) :
    Adversary F G₁ G₂ (D + 1) :=
  fun P _ =>
    let τ := SDH.searchTrapdoor g₁ P
    let S := avoidingSet D τ
    pure (S, g₁, (∏ s ∈ S, (τ - s))⁻¹ • g₁)

/-- With at least `D + 3` scalars, the exhaustive-search adversary wins the ARSDH experiment
with probability one. -/
theorem experiment_searchAdversary [DecidableEq G₁] (g₁ : G₁) (hg₁ : g₁ ≠ 0) (g₂ : G₂)
    {D : ℕ} (hF : D + 3 ≤ Fintype.card F) :
    Pr{let b ← experiment g₁ g₂ (searchAdversary (F := F) (G₂ := G₂) g₁ D)}[b = true] = 1 := by
  apply prEvent_eq_one_of_forall_mem_support
  simp only [experiment, searchAdversary, SDH.searchTrapdoor_srs g₁ hg₁]
  intro b hb
  simp only [pure_bind, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop] at hb
  obtain ⟨τ, -, rfl⟩ := hb
  obtain ⟨hcard, hτ⟩ := avoidingSet_spec hF τ
  have hZ : ∏ s ∈ avoidingSet D τ, (τ - s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr fun h => hτ (h ▸ hs)
  simp [Polynomial.eval_prod, hcard, hZ, hg₁]

/-- No bound below one holds for the ARSDH success of every adversary when `g₁ ≠ 0` and the
field has at least `D + 3` elements. -/
theorem not_forall_experiment_le (g₁ : G₁) (hg₁ : g₁ ≠ 0) (g₂ : G₂) {D : ℕ}
    (hF : D + 3 ≤ Fintype.card F) {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ ∀ A : Adversary F G₁ G₂ (D + 1), Pr{let b ← experiment g₁ g₂ A}[b = true] ≤ ε := by
  classical
  intro h
  have hA := h (searchAdversary g₁ D)
  rw [experiment_searchAdversary g₁ hg₁ g₂ hF] at hA
  exact (not_le_of_gt hε) hA

/-- Over `ZMod 5`, the exhaustive-search adversary wins the degree-two ARSDH experiment with
probability one. -/
theorem experiment_searchAdversary_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    Pr{let b ← (experiment (1 : ZMod 5) (1 : ZMod 5)
      (searchAdversary (F := ZMod 5) (G₂ := ZMod 5) (1 : ZMod 5) 1))}[b = true] = 1 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact experiment_searchAdversary _ one_ne_zero _ (by simp [ZMod.card])

end ARSDH
