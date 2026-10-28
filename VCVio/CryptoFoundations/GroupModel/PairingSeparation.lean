/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.PairingVariants
public import VCVio.CryptoFoundations.GroupModel.GenericDDH
import Mathlib.Algebra.Module.Torsion.Free

/-! # Pairing signatures separate generic DDH problems

A lower bound is a statement about a signature. These are P1 and P3 of Section 7
of the group-models design note: a symmetric pairing, or a source map followed by an
asymmetric pairing, distinguishes a DH tuple with advantage exactly `1 - 1 / |F|`.
The same four source elements at `groupSig` satisfy `ddhAdvantage_ofGeneric_le`.

The Type 1/2/3 classification follows Galbraith, Paterson and Smart, *Pairings for
cryptographers* (2008, ePrint 2006/165). The symmetric DDH test illustrates the
decisional/computational gap of Joux and Nguyen, *Separating Decision Diffie–Hellman
from Computational Diffie–Hellman in Cryptographic Groups* (2003).
-/

public section

open OracleComp OracleSpec DiffieHellman
open scoped ENNReal

namespace GroupModel

variable {F G G₁ G₂ Gₜ : Type}

/-- Interpret a Type 1 adversary on the four source handles of a DDH challenge. -/
@[expose] def symmDDH.ofGeneric [Field F] [AddCommGroup G] [Module F G]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (SFam G Gₜ s)]
    (e : G →ₗ[F] G →ₗ[F] Gₜ) (A : OracleComp (genSpec F symmPairingSig) Bool) :
    DiffieHellman.DDHAdversary F G :=
  fun g X Y T => Prod.fst <$> runGen (symmPairingReal e) (fun _ => id) A
    (fun | false => [g, X, Y, T] | true => [])

/-- Pair the two challenge factors and compare with the generator paired with the target. -/
@[expose] def symmDDHAttack (F : Type) : OracleComp (genSpec F symmPairingSig) Bool := do
  let xy ← (genSpec F symmPairingSig).query (.inl (.bil () 1 2))
  let gt ← (genSpec F symmPairingSig).query (.inl (.bil () 0 3))
  (genSpec F symmPairingSig).query (.inl (.eq true xy gt))

/-- Interpret a Type 2 adversary on four second-source handles and empty other tables. -/
@[expose] def isoDDH.ofGeneric [Field F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (A : OracleComp (genSpec F pairingIsoSig) Bool) : DiffieHellman.DDHAdversary F G₂ :=
  fun g X Y T => Prod.fst <$> runGen (pairingIsoReal ψ e) (fun _ => id) A
    (fun | .g₁ => [] | .g₂ => [g, X, Y, T] | .gₜ => [])

/-- Map the first challenge factor and generator to the first source, then compare pairings. -/
@[expose] def isoDDHAttack (F : Type) : OracleComp (genSpec F pairingIsoSig) Bool := do
  let x ← (genSpec F pairingIsoSig).query (.inl (.lin () 1))
  let g ← (genSpec F pairingIsoSig).query (.inl (.lin () 0))
  let xy ← (genSpec F pairingIsoSig).query (.inl (.bil () x 2))
  let gt ← (genSpec F pairingIsoSig).query (.inl (.bil () g 3))
  (genSpec F pairingIsoSig).query (.inl (.eq .gₜ xy gt))

private theorem symmDDHAttack_run [DecidableEq Gₜ] [Field F] [AddCommGroup G] [Module F G]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (SFam G Gₜ s)]
    (e : G →ₗ[F] G →ₗ[F] Gₜ) (g X Y T : G) :
    symmDDH.ofGeneric e (symmDDHAttack F) g X Y T = pure (decide (e X Y = e g T)) := by
  let t₀ : Tbl (SFam G Gₜ) := fun | false => [g, X, Y, T] | true => []
  let t₁ := append t₀ true (e X Y)
  let t₂ := append t₁ true (e g T)
  unfold symmDDH.ofGeneric symmDDHAttack runGen run
  erw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, QueryImpl.add_apply_inl]
  change (Prod.fst <$> ((pure (0, t₁) : ProbComp _) >>= _)) = _
  erw [pure_bind]
  erw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, QueryImpl.add_apply_inl]
  change (Prod.fst <$> ((pure (1, t₂) : ProbComp _) >>= _)) = _
  erw [pure_bind]
  erw [simulateQ_spec_query, QueryImpl.add_apply_inl, impl, StateT.run_bind,
    StateT.run_get, pure_bind, StateT.run_pure]
  erw [map_pure]
  congr 1
  rw [decide_eq_decide]
  rfl

private theorem isoDDHAttack_run [DecidableEq Gₜ] [Field F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g X Y T : G₂) :
    isoDDH.ofGeneric ψ e (isoDDHAttack F) g X Y T =
      pure (decide (e (ψ X) Y = e (ψ g) T)) := by
  let t₀ : Tbl (PFam G₁ G₂ Gₜ) := fun | .g₁ => [] | .g₂ => [g, X, Y, T] | .gₜ => []
  let t₁ := append t₀ .g₁ (ψ X)
  let t₂ := append t₁ .g₁ (ψ g)
  let t₃ := append t₂ .gₜ (e (ψ X) Y)
  let t₄ := append t₃ .gₜ (e (ψ g) T)
  unfold isoDDH.ofGeneric isoDDHAttack runGen run
  erw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, QueryImpl.add_apply_inl]
  change (Prod.fst <$> ((pure (0, t₁) : ProbComp _) >>= _)) = _
  erw [pure_bind]
  erw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, QueryImpl.add_apply_inl]
  change (Prod.fst <$> ((pure (1, t₂) : ProbComp _) >>= _)) = _
  erw [pure_bind]
  erw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, QueryImpl.add_apply_inl]
  change (Prod.fst <$> ((pure (0, t₃) : ProbComp _) >>= _)) = _
  erw [pure_bind]
  erw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, QueryImpl.add_apply_inl]
  change (Prod.fst <$> ((pure (1, t₄) : ProbComp _) >>= _)) = _
  erw [pure_bind]
  erw [simulateQ_spec_query, QueryImpl.add_apply_inl, impl, StateT.run_bind,
    StateT.run_get, pure_bind, StateT.run_pure]
  erw [map_pure]
  congr 1
  rw [decide_eq_decide]
  rfl

private theorem ddhAdvantage_of_scalar_test [Field F] [Fintype F] [SampleableType F]
    [DecidableEq F] [AddCommGroup G] [Module F G]
    (g : G) (A : DiffieHellman.DDHAdversary F G)
    (hA : ∀ a b c : F, A g (a • g) (b • g) (c • g) = pure (decide (c = a * b))) :
    ddhAdvantage g A = 1 - 1 / (Fintype.card F : ℝ≥0∞) := by
  have hr : Pr{let z ← ddhRealExperiment g A}[z = true] = 1 := by
    simp [ddhRealExperiment, hA, prEvent_norm]
  have hu : Pr{let z ← ddhRandomExperiment g A}[z = true] =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
    simp only [ddhRandomExperiment]
    refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun a => ?_
    refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun b => ?_
    simp only [hA, prEvent_norm, decide_eq_true_eq]
    exact SampleableType.prEvent_uniformSample_eq_singleton (a * b)
  have hu_le : (Fintype.card F : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [← hu]
    exact prEvent_le_one _
  rw [ddhAdvantage, MeasureTheory.Measure.boolDist,
    ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton, hr, hu]
  simp only [ENNReal.absDiff, tsub_eq_zero_of_le hu_le, add_zero, one_div]

/-- P1: two symmetric pairing queries and one equality test have exact DDH advantage
`1 - 1 / |F|`. Nonzero self-pairing makes the scalar equality test faithful. -/
theorem ddhAdvantage_symmDDHAttack_eq [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G] [Module F G] [AddCommGroup Gₜ] [Module F Gₜ]
    [∀ s, DecidableEq (SFam G Gₜ s)]
    (e : G →ₗ[F] G →ₗ[F] Gₜ) (g : G) (he : e g g ≠ 0) :
    ddhAdvantage g (symmDDH.ofGeneric e (symmDDHAttack F)) =
      1 - 1 / (Fintype.card F : ℝ≥0∞) := by
  classical
  apply ddhAdvantage_of_scalar_test
  intro a b c
  rw [symmDDHAttack_run]
  congr 1
  rw [decide_eq_decide]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [mul_comm b a, (smul_left_injective F he).eq_iff]
  exact eq_comm

/-- P1 gives advantage at least `1 - 1 / |F|` for a cyclic source with nonzero self-pairing.
At the one-group signature the same four inputs instead obey `ddhAdvantage_ofGeneric_le`. -/
theorem ddhAdvantage_symmDDHAttack_ge [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G] [Module F G] [AddCommGroup Gₜ] [Module F Gₜ]
    [∀ s, DecidableEq (SFam G Gₜ s)]
    (e : G →ₗ[F] G →ₗ[F] Gₜ) (g : G) (hg : Function.Bijective (· • g : F → G))
    (he : e g g ≠ 0) :
    1 - 1 / (Fintype.card F : ℝ≥0∞) ≤
      ddhAdvantage g (symmDDH.ofGeneric e (symmDDHAttack F)) := by
  obtain ⟨_, _⟩ := hg
  exact (ddhAdvantage_symmDDHAttack_eq e g he).ge

/-- P3: two source-map queries, two pairing queries and one equality test have exact
DDH advantage `1 - 1 / |F|` in the second source group. -/
theorem ddhAdvantage_isoDDHAttack_eq [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂)
    (he : e (ψ g₂) g₂ ≠ 0) :
    ddhAdvantage g₂ (isoDDH.ofGeneric ψ e (isoDDHAttack F)) =
      1 - 1 / (Fintype.card F : ℝ≥0∞) := by
  classical
  apply ddhAdvantage_of_scalar_test
  intro a b c
  rw [isoDDHAttack_run]
  congr 1
  rw [decide_eq_decide]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [mul_comm b a, (smul_left_injective F he).eq_iff]
  exact eq_comm

/-- P3 gives advantage at least `1 - 1 / |F|` for a cyclic second source when its
source-map image has nonzero pairing with its generator. -/
theorem ddhAdvantage_isoDDHAttack_ge [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂)
    (hg₂ : Function.Bijective (· • g₂ : F → G₂)) (he : e (ψ g₂) g₂ ≠ 0) :
    1 - 1 / (Fintype.card F : ℝ≥0∞) ≤
      ddhAdvantage g₂ (isoDDH.ofGeneric ψ e (isoDDHAttack F)) := by
  obtain ⟨_, _⟩ := hg₂
  exact (ddhAdvantage_isoDDHAttack_eq ψ e g₂ he).ge

end GroupModel
