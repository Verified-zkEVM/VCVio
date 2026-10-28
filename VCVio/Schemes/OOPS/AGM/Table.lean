/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.OOPS.AGM.Execution
public import VCVio.Schemes.OOPS.AGM.Functional
import all VCVio.Schemes.OOPS.AGM.Execution
import all VCVio.Schemes.OOPS.AGM.Reductions

/-! # Finite-table interpretations of the named OOPS reductions

Both reductions execute their original lazy programs. Finite tables appear only in the
proof and share the same chronological adversary view and signing functional.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace OOPS.AGM

/-- The scalar polynomial hash determined by a table of base exponents. -/
@[expose] def scalarHash {F T : Type} [Semiring F] (degree : ℕ)
    (ρ : T × Fin (degree + 1) → F) (m : F × T) : F :=
  ((terms degree m).map fun p => p.2 * ρ p.1).sum

/-- The public adversary view with fixed scalar bases and a fixed signing secret. -/
@[expose] def fixedView {F T G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree)
    (ρ : T × Fin (degree + 1) → F) (κ : F) :=
  weightedFixedRun (fun i => ρ i • g₁) (fun m => κ • (scalarHash degree ρ m • g₁))
    (rawMain A (κ • g₂))

/-- The target weight minus the chronological signing functional. -/
@[expose] def verificationGap {F T : Type} [Ring F] [DecidableEq T]
    (degree : ℕ) (coeff : List F)
    (tr : List ((T × Fin (degree + 1)) ⊕ (F × T))) (mt : F × T)
    (i : T × Fin (degree + 1)) : F :=
  weight degree i mt - signingFunctional degree coeff tr i

/-- The good reduction's denominator is the table evaluation of the verification gap. -/
theorem scalarHash_sub_goodRepresentation_snd {F T : Type} [CommRing F] [DecidableEq T]
    (degree : ℕ) (S : Finset (T × Fin (degree + 1))) (ρ : S → F) (coeff : List F)
    (tr : List ((T × Fin (degree + 1)) ⊕ (F × T))) (mt : F × T) :
    scalarHash degree (extendTable S 0 ρ) mt -
      (goodRepresentation degree coeff tr (extendTable S 0 ρ)).2 =
        ∑ i : S, verificationGap degree coeff tr mt i.val * ρ i := by
  simp only [scalarHash, sum_terms_extendTable_eq, goodRepresentation_snd,
    verificationGap, sub_mul, Finset.sum_sub_distrib]

/-- A finite proof cover interprets the actual good reduction by its affine extraction quotient. -/
theorem goodReduction_table {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) (κ : F)
    (S : Finset (T × Fin (degree + 1)))
    (hS : WeightedInterfaceCovered S (terms degree) (fun out => out.value.data)
      (rawMain A (κ • g₂))) :
    OOPS.goodReduction A g₁ (κ • g₁) g₂ (κ • g₂) =ᵈ
      (do
        let ρ ← $ᵗ (S → F)
        let z ← fixedView A (extendTable S 0 ρ) κ
        let repr := goodRepresentation degree ((z.1.coefficients false).headD []) z.2
          (extendTable S 0 ρ)
        return repr.1 / (scalarHash degree (extendTable S 0 ρ) z.1.value.data - repr.2)) := by
  have h := (reductionRun_eq_table A (κ • g₂)
    (fun ρ : F => ρ • g₁) (fun ρ => ρ • (κ • g₁))
    (fun ρ => (ρ, (0 : F))) (fun ρ => ((0 : F), ρ)) [(1, 0)] S hS 0).map
      (fun z => (evaluate (OOPS.coefficients z.1) z.2.1).1 /
        (z.2.2 - (evaluate (OOPS.coefficients z.1) z.2.1).2))
  simpa only [OOPS.goodReduction, OOPS.coefficients, bind_pure_comp, map_bind, map_pure,
    Functor.map_map, fixedView, scalarHash, goodRepresentation, Function.comp_def,
    smul_eq_mul, smul_smul, mul_comm, List.singleton_append] using h

private theorem pair_tables {F ι : Type} [SampleableType F] [Fintype ι] [DecidableEq ι] :
    (do let a ← $ᵗ (ι → F); let b ← $ᵗ (ι → F); return fun i => (a i, b i)) =ᵈ
      ($ᵗ (ι → F × F) : ProbComp _) := by
  apply SampleableType.evalDistEq_uniformSample_pair_of_bijective
  constructor
  · intro ⟨a, b⟩ ⟨c, d⟩ h
    exact Prod.ext (funext fun i => congrArg Prod.fst (congrFun h i))
      (funext fun i => congrArg Prod.snd (congrFun h i))
  · intro ρ
    exact ⟨(fun i => (ρ i).1, fun i => (ρ i).2), rfl⟩

private theorem table_pair {F I : Type} [Zero F] [DecidableEq I]
    (S : Finset I) (a b : S → F) (i : I) :
    extendTable S (0, 0) (fun i => (a i, b i)) i =
      (extendTable S 0 a i, extendTable S 0 b i) := by
  simp only [GroupModel.LinearFunctional.extendTable]
  split <;> rfl

private theorem table_affine {F I : Type} [Ring F] [DecidableEq I]
    (S : Finset I) (a b : S → F) (α : F) (i : I) :
    extendTable S 0 (fun i => a i * α + b i) i =
      extendTable S 0 a i * α + extendTable S 0 b i := by
  simp only [GroupModel.LinearFunctional.extendTable]
  split <;> simp

private theorem terms_pair {F I : Type} [Semiring F] (ts : List (I × F)) (a b : I → F) :
    (ts.map fun p => p.2 • (a p.1, b p.1)).sum =
      ((ts.map fun p => p.2 * a p.1).sum, (ts.map fun p => p.2 * b p.1).sum) := by
  induction ts with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rfl

private theorem scalarHash_affine {F T : Type} [CommRing F] (degree : ℕ)
    (a b : T × Fin (degree + 1) → F) (α : F) (m : F × T) :
    scalarHash degree (fun i => a i * α + b i) m =
      scalarHash degree a m * α + scalarHash degree b m := by
  simp only [scalarHash, terms, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    mul_add, ← mul_assoc, Finset.sum_add_distrib, Finset.sum_mul]

/-- The actual masked reduction evaluates the verification-gap slope and offset on two
independent tables while presenting their affine combination to the adversary. -/
theorem badReduction_table {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) (α : F)
    (S : Finset (T × Fin (degree + 1)))
    (hS : ∀ κ : F, WeightedInterfaceCovered S (terms degree) (fun out => out.value.data)
      (rawMain A (κ • g₂))) :
    OOPS.badReduction A g₁ (α • g₁) g₂ (α • g₂) =ᵈ
      (do
        let κ ← $ᵗ F
        let a ← $ᵗ (S → F)
        let b ← $ᵗ (S → F)
        let z ← fixedView A (extendTable S 0 (fun i => a i * α + b i)) κ
        return (-∑ i : S, verificationGap degree ((z.1.coefficients false).headD [])
          z.2 z.1.value.data i.val * b i) /
          (∑ i : S, verificationGap degree ((z.1.coefficients false).headD [])
            z.2 z.1.value.data i.val * a i)) := by
  unfold OOPS.badReduction
  apply _root_.EvalDistEq.bind_right
  intro κ
  have h := (reductionRun_eq_table A (κ • g₂)
    (fun r : F × F => r.1 • (α • g₁) + r.2 • g₁)
    (fun r => κ • (r.1 • (α • g₁) + r.2 • g₁))
    (fun _ => ((0 : F), (0 : F))) id [(0, 0)] S (hS κ) (0, 0)).map
      (fun z => ((evaluate (OOPS.coefficients z.1) z.2.1).2 - z.2.2.2) /
        (z.2.2.1 - (evaluate (OOPS.coefficients z.1) z.2.1).1))
  simp only [bind_pure_comp]
  refine _root_.EvalDistEq.trans (m'' := ProbComp) h ?_
  simp only [map_bind, map_pure]
  refine ((pair_tables (F := F) (ι := S)).symm.bind_left _).trans ?_
  simp only [bind_assoc, pure_bind, table_pair, terms_pair,
    OOPS.coefficients, id_eq, List.singleton_append]
  apply _root_.EvalDistEq.bind_right
  intro a
  apply _root_.EvalDistEq.bind_right
  intro b
  have hv : weightedFixedRun
      (fun i => extendTable S 0 a i • (α • g₁) + extendTable S 0 b i • g₁)
      (fun m => κ • (scalarHash degree (extendTable S 0 a) m • (α • g₁) +
        scalarHash degree (extendTable S 0 b) m • g₁)) (rawMain A (κ • g₂)) =
      fixedView A (extendTable S 0 (fun i => a i * α + b i)) κ := by
    have hf : extendTable S 0 (fun i => a i * α + b i) =
        (fun i => extendTable S 0 a i * α + extendTable S 0 b i) :=
      funext (table_affine S a b α)
    simp only [fixedView, hf, scalarHash_affine, add_smul, mul_smul]
  change (do
    let z ← weightedFixedRun
      (fun i => extendTable S 0 a i • (α • g₁) + extendTable S 0 b i • g₁)
      (fun m => κ • (scalarHash degree (extendTable S 0 a) m • (α • g₁) +
        scalarHash degree (extendTable S 0 b) m • g₁)) (rawMain A (κ • g₂))
    return ((maskRepresentation degree ((z.1.coefficients false).headD []) z.2
        (extendTable S 0 a) (extendTable S 0 b)).2 -
      scalarHash degree (extendTable S 0 b) z.1.value.data) /
      (scalarHash degree (extendTable S 0 a) z.1.value.data -
        (maskRepresentation degree ((z.1.coefficients false).headD []) z.2
          (extendTable S 0 a) (extendTable S 0 b)).1)) =ᵈ _
  rw [hv]
  simp only [map_eq_bind_pure_comp]
  apply _root_.EvalDistEq.bind_right
  intro z
  rw [maskRepresentation_eq]
  simp only [scalarHash, sum_terms_extendTable_eq, verificationGap,
    sub_mul, Finset.sum_sub_distrib, neg_sub]
  exact _root_.EvalDistEq.refl _

end OOPS.AGM
