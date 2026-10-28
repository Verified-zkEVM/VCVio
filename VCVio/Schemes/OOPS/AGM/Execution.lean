/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.OOPS.AGM.Reductions
public import VCVio.Schemes.OOPS.Admissibility
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedTrace
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Interaction
import all VCVio.Schemes.OOPS.AGM.Reductions

/-! # Algebraic soundness of chronological OOPS executions

The public transcript records only replies received by the adversary. Fixed base tables
interpret the lazy reductions and their explanation vectors in this same chronological order.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace OOPS.AGM

/-- The explained adversary computation with its protocol queries forwarded to the signature
algorithm's ambient and signing interfaces. -/
@[expose] def rawMain {F T G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) (pk : G₂) :=
  simulateQ (fun q => oracle q.value) (A.main (initialInput g₁ g₂ pk))

private def received {F T G₁ G₂ : Type} {degree : ℕ}
    (initial : Groups (SourceGroup G₁ G₂))
    (hash : T × Fin (degree + 1) → G₁) (sign : F × T → G₁)
    (tr : List ((T × Fin (degree + 1)) ⊕ (F × T))) :
    Groups (SourceGroup G₁ G₂) :=
  sourceInputs (initial false ++ tr.map (Sum.elim hash sign))
    (initial true)

private def fixedPlainOracle {F T G₁ G₂ : Type} {degree : ℕ}
    (hash : T × Fin (degree + 1) → G₁) (sign : F × T → G₁) :
    QueryImpl (plainSpec (SourceGroup G₁ G₂) (Query F T degree) Reply) ProbComp := by
  intro ⟨q, _⟩
  rcases q with ((n | m) | m)
  · exact (fun r => ⟨r, sourceInputs [] []⟩) <$> (unifSpec.query n : ProbComp _)
  · exact pure ⟨(), sourceInputs [hash m] []⟩
  · exact pure ⟨(), sourceInputs [sign m] []⟩

private theorem received_empty {F T G₁ G₂ : Type} {degree : ℕ}
    (initial : Groups (SourceGroup G₁ G₂))
    (hash : T × Fin (degree + 1) → G₁) (sign : F × T → G₁) :
    received initial hash sign [] = initial := by
  funext s
  cases s <;> simp [received, sourceInputs]

private theorem weightedFixedRun_groups {F T G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) (pk : G₂)
    (hash : T × Fin (degree + 1) → G₁) (sign : F × T → G₁) :
    (fun z => (z.1, received (initialInput g₁ g₂ pk).groups hash sign z.2)) <$>
      weightedFixedRun hash sign (rawMain A pk) =
      A.toAdversary.run (fixedPlainOracle hash sign) (initialInput g₁ g₂ pk) := by
  let input := initialInput g₁ g₂ pk
  let impl₁ := (weightedFixedOracle hash sign) ∘ₛ (fun q => oracle q.value
    : QueryImpl (explainedSpec F (SourceGroup G₁ G₂) (Query F T degree) Reply)
      (OracleComp (rawSpec F T G₁ degree)))
  let impl₂ : QueryImpl (explainedSpec F (SourceGroup G₁ G₂) (Query F T degree) Reply)
      (StateT (Groups (SourceGroup G₁ G₂)) ProbComp) := fun q => StateT.mk fun basis => do
    let reply ← fixedPlainOracle hash sign q.value
    return (reply, extend basis reply.groups)
  have hstep : ∀ q tr, Prod.map id (received input.groups hash sign) <$>
      (impl₁ q).run tr = (impl₂ q).run (received input.groups hash sign tr) := by
    intro ⟨⟨q, groups⟩, coeff⟩ tr
    rcases q with ((n | m) | m) <;>
      simp only [impl₁, impl₂, QueryImpl.apply_compose, oracle, fixedPlainOracle,
        simulateQ_map, simulateQ_spec_query, StateT.run_map, StateT.run_mk,
        bind_pure_comp, Functor.map_map]
    · change (Prod.map id (received input.groups hash sign) <$>
        ((fun r => ((⟨r, sourceInputs [] []⟩ : Message _ (SourceGroup G₁ G₂)), tr)) <$>
          (unifSpec.query n : ProbComp _))) = _
      rw [Functor.map_map]
      change (fun r : Fin (n + 1) =>
          ((⟨r, sourceInputs [] []⟩ : Message _ (SourceGroup G₁ G₂)),
            received input.groups hash sign tr)) <$> (unifSpec.query n : ProbComp _) =
        (fun r : Fin (n + 1) =>
          ((⟨r, sourceInputs [] []⟩ : Message _ (SourceGroup G₁ G₂)),
            extend (received input.groups hash sign tr) (sourceInputs [] []))) <$>
          (unifSpec.query n : ProbComp _)
      congr 1
      funext r
      apply Prod.ext
      · rfl
      · funext s
        cases s <;> simp [received, sourceInputs, extend]
    · simp only [weightedFixedOracle, StateT.run]
      simp only [map_pure, Prod.map_apply', id_eq]
      apply congrArg pure
      apply Prod.ext
      · rfl
      · funext s
        cases s <;> simp [received, sourceInputs, extend, List.append_assoc]
    · simp only [weightedFixedOracle, StateT.run]
      simp only [map_pure, Prod.map_apply', id_eq]
      apply congrArg pure
      apply Prod.ext
      · rfl
      · funext s
        cases s <;> simp [received, sourceInputs, extend, List.append_assoc]
  have h := map_run_simulateQ_eq_of_query_map_eq impl₁ impl₂
    (received input.groups hash sign) hstep (A.main input) []
  rw [received_empty] at h
  simpa only [impl₁, QueryImpl.simulateQ_compose, impl₂, Adversary.run,
    weightedFixedRun, rawMain, input, Prod.map_def, id_eq] using h

private theorem weightedFixedRun_valid {F T G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) (pk : G₂)
    (hash : T × Fin (degree + 1) → G₁) (sign : F × T → G₁)
    (z : Explained F (F × T) (SourceGroup G₁ G₂) ×
      List ((T × Fin (degree + 1)) ⊕ (F × T)))
    (hz : z ∈ support (weightedFixedRun hash sign (rawMain A pk))) :
    z.1.Valid (received (initialInput g₁ g₂ pk).groups hash sign z.2) := by
  apply A.toAdversary.run_valid (fixedPlainOracle hash sign) (initialInput g₁ g₂ pk)
    (z.1, received (initialInput g₁ g₂ pk).groups hash sign z.2)
  rw [← weightedFixedRun_groups]
  rw [support_map]
  exact ⟨z, hz, rfl⟩


/-- Algebraic validity gives the scalar affine representation on every supported fixed-table
run, with a single generator position before the chronological replies. -/
theorem fixedRun_good_sound {F T G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) (κ : F)
    (ρ : T × Fin (degree + 1) → F)
    (z : Explained F (F × T) (SourceGroup G₁ G₂) ×
      List ((T × Fin (degree + 1)) ⊕ (F × T)))
    (hz : z ∈ support (weightedFixedRun (fun i => ρ i • g₁)
      (fun m => κ • ((((terms degree m).map fun p => p.2 * ρ p.1).sum) • g₁))
      (rawMain A (κ • g₂)))) :
    let repr := evaluate ((z.1.coefficients false).headD []) ([(1, 0)] ++
      z.2.map (Sum.elim (fun i => (ρ i, (0 : F)))
        (fun m => (0, ((terms degree m).map fun p => p.2 * ρ p.1).sum))))
    (forgery z.1).2 = (repr.1 + repr.2 * κ) • g₁ := by
  let f : (F × F) →ₗ[F] G₁ :=
    (LinearMap.fst F F F).smulRight g₁ + (LinearMap.snd F F F).smulRight (κ • g₁)
  have hv := z.1.evaluate_headD
    (received (initialInput g₁ g₂ (κ • g₂)).groups
      (fun i => ρ i • g₁)
      (fun m => κ • ((((terms degree m).map fun p => p.2 * ρ p.1).sum) • g₁)) z.2)
    (by
      intro s
      cases s <;> exact weightedFixedRun_valid A (κ • g₂) _ _ z hz _) false
  let basis : List (F × F) := [(1, 0)] ++
    z.2.map (Sum.elim (fun i => (ρ i, 0))
      (fun m => (0, ((terms degree m).map fun p => p.2 * ρ p.1).sum)))
  have hb : (received (initialInput g₁ g₂ (κ • g₂)).groups
      (fun i => ρ i • g₁)
      (fun m => κ • ((((terms degree m).map fun p => p.2 * ρ p.1).sum) • g₁)) z.2) false =
      basis.map f := by
    simp only [received, initialInput, sourceInputs, basis, List.map_append, List.map_cons,
      List.map_nil, List.map_map]
    congr 1
    · simp [f]
    · apply List.map_congr_left
      intro q _
      cases q <;> simp [f, smul_smul, mul_comm]
  rw [hb, evaluate_map] at hv
  dsimp only
  change (z.1.value.groups false).headD 0 = _
  rw [← hv]
  simp [f, basis, add_smul, mul_smul]

private theorem reductionRun_eq_table {F T G₁ G₂ Gₜ R V : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [AddMonoid R] [SMul F R]
    [DecidableEq T] [SampleableType R]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) (pk : G₂)
    (hash sign : R → G₁) (hashRep signRep : R → V) (initial : List V)
    (S : Finset (T × Fin (degree + 1)))
    (hS : WeightedInterfaceCovered S (terms degree) (fun out => out.value.data) (rawMain A pk))
    (fallback : R) :
    OOPS.reductionRun A.toAdversary g₁ g₂ pk hash sign hashRep signRep initial =ᵈ
      (do
        let table ← $ᵗ (S → R)
        let H := extendTable S fallback table
        let value := fun m : F × T =>
          ((terms degree m).map fun p : (T × Fin (degree + 1)) × F => p.2 • H p.1).sum
        let z ← weightedFixedRun (fun i => hash (H i)) (fun m => sign (value m)) (rawMain A pk)
        return (z.1, initial ++ z.2.map
          (Sum.elim (fun i => hashRep (H i)) (fun m => signRep (value m))),
          value z.1.value.data)) := by
  have h := weightedExtractionProgram_evalDistEq_finite_table (terms degree)
    (fun out => out.value.data) hash sign hashRep signRep initial (rawMain A pk) S fallback
    (weightedExtractionProgram_covered S (terms degree) (fun out => out.value.data)
      hash sign hashRep signRep initial (rawMain A pk) hS)
  simpa only [OOPS.reductionRun, rawMain, weightedTableOracle_run_eq,
    Functor.map_map, bind_pure_comp, Function.comp_def] using h

end OOPS.AGM
