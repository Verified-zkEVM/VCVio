/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.SynchronizedPS.Reductions
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedTrace
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Interaction
import all VCVio.Schemes.SynchronizedPS.Reductions

/-! # Algebraic soundness of chronological SynchronizedPS executions

The public transcript records only replies received by the adversary. Fixed base tables
interpret the lazy reductions and their explanation vectors in this same chronological order.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace SynchronizedPS.AGM

/-- The explained adversary computation with its protocol queries forwarded to the signature
algorithm's ambient and signing interfaces. -/
@[expose] def rawMain {F T G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) (pk : G₂ × G₂) :=
  simulateQ (fun q => oracle q.value) (A.main (initialInput g₁ g₂ pk))

private def received {F T G₁ G₂ : Type}
    (initial : Groups (SourceGroup G₁ G₂))
    (hash : T → G₁) (sign : T × F → G₁)
    (tr : List (T ⊕ (T × F))) :
    Groups (SourceGroup G₁ G₂) :=
  sourceInputs (initial false ++ tr.map (Sum.elim hash sign))
    (initial true)

private def fixedPlainOracle {F T G₁ G₂ : Type}
    (hash : T → G₁) (sign : T × F → G₁) :
    QueryImpl (plainSpec (SourceGroup G₁ G₂) (Query F T) Reply) ProbComp := by
  intro ⟨q, _⟩
  rcases q with ((n | m) | m)
  · exact (fun r => ⟨r, sourceInputs [] []⟩) <$> (unifSpec.query n : ProbComp _)
  · exact pure ⟨(), sourceInputs [hash m] []⟩
  · exact pure ⟨(), sourceInputs [sign m] []⟩

private theorem received_empty {F T G₁ G₂ : Type}
    (initial : Groups (SourceGroup G₁ G₂))
    (hash : T → G₁) (sign : T × F → G₁) :
    received initial hash sign [] = initial := by
  funext s
  cases s <;> simp [received, sourceInputs]

private theorem weightedFixedRun_groups {F T G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) (pk : G₂ × G₂)
    (hash : T → G₁) (sign : T × F → G₁) :
    (fun z => (z.1, received (initialInput g₁ g₂ pk).groups hash sign z.2)) <$>
      weightedFixedRun hash sign (rawMain A pk) =
      A.toAdversary.run (fixedPlainOracle hash sign) (initialInput g₁ g₂ pk) := by
  let input := initialInput g₁ g₂ pk
  let impl₁ := (weightedFixedOracle hash sign) ∘ₛ (fun q => oracle q.value
    : QueryImpl (explainedSpec F (SourceGroup G₁ G₂) (Query F T) Reply)
      (OracleComp (rawSpec F T G₁)))
  let impl₂ : QueryImpl (explainedSpec F (SourceGroup G₁ G₂) (Query F T) Reply)
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
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) (pk : G₂ × G₂)
    (hash : T → G₁) (sign : T × F → G₁)
    (z : Explained F ((T × F) × List ((F × F) × F)) (SourceGroup G₁ G₂) ×
      List (T ⊕ (T × F)))
    (hz : z ∈ support (weightedFixedRun hash sign (rawMain A pk))) :
    z.1.Valid (received (initialInput g₁ g₂ pk).groups hash sign z.2) := by
  apply A.toAdversary.run_valid (fixedPlainOracle hash sign) (initialInput g₁ g₂ pk)
    (z.1, received (initialInput g₁ g₂ pk).groups hash sign z.2)
  rw [← weightedFixedRun_groups]
  rw [support_map]
  exact ⟨z, hz, rfl⟩


/-- The public view under a fixed period-exponent table and two signing secrets. -/
@[expose] def fixedView {F T G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) (ρ : T → F) (x y : F) :=
  weightedFixedRun (fun t => ρ t • g₁) (fun tm => (x + y * tm.2) • (ρ tm.1 • g₁))
    (rawMain A (publicKeyOf g₂ (x, y)))

/-- The constant, first-secret, and second-secret coefficients of an explained aggregate. -/
@[expose] def representation {F T : Type} [Semiring F]
    (coeff : List F) (tr : List (T ⊕ (T × F))) (ρ : T → F) : F × F × F :=
  evaluate coeff ((1, 0, 0) :: tr.map (Sum.elim (fun t => (ρ t, 0, 0))
    (fun tm => (0, ρ tm.1, ρ tm.1 * tm.2))))

/-- Every supported fixed-table execution has the explained two-secret scalar representation. -/
theorem fixedView_sound {F T G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) (ρ : T → F) (x y : F)
    (z : Explained F ((T × F) × List ((F × F) × F)) (SourceGroup G₁ G₂) ×
      List (T ⊕ (T × F))) (hz : z ∈ support (fixedView A ρ x y)) :
    let r := representation ((z.1.coefficients false).headD []) z.2 ρ
    (forgery z.1).2.2 = (r.1 + r.2.1 * x + r.2.2 * y) • g₁ := by
  let f : (F × F × F) →ₗ[F] G₁ :=
    (LinearMap.fst F F (F × F)).smulRight g₁ +
      ((LinearMap.fst F F F).comp (LinearMap.snd F F (F × F))).smulRight (x • g₁) +
      ((LinearMap.snd F F F).comp (LinearMap.snd F F (F × F))).smulRight (y • g₁)
  have hv := z.1.evaluate_headD
    (received (initialInput g₁ g₂ (publicKeyOf g₂ (x, y))).groups
      (fun t => ρ t • g₁) (fun tm => (x + y * tm.2) • (ρ tm.1 • g₁)) z.2)
    (by intro s; cases s <;> exact weightedFixedRun_valid A _ _ _ z hz _) false
  let basis : List (F × F × F) := (1, 0, 0) :: z.2.map
    (Sum.elim (fun t => (ρ t, 0, 0)) (fun tm => (0, ρ tm.1, ρ tm.1 * tm.2)))
  have hb : (received (initialInput g₁ g₂ (publicKeyOf g₂ (x, y))).groups
      (fun t => ρ t • g₁) (fun tm => (x + y * tm.2) • (ρ tm.1 • g₁)) z.2) false =
      basis.map f := by
    simp only [received, initialInput, sourceInputs, basis, List.singleton_append,
      List.map_cons, List.map_map]
    congr 1
    · simp [f]
    · apply List.map_congr_left
      intro q _
      cases q with
      | inl t => simp [f]
      | inr tm =>
        simp only [Function.comp_apply, Sum.elim_inr, f, LinearMap.add_apply,
          LinearMap.smulRight_apply, LinearMap.fst_apply, LinearMap.snd_apply,
          LinearMap.comp_apply, zero_smul, zero_add, smul_smul, ← add_smul]
        congr 1
        ring
  rw [hb, evaluate_map] at hv
  dsimp only
  change (z.1.value.groups false).headD 0 = _
  rw [← hv]
  simp [f, basis, representation, add_smul, mul_smul]

set_option maxHeartbeats 800000 in
-- Elaborating the dependent oracle and representation types needs additional reduction steps.
/-- The lazy extraction runner is distributed as a uniform finite table on any public cover.
The label type itself is unrestricted and all repeated accesses use the same table. -/
private theorem reductionRun_eq_table {F T G₁ G₂ Gₜ R V : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [AddCommMonoid R] [Module F R]
    [DecidableEq T] [SampleableType R]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) (pk : G₂ × G₂)
    (hash : R → G₁) (sign : (T × F) → R → G₁)
    (hashRep : R → V) (signRep : (T × F) → R → V) (initial : List V)
    (S : Finset T)
    (hS : WeightedInterfaceCovered S terms (fun out => out.value.data.1) (rawMain A pk))
    (fallback : R) :
    SynchronizedPS.reductionRun A.toAdversary g₁ g₂ pk hash sign hashRep signRep initial =ᵈ
      (do
        let table ← $ᵗ (S → R)
        let H := extendTable S fallback table
        let z ← weightedFixedRun (fun i => hash (H i)) (fun m => sign m (H m.1)) (rawMain A pk)
        return (z.1, initial ++ z.2.map
          (Sum.elim (fun i => hashRep (H i)) (fun m => signRep m (H m.1))),
          H z.1.value.data.1.1)) := by
  have h := indexedWeightedExtractionProgram_evalDistEq_finite_table terms
    (fun out => out.value.data.1) hash sign hashRep signRep initial (rawMain A pk) S fallback
    (indexedWeightedExtractionProgram_covered S terms (fun out => out.value.data.1)
      hash sign hashRep signRep initial (rawMain A pk) hS)
  simpa only [SynchronizedPS.reductionRun, rawMain, indexedWeightedTableOracle_run_eq,
    Functor.map_map, bind_pure_comp, Function.comp_def, terms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, one_smul] using h

end SynchronizedPS.AGM
