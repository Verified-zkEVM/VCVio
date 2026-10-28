/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Proximity.Collision
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! # Soundness of Proximity's chronological representations

The certified interactive execution explains the final signature over exactly the initial
generator and the chronological hash and signing replies. Applying a linear interpretation to
that basis gives the affine exponent used by the good reduction. A nonzero verification gap
therefore extracts the signing secret from every accepting execution.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace Proximity.AGM

private def received {I M G₁ G₂ : Type} (initial : Groups (Group G₁ G₂))
    (hash : I → G₁) (sign : M → G₁) (tr : Weighted.Transcript I M) : Groups (Group G₁ G₂) :=
  sourceInputs (initial false ++ tr.map (Sum.elim hash sign)) (initial true)

private def fixedPlainOracle {F Slot G₁ G₂ : Type} {dimension : ℕ}
    (hash : Index Slot dimension → G₁) (sign : Proximity.Message F Slot dimension → G₁) :
    QueryImpl (plainSpec (Group G₁ G₂) (Query F Slot dimension) Reply) ProbComp := by
  intro ⟨q, _⟩
  rcases q with ((n | i) | m)
  · exact (fun r => ⟨r, sourceInputs [] []⟩) <$> (unifSpec.query n : ProbComp _)
  · exact pure ⟨(), sourceInputs [hash i] []⟩
  · exact pure ⟨(), sourceInputs [sign m] []⟩

private theorem received_empty {I M G₁ G₂ : Type} (initial : Groups (Group G₁ G₂))
    (hash : I → G₁) (sign : M → G₁) : received initial hash sign [] = initial := by
  funext s
  cases s <;> simp [received, sourceInputs]

private theorem fixedRun_groups {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) (pk : G₂)
    (hash : Index Slot dimension → G₁) (sign : Proximity.Message F Slot dimension → G₁) :
    (fun z => (z.1, received (initialInput g₁ g₂ pk).groups hash sign z.2)) <$>
      weightedFixedRun hash sign (A.rawMain pk) =
      A.toAdversary.run (fixedPlainOracle hash sign) (initialInput g₁ g₂ pk) := by
  let input := initialInput g₁ g₂ pk
  let impl₁ := (weightedFixedOracle hash sign) ∘ₛ (fun q => oracle q.value
    : QueryImpl (explainedSpec F (Group G₁ G₂) (Query F Slot dimension) Reply)
      (OracleComp (rawSpec F Slot G₁ dimension)))
  let impl₂ : QueryImpl (explainedSpec F (Group G₁ G₂) (Query F Slot dimension) Reply)
      (StateT (Groups (Group G₁ G₂)) ProbComp) := fun q => StateT.mk fun basis => do
    let reply ← fixedPlainOracle hash sign q.value
    return (reply, extend basis reply.groups)
  have hstep : ∀ q tr, Prod.map id (received input.groups hash sign) <$>
      (impl₁ q).run tr = (impl₂ q).run (received input.groups hash sign tr) := by
    intro ⟨⟨q, groups⟩, coeff⟩ tr
    rcases q with ((n | i) | m) <;>
      simp only [impl₁, impl₂, QueryImpl.apply_compose, oracle, fixedPlainOracle,
        simulateQ_map, simulateQ_spec_query, StateT.run_map, StateT.run_mk,
        bind_pure_comp, Functor.map_map]
    · change (fun r : Fin (n + 1) =>
          ((⟨r, sourceInputs [] []⟩ : GroupModel.Interaction.Message _ (Group G₁ G₂)),
            received input.groups hash sign tr)) <$> (unifSpec.query n : ProbComp _) =
        (fun r : Fin (n + 1) =>
          ((⟨r, sourceInputs [] []⟩ : GroupModel.Interaction.Message _ (Group G₁ G₂)),
            extend (received input.groups hash sign tr) (sourceInputs [] []))) <$>
          (unifSpec.query n : ProbComp _)
      congr 1
      funext r
      apply Prod.ext
      · rfl
      · funext s
        cases s <;> simp [received, sourceInputs, extend]
    · simp only [weightedFixedOracle, StateT.run, map_pure, Prod.map_apply', id_eq]
      apply congrArg pure
      apply Prod.ext
      · rfl
      · funext s
        cases s <;> simp [received, sourceInputs, extend, List.append_assoc]
    · simp only [weightedFixedOracle, StateT.run, map_pure, Prod.map_apply', id_eq]
      apply congrArg pure
      apply Prod.ext
      · rfl
      · funext s
        cases s <;> simp [received, sourceInputs, extend, List.append_assoc]
  have h := map_run_simulateQ_eq_of_query_map_eq impl₁ impl₂
    (received input.groups hash sign) hstep (A.main input) []
  rw [received_empty] at h
  simpa only [impl₁, QueryImpl.simulateQ_compose, impl₂, Adversary.run,
    weightedFixedRun, AlgebraicAdversary.rawMain, input, Prod.map_def, id_eq] using h

private theorem fixedRun_valid {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) (pk : G₂)
    (hash : Index Slot dimension → G₁) (sign : Proximity.Message F Slot dimension → G₁)
    (z : Explained F (Proximity.Message F Slot dimension) (Group G₁ G₂) ×
      Weighted.Transcript (Index Slot dimension) (Proximity.Message F Slot dimension))
    (hz : z ∈ support (weightedFixedRun hash sign (A.rawMain pk))) :
    z.1.Valid (received (initialInput g₁ g₂ pk).groups hash sign z.2) := by
  apply A.toAdversary.run_valid (fixedPlainOracle hash sign) (initialInput g₁ g₂ pk)
    (z.1, received (initialInput g₁ g₂ pk).groups hash sign z.2)
  rw [← fixedRun_groups]
  rw [support_map]
  exact ⟨z, hz, rfl⟩

private theorem valid_head {F Slot G₁ G₂ : Type} [Semiring F] {dimension : ℕ}
    [AddCommMonoid G₁] [Module F G₁] [AddCommMonoid G₂] [Module F G₂]
    (out : Explained F (Proximity.Message F Slot dimension) (Group G₁ G₂))
    (inputs : Groups (Group G₁ G₂)) (h : out.Valid inputs) :
    evaluate (coefficients out) (inputs false) = (forgery out).2 := by
  have hv := h false
  cases hg : out.value.groups false with
  | nil => simp [coefficients, forgery, hg, evaluate, List.mapIdx_eq_ofFn]
  | cons σ rest =>
      cases hc : out.coefficients false with
      | nil => simp [hg, hc] at hv
      | cons c cs =>
          rw [hg, hc] at hv
          have he := (List.forall₂_cons.mp hv).1.2
          simpa [coefficients, forgery, hg, hc] using he

/-- The affine representation obtained by interpreting a scalar-programmed transcript. -/
@[expose] def goodRepresentation {F Slot G₁ G₂ : Type} [Semiring F] {dimension : ℕ}
    (ρ : Index Slot dimension → F)
    (out : Explained F (Proximity.Message F Slot dimension) (Group G₁ G₂))
    (tr : Weighted.Transcript (Index Slot dimension) (Proximity.Message F Slot dimension)) :
    AffineForm F :=
  let r := evaluate (coefficients out) ([(1, 0)] ++ tr.map
    (Sum.elim (fun i => (ρ i, (0 : F))) (fun m => ((0 : F), Weighted.value ρ (terms m)))))
  ⟨r.1, r.2⟩

/-- Algebraicity makes the chronological affine representation equal the actual forged signature. -/
theorem fixedRun_good_sound {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) (κ : F)
    (ρ : Index Slot dimension → F)
    (z : Explained F (Proximity.Message F Slot dimension) (Group G₁ G₂) ×
      Weighted.Transcript (Index Slot dimension) (Proximity.Message F Slot dimension))
    (hz : z ∈ support (weightedFixedRun (fun i => ρ i • g₁)
      (fun m => Weighted.value ρ (terms m) • (κ • g₁)) (A.rawMain (κ • g₂)))) :
    (forgery z.1).2 = (goodRepresentation ρ z.1 z.2).eval κ • g₁ := by
  let f : (F × F) →ₗ[F] G₁ :=
    (LinearMap.fst F F F).smulRight g₁ + (LinearMap.snd F F F).smulRight (κ • g₁)
  have hv := valid_head z.1 _ (fixedRun_valid A (κ • g₂) _ _ z hz)
  let basis : List (F × F) := [(1, 0)] ++ z.2.map
    (Sum.elim (fun i => (ρ i, (0 : F))) (fun m => ((0 : F), Weighted.value ρ (terms m))))
  have hb : (received (initialInput g₁ g₂ (κ • g₂)).groups
      (fun i => ρ i • g₁) (fun m => Weighted.value ρ (terms m) • (κ • g₁)) z.2) false =
      basis.map f := by
    simp only [received, initialInput, sourceInputs, basis, List.map_append, List.map_cons,
      List.map_nil, List.map_map]
    congr 1
    · simp [f]
    · apply List.map_congr_left
      intro q _
      cases q <;> simp [f]
  rw [hb, evaluate_map] at hv
  rw [← hv]
  simp [f, basis, goodRepresentation, AffineForm.eval, add_smul, mul_smul]

/-- Every accepting fixed-table execution with nonzero gap yields the secret returned by
Proximity's good reduction. No noncollision or freshness assumption is needed for this branch. -/
theorem goodRepresentation_extract {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) (κ : F)
    (ρ : Index Slot dimension → F)
    (z : Explained F (Proximity.Message F Slot dimension) (Group G₁ G₂) ×
      Weighted.Transcript (Index Slot dimension) (Proximity.Message F Slot dimension))
    (hz : z ∈ support (weightedFixedRun (fun i => ρ i • g₁)
      (fun m => Weighted.value ρ (terms m) • (κ • g₁)) (A.rawMain (κ • g₂))))
    (he : e g₁ g₂ ≠ 0)
    (hv : e (forgery z.1).2 g₂ = e (Weighted.value ρ (terms z.1.value.data) • g₁) (κ • g₂))
    (hgap : (goodRepresentation ρ z.1 z.2).lin ≠ Weighted.value ρ (terms z.1.value.data)) :
    (goodRepresentation ρ z.1 z.2).const /
      (Weighted.value ρ (terms z.1.value.data) - (goodRepresentation ρ z.1 z.2).lin) = κ := by
  exact (AffineForm.extract_secret
    (pairing_eq_implies_eval_eq e g₁ g₂ he (fixedRun_good_sound A κ ρ z hz) hv) hgap).symm

end Proximity.AGM
