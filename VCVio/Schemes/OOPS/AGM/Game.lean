/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.OOPS.AGM.Table

/-! # Signing transcripts in the existing OOPS signature game

The fixed-table interpretation preserves the actual signing messages of the existing
signature experiment. In particular, its target-topic degree predicate transports without
introducing another unforgeability experiment.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace OOPS.AGM

private theorem fixed_writerTMapBase {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ pk : G₂) (degree : ℕ) (x : F)
    (H : T × Fin (degree + 1) → G₁) :
    (unifFwdAnswerImpl (QueryImpl.ofFn H)).writerTMapBase
      ((unifSpec + ((T × Fin (degree + 1)) →ₒ G₁)).passthrough +
        (scheme (T := T) e g₂ degree).signingOracle pk x) =
    (unifFwdAnswerImpl (QueryImpl.ofFn H)).liftTarget
      (WriterT (QueryLog ((F × T) →ₒ G₁)) ProbComp) +
      QueryImpl.withLogging (fun m : F × T =>
        (pure (x • ((terms degree m).map fun p => p.2 • H p.1).sum) : ProbComp G₁)) := by
  funext q
  rcases q with q | m
  · apply WriterT.ext
    simp [QueryImpl.writerTMapBase, QueryImpl.liftTarget]
  · apply WriterT.ext
    simp [QueryImpl.writerTMapBase, SignatureAlg.signingOracle, QueryImpl.withLogging_apply,
      scheme, hash, simulateQ_unifFwd_weightedQuery, map_eq_bind_pure_comp]

/-- Fixing the base table preserves the exact signing-message projection of the existing
signing-oracle runner, including order and repeated requests. -/
theorem runWithSigningOracle_fixedTable {F T G₁ G₂ Gₜ α : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ pk : G₂) (degree : ℕ) (x : F)
    (H : T × Fin (degree + 1) → G₁) (oa : OracleComp (rawSpec F T G₁ degree) α) :
    (fun z => (z.1, z.2.map fun q => q.1)) <$>
      simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H))
        ((scheme e g₂ degree).runWithSigningOracle pk x oa) =
    (fun z => (z.1, weightedSignedMessages z.2)) <$>
      weightedFixedRun H (fun m => x • ((terms degree m).map fun p => p.2 • H p.1).sum) oa := by
  let base := unifFwdAnswerImpl (QueryImpl.ofFn H)
  let sign : QueryImpl ((F × T) →ₒ G₁) ProbComp := fun m =>
    pure (x • ((terms degree m).map fun p => p.2 • H p.1).sum)
  let hq : HasQuery (unifSpec + ((T × Fin (degree + 1)) →ₒ G₁)) ProbComp := base.toHasQuery
  rw [SignatureAlg.runWithSigningOracle_def, QueryImpl.simulateQ_writerTMapBase_run,
    fixed_writerTMapBase]
  have hr := QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
    (spec₀ := unifSpec + ((T × Fin (degree + 1)) →ₒ G₁))
    (loggedSpec := (F × T) →ₒ G₁) (m₀ := ProbComp) sign oa []
  change (fun z => (z.1, [] ++ z.2.map fun q => q.1)) <$>
      (simulateQ (base.liftTarget (WriterT (QueryLog ((F × T) →ₒ G₁)) ProbComp) +
        QueryImpl.withLogging sign) oa).run = _ at hr
  simp only [List.nil_append] at hr
  rw [hr]
  symm
  have hstep : ∀ q tr, Prod.map id weightedSignedMessages <$>
      ((weightedFixedOracle H
        (fun m => x • ((terms degree m).map fun p => p.2 • H p.1).sum)) q).run tr =
      ((base.liftTarget (StateT (List (F × T)) ProbComp) +
        QueryImpl.appendInputLog sign) q).run (weightedSignedMessages tr) := by
    intro q tr
    rcases q with ((n | i) | m) <;>
      simp only [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        QueryImpl.liftTarget_apply, StateT.run_monadLift, monadLift_self,
        QueryImpl.run_appendInputLog_apply]
    all_goals
      simp [weightedFixedOracle, weightedSignedMessages, base, sign, StateT.run,
        unifFwdAnswerImpl, List.filterMap_cons]
    rfl
  have h := map_run_simulateQ_eq_of_query_map_eq _ _ weightedSignedMessages hstep oa []
  change _ = (simulateQ (base.liftTarget (StateT (List (F × T)) ProbComp) +
    QueryImpl.appendInputLog sign) oa).run []
  simpa only [weightedFixedRun, Prod.map_def, id_eq, weightedSignedMessages,
    List.filterMap_nil] using h

/-- Successful fresh fixed-table forgeries obey the degree rule, by transporting the signing
runner and verifier together into the existing shared-cache random-oracle execution. -/
theorem fixedRun_admissible {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [DecidableEq F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) (hA : A.Admissible)
    (x : F) (H : T × Fin (degree + 1) → G₁)
    (z : Explained F (F × T) (SourceGroup G₁ G₂) ×
      List ((T × Fin (degree + 1)) ⊕ (F × T)))
    (hz : z ∈ support (weightedFixedRun H
      (fun m => x • ((terms degree m).map fun p => p.2 • H p.1).sum)
      (rawMain A (x • g₂))))
    (hfresh : z.1.value.data ∉ weightedSignedMessages z.2)
    (hverify : e (forgery z.1).2 g₂ =
      e (((terms degree z.1.value.data).map fun p => p.2 • H p.1).sum) (x • g₂)) :
    admissible degree z.1.value.data (weightedSignedMessages z.2) := by
  have hproj := runWithSigningOracle_fixedTable e g₂ (x • g₂) degree x H
    (A.toUnforgeableAdversary.main (x • g₂))
  simp only [AlgebraicAdversary.toUnforgeableAdversary, weightedFixedRun, simulateQ_map,
    StateT.run_map, Functor.map_map] at hproj
  have hz' : (forgery z.1, weightedSignedMessages z.2) ∈ support
      ((fun z => (z.1, z.2.map fun q => q.1)) <$>
        simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H))
          ((scheme e g₂ degree).runWithSigningOracle (x • g₂) x
            (A.toUnforgeableAdversary.main (x • g₂)))) := by
    simp only [AlgebraicAdversary.toUnforgeableAdversary]
    rw [hproj, support_map]
    exact ⟨z, hz, rfl⟩
  rw [support_map] at hz'
  obtain ⟨w, hw, heq⟩ := hz'
  have hm := congrArg (fun z => z.1.1) heq
  have hs := congrArg Prod.snd heq
  have hσ := congrArg (fun z => z.1.2) heq
  change w.1.2 = (forgery z.1).2 at hσ
  change w.1.1 = z.1.value.data at hm
  change w.2.map (fun q => q.1) = weightedSignedMessages z.2 at hs
  have hsuccess : (w, true) ∈ support
      (simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)) (do
        let w ← (scheme e g₂ degree).runWithSigningOracle (x • g₂) x
          (A.toUnforgeableAdversary.main (x • g₂))
        let accepted ← (scheme e g₂ degree).verify (x • g₂) w.1.1 w.1.2
        return (w, accepted))) := by
    simp only [simulateQ_bind, simulateQ_pure, support_bind, Set.mem_iUnion]
    refine ⟨w, hw, ?_⟩
    simp only [scheme, hash, simulateQ_bind, simulateQ_unifFwd_weightedQuery,
      pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff]
    exact ⟨true, by simp only [hm, hσ, hverify, decide_true], rfl⟩
  obtain ⟨cache, hc⟩ :=
    (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff _ ∅ (w, true)).mp
      ⟨QueryImpl.ofFn H, by intro i u hu; simp at hu, hsuccess⟩
  have hadm := hA x (w, true) (by
    rw [StateT.run'_eq, support_map]
    exact ⟨((w, true), cache), hc, rfl⟩) (by simpa only [hm, hs] using hfresh) rfl
  simpa only [hm, hs] using hadm

open scoped Classical in
private theorem unforgeableExperiment_fixedTable {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (degree : ℕ)
    (A : SignatureAlg.UnforgeableAdversary (scheme (T := T) e g₂ degree))
    (H : T × Fin (degree + 1) → G₁) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)) (SignatureAlg.unforgeableExperiment A) =
      (do
        let x ← ($ᵗ F : ProbComp F)
        let z ← weightedFixedRun H
          (fun m => x • ((terms degree m).map fun p => p.2 • H p.1).sum)
          (A.main (x • g₂))
        return decide (z.1.1 ∉ weightedSignedMessages z.2) &&
          decide (e z.1.2 g₂ = e (((terms degree z.1.1).map fun p => p.2 • H p.1).sum)
            (x • g₂))) := by
  classical
  have hlift : ∀ {α : Type} (oa : ProbComp α),
      simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)) (liftM oa) = oa := by
    intro α oa
    change simulateQ (unifSpec.passthrough + (QueryImpl.ofFn H).liftTarget ProbComp)
      (OracleComp.liftComp oa (unifSpec + ((T × Fin (degree + 1)) →ₒ G₁))) = oa
    simpa using QueryImpl.simulateQ_add_liftComp_left
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp) ((QueryImpl.ofFn H).liftTarget _) oa
  simp only [SignatureAlg.unforgeableExperiment, scheme, bind_assoc, pure_bind,
    simulateQ_bind, simulateQ_pure, hlift, hash, simulateQ_unifFwd_weightedQuery]
  apply bind_congr
  intro x
  have h := congrArg (fun oc => (fun z : ((F × T) × G₁) × List (F × T) =>
    decide (z.1.1 ∉ z.2) && decide (e z.1.2 g₂ =
      e (((terms degree z.1.1).map fun p => p.2 • H p.1).sum) (x • g₂))) <$> oc)
    (runWithSigningOracle_fixedTable e g₂ (x • g₂) degree x H (A.main (x • g₂)))
  simp only [Functor.map_map, bind_pure_comp,
    QueryLog.wasQueried_eq_decide_mem_map_fst, decide_not] at h ⊢
  convert h using 2
  · funext a
    congr 2
    exact decide_eq_decide.mpr Iff.rfl
  · simp only [scheme, hash, bind_pure_comp]

/-- A finite cover of the existing signature experiment gives its exact fixed-table winning
probability; all signing requests and final verification use the same table. -/
theorem unforgeableAdvantage_eq_table {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq T]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree)
    (S : Finset (T × Fin (degree + 1)))
    (hS : QueriesCovered S (SignatureAlg.unforgeableExperiment A.toUnforgeableAdversary)) :
    SignatureAlg.unforgeableAdvantage
        (ProbCompRuntime.rom ((T × Fin (degree + 1)) →ₒ G₁)) A.toUnforgeableAdversary =
      Pr{let table ← ($ᵗ (S → G₁) : ProbComp _)
         let x ← ($ᵗ F : ProbComp F)
         let H := extendTable S 0 table
         let z ← weightedFixedRun H
           (fun m => x • ((terms degree m).map fun p => p.2 • H p.1).sum)
           (rawMain A (x • g₂))}[
        z.1.value.data ∉ weightedSignedMessages z.2 ∧
          e (forgery z.1).2 g₂ =
            e (((terms degree z.1.value.data).map fun p => p.2 • H p.1).sum) (x • g₂)] := by
  rw [SignatureAlg.unforgeableAdvantage, ProbCompRuntime.rom_evalDist,
    ← prEvent_eq_evalDist_singleton]
  rw [(simulateQ_romImpl_evalDistEq_finite_table S _ hS (0 : G₁)).prEvent_eq]
  simp only [unforgeableExperiment_fixedTable, AlgebraicAdversary.toUnforgeableAdversary,
    weightedFixedRun, simulateQ_map, StateT.run_map, map_bind, bind_map_left,
    rawMain, prEvent_norm, Bool.and_eq_true, decide_eq_true_eq, forgery]

private theorem terms_smul {F I G : Type} [Semiring F] [AddCommMonoid G] [Module F G]
    (ts : List (I × F)) (ρ : I → F) (g : G) :
    (ts.map fun p => p.2 • (ρ p.1 • g)).sum =
      (ts.map fun p => p.2 * ρ p.1).sum • g := by
  induction ts with
  | nil => simp
  | cons p rest ih => simp [ih, add_smul, mul_smul]

private theorem table_smul {F I G : Type} [Semiring F] [AddCommMonoid G] [Module F G]
    [DecidableEq I] (S : Finset I) (ρ : S → F) (g : G) (i : I) :
    extendTable S 0 (fun i => ρ i • g) i = extendTable S 0 ρ i • g := by
  simp only [GroupModel.LinearFunctional.extendTable]
  split <;> simp

/-- Successful fresh forgeries in the common scalar-table view obey the degree rule. -/
theorem fixedView_admissible {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [DecidableEq F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) (hA : A.Admissible)
    (x : F) (ρ : T × Fin (degree + 1) → F)
    (z : Explained F (F × T) (SourceGroup G₁ G₂) ×
      List ((T × Fin (degree + 1)) ⊕ (F × T)))
    (hz : z ∈ support (fixedView A ρ x))
    (hfresh : z.1.value.data ∉ weightedSignedMessages z.2)
    (hverify : e (forgery z.1).2 g₂ = e (scalarHash degree ρ z.1.value.data • g₁) (x • g₂)) :
    admissible degree z.1.value.data (weightedSignedMessages z.2) := by
  apply fixedRun_admissible A hA x (fun i => ρ i • g₁) z
  · simpa only [terms_smul, fixedView, scalarHash] using hz
  · exact hfresh
  · simpa only [terms_smul, scalarHash] using hverify

/-- Generator bijectivity identifies the existing advantage with the common scalar-table
view. This preserves both freshness and the original pairing verification equation. -/
theorem unforgeableAdvantage_eq_scalarTable {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq T]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁))
    (S : Finset (T × Fin (degree + 1)))
    (hS : QueriesCovered S (SignatureAlg.unforgeableExperiment A.toUnforgeableAdversary)) :
    SignatureAlg.unforgeableAdvantage
        (ProbCompRuntime.rom ((T × Fin (degree + 1)) →ₒ G₁)) A.toUnforgeableAdversary =
      Pr{let ρ ← ($ᵗ (S → F) : ProbComp _)
         let x ← ($ᵗ F : ProbComp F)
         let z ← fixedView A (extendTable S 0 ρ) x}[
        z.1.value.data ∉ weightedSignedMessages z.2 ∧
          e (forgery z.1).2 g₂ =
            e (scalarHash degree (extendTable S 0 ρ) z.1.value.data • g₁) (x • g₂)] := by
  classical
  have hbij : Function.Bijective (fun ρ : S → F => fun i => ρ i • g₁) := by
    constructor
    · intro a b h
      exact funext fun i => hg₁.1 (congrFun h i)
    · intro H
      choose ρ hρ using fun i => hg₁.2 (H i)
      exact ⟨ρ, funext hρ⟩
  have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective hbij).bind_left
    (fun H : S → G₁ => simulateQ
      (unifFwdAnswerImpl (QueryImpl.ofFn (extendTable S 0 H)))
      (SignatureAlg.unforgeableExperiment A.toUnforgeableAdversary))
  rw [SignatureAlg.unforgeableAdvantage, ProbCompRuntime.rom_evalDist,
    ← prEvent_eq_evalDist_singleton]
  rw [(simulateQ_romImpl_evalDistEq_finite_table S _ hS (0 : G₁)).prEvent_eq,
    ← h.prEvent_eq (· = true)]
  have htab (ρ : S → F) : extendTable S 0 (fun i => ρ i • g₁) =
      (fun i => extendTable S 0 ρ i • g₁) := funext (table_smul S ρ g₁)
  simp only [bind_map_left, unforgeableExperiment_fixedTable, htab, terms_smul,
    AlgebraicAdversary.toUnforgeableAdversary, weightedFixedRun, simulateQ_map,
    StateT.run_map, fixedView, rawMain, scalarHash, prEvent_norm,
    Bool.and_eq_true, decide_eq_true_eq, forgery]

end OOPS.AGM
