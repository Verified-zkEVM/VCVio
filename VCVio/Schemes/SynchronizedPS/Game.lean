/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.SynchronizedPS.Execution

/-! # Signing transcripts in the synchronized certified-key game

The fixed-table interpretation preserves the actual signing messages of the existing
aggregate experiment, including duplicate signing occurrences and the once-per-period
winning condition. The random-oracle cache is shared with final aggregate verification.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace SynchronizedPS.AGM

private theorem fixed_writerTMapBase {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq T]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (pk : G₂ × G₂) (sk : F × F)
    (H : T → G₁) :
    (unifFwdAnswerImpl (QueryImpl.ofFn H)).writerTMapBase
      ((unifSpec + (T →ₒ G₁)).passthrough +
        (scheme (Period := T) e g₂).signingOracle pk sk) =
    (unifFwdAnswerImpl (QueryImpl.ofFn H)).liftTarget
      (WriterT (QueryLog ((T × F) →ₒ G₁)) ProbComp) +
      QueryImpl.withLogging (fun m : T × F =>
        (pure ((sk.1 + sk.2 * m.2) • H m.1) : ProbComp G₁)) := by
  funext q
  rcases q with q | m
  · apply WriterT.ext
    simp [QueryImpl.writerTMapBase, QueryImpl.liftTarget]
  · apply WriterT.ext
    have hId (a : G₁) : (liftM (m := Id) (a : Id G₁) : ProbComp G₁) = pure a := rfl
    simp [QueryImpl.writerTMapBase, SignatureAlg.signingOracle, QueryImpl.withLogging_apply,
      scheme, map_eq_bind_pure_comp, unifFwdAnswerImpl,
      QueryImpl.simulateQ_add_liftM_query_right, hId]

/-- Fixing the period table preserves the exact signing-message projection of the existing
signing-oracle runner, including order and repeated requests. -/
theorem runWithSigningOracle_fixedTable {F T G₁ G₂ Gₜ α : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq T]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (pk : G₂ × G₂) (sk : F × F)
    (H : T → G₁) (oa : OracleComp (rawSpec F T G₁) α) :
    (fun z => (z.1, z.2.map fun q => q.1)) <$>
      simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H))
        ((scheme e g₂).runWithSigningOracle pk sk oa) =
    (fun z => (z.1, weightedSignedMessages z.2)) <$>
      weightedFixedRun H (fun m => (sk.1 + sk.2 * m.2) • H m.1) oa := by
  let base := unifFwdAnswerImpl (QueryImpl.ofFn H)
  let sign : QueryImpl ((T × F) →ₒ G₁) ProbComp := fun m =>
    pure ((sk.1 + sk.2 * m.2) • H m.1)
  let hq : HasQuery (unifSpec + (T →ₒ G₁)) ProbComp := base.toHasQuery
  rw [SignatureAlg.runWithSigningOracle_def, QueryImpl.simulateQ_writerTMapBase_run,
    fixed_writerTMapBase]
  have hr := QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
    (spec₀ := unifSpec + (T →ₒ G₁))
    (loggedSpec := (T × F) →ₒ G₁) (m₀ := ProbComp) sign oa []
  change (fun z => (z.1, [] ++ z.2.map fun q => q.1)) <$>
      (simulateQ (base.liftTarget (WriterT (QueryLog ((T × F) →ₒ G₁)) ProbComp) +
        QueryImpl.withLogging sign) oa).run = _ at hr
  simp only [List.nil_append] at hr
  rw [hr]
  symm
  have hstep : ∀ q tr, Prod.map id weightedSignedMessages <$>
      ((weightedFixedOracle H
        (fun m => (sk.1 + sk.2 * m.2) • H m.1)) q).run tr =
      ((base.liftTarget (StateT (List (T × F)) ProbComp) +
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
  change _ = (simulateQ (base.liftTarget (StateT (List (T × F)) ProbComp) +
    QueryImpl.appendInputLog sign) oa).run []
  simpa only [weightedFixedRun, Prod.map_def, id_eq, weightedSignedMessages,
    List.filterMap_nil] using h

open scoped Classical in
/-- Interpreting the entire certified-key experiment by one fixed period hash table preserves
freshness, synchronization, and the pairing equation with the certified co-signer offset. -/
theorem unforgeableExperiment_fixedTable {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq T]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂)
    (A : AggregateSignatureAlg.Synchronized.Adversary (scheme (Period := T) e g₂))
    (H : T → G₁) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H))
      (AggregateSignatureAlg.Synchronized.unforgeableExperiment (publicKeyOf g₂) A) = (do
        let x ← ($ᵗ F : ProbComp F)
        let y ← $ᵗ F
        let z ← weightedFixedRun H (fun m => (x + y * m.2) • H m.1)
          (A.main (publicKeyOf g₂ (x, y)))
        return decide (z.1.1 ∉ weightedSignedMessages z.2) &&
          decide (AggregateSignatureAlg.Synchronized.OnePerPeriod (weightedSignedMessages z.2)) &&
          decide (e (H z.1.1.1) ((x + y * z.1.1.2 + offset z.1.2.1) • g₂) =
            e z.1.2.2 g₂)) := by
  classical
  have hlift : ∀ {α : Type} (oa : ProbComp α),
      simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)) (liftM oa) = oa := by
    intro α oa
    change simulateQ (unifSpec.passthrough + (QueryImpl.ofFn H).liftTarget ProbComp)
      (OracleComp.liftComp oa (unifSpec + (T →ₒ G₁))) = oa
    simpa using QueryImpl.simulateQ_add_liftComp_left
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp) ((QueryImpl.ofFn H).liftTarget _) oa
  have hquery (t : T) : simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H))
      (liftM ((T →ₒ G₁).query t) : OracleComp (unifSpec + (T →ₒ G₁)) G₁) =
      (pure (H t) : ProbComp G₁) := by
    have hId (a : G₁) : (liftM (m := Id) (a : Id G₁) : ProbComp G₁) = pure a := rfl
    simp [unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_query_right, hId]
  simp only [AggregateSignatureAlg.Synchronized.unforgeableExperiment,
    show (scheme (Period := T) e g₂).keygen = (do
      let x ← (liftM ($ᵗ F) : OracleComp (unifSpec + (T →ₒ G₁)) F)
      let y ← liftM ($ᵗ F)
      return (publicKeyOf g₂ (x, y), (x, y))) from rfl,
    bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, hlift, aggregateVerify_certified,
    hquery]
  apply bind_congr
  intro x
  apply bind_congr
  intro y
  have h := congrArg (fun oc => (fun z :
      AggregateSignatureAlg.Synchronized.Forgery T F (F × F) G₁ × List (T × F) =>
      decide (z.1.1 ∉ z.2) && decide (AggregateSignatureAlg.Synchronized.OnePerPeriod z.2) &&
      decide (e (H z.1.1.1) ((x + y * z.1.1.2 + offset z.1.2.1) • g₂) = e z.1.2.2 g₂)) <$> oc)
    (runWithSigningOracle_fixedTable e g₂ (publicKeyOf g₂ (x, y)) (x, y) H
      (A.main (publicKeyOf g₂ (x, y))))
  simp only [Functor.map_map, bind_pure_comp, AggregateSignatureAlg.Synchronized.winningEvent,
    QueryLog.wasQueried_eq_decide_mem_map_fst, decide_not] at h ⊢
  convert h using 2
  funext a
  congr 3
  exact decide_eq_decide.mpr Iff.rfl

/-- Generator bijectivity transports the exact certified-key advantage to uniform finite
scalar tables without changing freshness, period uniqueness, or aggregate verification. -/
theorem unforgeableAdvantage_eq_scalarTable {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq T]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (S : Finset T)
    (hS : QueriesCovered S (AggregateSignatureAlg.Synchronized.unforgeableExperiment
      (publicKeyOf g₂) A.toUnforgeableAdversary)) :
    AggregateSignatureAlg.Synchronized.unforgeableAdvantage
        (ProbCompRuntime.rom (T →ₒ G₁)) (publicKeyOf g₂) A.toUnforgeableAdversary =
      Pr{let ρ ← ($ᵗ (S → F) : ProbComp _)
         let x ← ($ᵗ F : ProbComp F)
         let y ← $ᵗ F
         let z ← fixedView A (extendTable S 0 ρ) x y}[
        (z.1.value.data.1 ∉ weightedSignedMessages z.2 ∧
          AggregateSignatureAlg.Synchronized.OnePerPeriod (weightedSignedMessages z.2)) ∧
          e (extendTable S 0 ρ z.1.value.data.1.1 • g₁)
            ((x + y * z.1.value.data.1.2 + offset z.1.value.data.2) • g₂) =
              e (forgery z.1).2.2 g₂] := by
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
      (AggregateSignatureAlg.Synchronized.unforgeableExperiment
        (publicKeyOf g₂) A.toUnforgeableAdversary))
  rw [AggregateSignatureAlg.Synchronized.unforgeableAdvantage, ProbCompRuntime.rom_evalDist,
    ← prEvent_eq_evalDist_singleton]
  rw [(simulateQ_romImpl_evalDistEq_finite_table S _ hS (0 : G₁)).prEvent_eq,
    ← h.prEvent_eq (· = true)]
  have htab (ρ : S → F) : extendTable S 0 (fun i => ρ i • g₁) =
      (fun i => extendTable S 0 ρ i • g₁) := by
    funext i
    simp only [GroupModel.LinearFunctional.extendTable]
    split <;> simp
  simp only [bind_map_left, unforgeableExperiment_fixedTable, htab,
    AlgebraicAdversary.toUnforgeableAdversary, weightedFixedRun, simulateQ_map,
    StateT.run_map, fixedView, rawMain, prEvent_norm,
    Bool.and_eq_true, decide_eq_true_eq, forgery]

end SynchronizedPS.AGM
