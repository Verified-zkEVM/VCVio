/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.Proximity.Collision
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! # The direct Proximity game and its chronological presentation

The ordinary `SignatureAlg` experiment is the security game. Projecting its signing log to
messages gives exactly the chronological weighted execution. The equality holds before
random-oracle interpretation, so every shared-cache runtime preserves it, including the
standard lazy random oracle. No separate security game is introduced.
-/

public section

open OracleComp OracleSpec GroupModel.LinearFunctional

namespace Proximity

/-- Projecting the direct signing log gives the signed messages in the weighted transcript. -/
theorem runWithSigningOracle_eq {F Slot G₁ G₂ Gₜ α : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ pk : G₂) (κ : F)
    (oa : OracleComp (AGM.rawSpec F Slot G₁ dimension) α) :
    (fun z => (z.1, z.2.map (fun entry => entry.1))) <$>
      (scheme e g₂).runWithSigningOracle pk κ oa =
    (fun z => (z.1, weightedSignedMessages z.2)) <$>
      (simulateQ (Weighted.oracle terms id (fun r : G₁ => κ • r)) oa).run [] := by
  let spec := unifSpec + (Index Slot dimension →ₒ G₁)
  let sign : QueryImpl (Message F Slot dimension →ₒ G₁) (OracleComp spec) :=
    (scheme e g₂).sign pk κ
  let impl : QueryImpl (AGM.rawSpec F Slot G₁ dimension)
      (StateT (List (Message F Slot dimension)) (OracleComp spec)) :=
    spec.passthrough + QueryImpl.appendInputLog sign
  have hr := QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
    (spec₀ := spec) sign oa []
  have hs : ∀ q tr, Prod.map id weightedSignedMessages <$>
      (Weighted.oracle terms id (fun r : G₁ => κ • r) q).run tr =
      (impl q).run (weightedSignedMessages tr) := by
    intro q tr
    rcases q with ((n | i) | m)
    · change Prod.map id weightedSignedMessages <$>
        ((fun r => (r, tr)) <$>
          (liftM ((unifSpec + (Index Slot dimension →ₒ G₁)).query (.inl n)) :
            OracleComp (unifSpec + (Index Slot dimension →ₒ G₁)) _)) = _
      simp [impl, weightedSignedMessages, spec]
    · change Prod.map id weightedSignedMessages <$>
        ((fun r => (r, tr ++ [.inl i])) <$>
          (liftM ((unifSpec + (Index Slot dimension →ₒ G₁)).query (.inr i)) :
            OracleComp (unifSpec + (Index Slot dimension →ₒ G₁)) _)) = _
      simp [impl, weightedSignedMessages, spec]
      simp only [List.filterMap_cons, Sum.elim_inl, List.filterMap_nil, List.append_nil]
    · change Prod.map id weightedSignedMessages <$>
        ((fun r : G₁ => (κ • r, tr ++ [.inr m])) <$>
          (liftM (weightedQuery (terms m)) : OracleComp spec G₁)) = _
      simp [impl, weightedSignedMessages, sign, scheme, hash]
  have ht := map_run_simulateQ_eq_of_query_map_eq _ impl weightedSignedMessages hs oa []
  simp only [weightedSignedMessages, List.filterMap_nil] at ht
  have hr' : (fun z => (z.1, z.2.map (fun entry => entry.1))) <$>
      (scheme e g₂).runWithSigningOracle pk κ oa = (simulateQ impl oa).run [] := by
    simpa only [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle,
      List.nil_append, sign, impl, QueryImpl.passthrough_add, HasQuery.toQueryImpl_eq_id'] using hr
  exact hr'.trans (by simpa only [Prod.map_def, id_eq] using ht.symm)

open scoped Classical in
/-- The existing EUF-CMA experiment equals the chronological presentation with the same
verification and full-message freshness checks, before interpreting its shared oracle. -/
theorem unforgeableExperiment_eq {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) :
    SignatureAlg.unforgeableExperiment A.toUnforgeableAdversary = (do
      let κ ← (liftM ($ᵗ F) : OracleComp (unifSpec + (Index Slot dimension →ₒ G₁)) F)
      let (out, tr) ← (simulateQ (Weighted.oracle terms id (fun r : G₁ => κ • r))
        (A.rawMain (κ • g₂))).run []
      let h ← hash out.value.data
      return decide (out.value.data ∉ weightedSignedMessages tr) &&
        decide (e (AGM.forgery out).2 g₂ = e h (κ • g₂))) := by
  classical
  have hkey : (scheme (Slot := Slot) (dimension := dimension) e g₂).keygen =
      (do let κ ← liftM ($ᵗ F); return (κ • g₂, κ)) := rfl
  have hver (pk : G₂) (m : Message F Slot dimension) (σ : G₁) :
      (scheme e g₂).verify pk m σ =
        (do let h ← hash m; return decide (e σ g₂ = e h pk)) := rfl
  simp only [SignatureAlg.unforgeableExperiment, hkey, hver, bind_assoc, pure_bind]
  apply bind_congr
  intro κ
  have h := runWithSigningOracle_eq e g₂ (κ • g₂) κ
    (A.toUnforgeableAdversary.main (κ • g₂))
  have h' := congrArg (fun p => p >>= fun z => do
    let h ← hash z.1.1
    return decide (z.1.1 ∉ z.2) && decide (e z.1.2 g₂ = e h (κ • g₂))) h
  simp only [bind_map_left, AlgebraicAdversary.toUnforgeableAdversary,
    simulateQ_map, StateT.run_map, AGM.forgery] at h'
  convert h' using 1
  · apply bind_congr
    intro z
    apply bind_congr
    intro h
    congr 2
    simp only [QueryLog.wasQueried_eq_decide_mem_map_fst, decide_not]
    congr 1
    rw [decide_eq_decide]
  · apply bind_congr
    intro z
    apply bind_congr
    intro h
    congr 2

end Proximity
