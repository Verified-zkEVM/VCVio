/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.Schnorr.AGM.Probability
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.Reduction

/-! # Schnorr signing-simulation bounds

Erasure preserves the explicit signing and hash budgets. Perfect Schnorr HVZK and uniform
simulator commitments instantiate the existing Fiat-Shamir signing-simulation comparison
with loss `qS * (qS + qH) / |F|`. This comparison retains the existing signature game's
freshness condition.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction DiffieHellman
open scoped ENNReal

namespace Schnorr.AGM.Reduction

/-- Select signing requests for the explicit signing-query budget. -/
@[expose] def signRequest {F M G : Type} (q : Explained F (Request M) (Group G)) : Bool :=
  match q.value.data with | .sign _ => true | _ => false

end Schnorr.AGM.Reduction

namespace Schnorr

/-- Erasing explanations forwards exactly the counted signing and hash requests. -/
theorem AlgebraicAdversary.toUnforgeableAdversary_queryBound {F G M : Type}
    [Field F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G]
    [SampleableType G] [DecidableEq M] (A : AlgebraicAdversary F G M) (g pk : G)
    (qS qH : ℕ)
    (hS : IsQueryBoundP (A.main (AGM.initial g pk))
      (fun q => AGM.Reduction.signRequest q = true) qS)
    (hH : IsQueryBoundP (A.main (AGM.initial g pk))
      (fun q => AGM.Reduction.hashRequest q = true) qH) :
    FiatShamir.signHashQueryBound (M := M) (oa := (A.toUnforgeableAdversary g).main pk) qS qH := by
  constructor
  · apply (isQueryBoundP_map_iff _ _ _).mpr
    refine hS.simulateQ_of_step ?_ ?_
    · rintro ⟨⟨q, groups⟩, coeff⟩ hq
      cases q <;> simp_all [AGM.Reduction.signRequest, AGM.oracle]
    · rintro ⟨⟨q, groups⟩, coeff⟩ hq
      cases q <;> simp_all [AGM.Reduction.signRequest, AGM.oracle,
        isQueryBoundP_query_bind_iff, isQueryBoundP_pure]
  · apply (isQueryBoundP_map_iff _ _ _).mpr
    refine hH.simulateQ_of_step ?_ ?_
    · rintro ⟨⟨q, groups⟩, coeff⟩ hq
      cases q <;> simp_all [AGM.Reduction.hashRequest, AGM.oracle,
        isQueryBoundP_query_bind_iff, isQueryBoundP_pure]
    · rintro ⟨⟨q, groups⟩, coeff⟩ hq
      cases q <;> simp_all [AGM.Reduction.hashRequest, AGM.oracle]

/-- The original Schnorr EUF-CMA advantage is bounded by the existing freshness-preserving
Fiat-Shamir signing simulation and the standard programming-collision loss. -/
theorem unforgeableAdvantage_le_simulatedCma {F G M : Type}
    [Field F] [SampleableType F] [Fintype F]
    [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G] [DecidableEq M]
    (g : G) (hg : Function.Bijective (fun x : F => x • g))
    (A : AlgebraicAdversary F G M) (qS qH : ℕ)
    (hS : ∀ pk, IsQueryBoundP (A.main (AGM.initial g pk))
      (fun q => AGM.Reduction.signRequest q = true) qS)
    (hH : ∀ pk, IsQueryBoundP (A.main (AGM.initial g pk))
      (fun q => AGM.Reduction.hashRequest q = true) qH) :
    SignatureAlg.unforgeableAdvantage (FiatShamir.runtime (Commit := G) (Chal := F) M)
        (A.toUnforgeableAdversary g) ≤
      Pr{let b ← (FiatShamir.Stateful.cmaSim M G F (dlogGenerable F g)
          (simTranscript F G g)).runProb (FiatShamir.Stateful.cmaInit M G F G F)
          (FiatShamir.Stateful.signedFreshAdv (sigma F G g) (dlogGenerable F g) M
            (A.toUnforgeableAdversary g))}[b = true] +
        (qS : ℝ≥0∞) * (qS + qH) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  classical
  have hQ := fun pk => A.toUnforgeableAdversary_queryBound g pk qS qH (hS pk) (hH pk)
  have hc := FiatShamir.Stateful.signedFreshAdv_H3_bound
    (sigma F G g) (dlogGenerable F g) M (A.toUnforgeableAdversary g)
    (simTranscript F G g) 0 (Fintype.card F : ℝ≥0∞)⁻¹
    ((ChallengeVerifyProtocol.perfectHVZK_iff_hvzk_zero _ _).mp (sigma_hvzk F G g))
    (sigma_simCommitPredictability F G g hg) qS qH hQ
  have he := (FiatShamir.Stateful.unforgeableAdvantage_eq_statefulPostKeygenFreshAdvantage
    (sigma F G g) (dlogGenerable F g) M (A.toUnforgeableAdversary g)).trans
    (FiatShamir.Stateful.statefulPostKeygenFreshAdvantage_eq_cmaRealRunProb_signedFreshAdv
      (sigma F G g) (dlogGenerable F g) M (A.toUnforgeableAdversary g))
  erw [he, prEvent_eq_evalDist_singleton]
  exact (MeasureTheory.Measure.apply_true_le_add_boolDist _ _).trans
    (add_le_add le_rfl (by simpa only [FiatShamir.Stateful.cmaH3Advantage,
      QueryImpl.Stateful.advantage, mul_zero, zero_add] using hc))

end Schnorr

namespace Schnorr.AGM

open FiatShamir FiatShamir.Stateful

private theorem simulatedCma_eq_normalForm {F G M : Type}
    [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    [DecidableEq G] [SampleableType G] [DecidableEq M]
    (g : G) (A : Schnorr.AlgebraicAdversary F G M) :
    (cmaSim M G F (dlogGenerable F g) (Schnorr.simTranscript F G g)).runProb
      (cmaInit M G F G F)
      (signedFreshAdv (Schnorr.sigma F G g) (dlogGenerable F g) M
        (A.toUnforgeableAdversary g)) = (do
      let x ← $ᵗ F
      let p ← (simulateQ
        (simulatedNmaLoggedProbImpl (M := M) (Commit := G) (Chal := F)
          (Resp := F) (Schnorr.simTranscript F G g) (x • g))
        ((A.toUnforgeableAdversary g).main (x • g))).run (∅, [])
      simLoggedVerifyFreshComp (M := M) (Schnorr.sigma F G g) (x • g) p.1 p.2) := by
  erw [cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma,
    nma_runProb_shiftLeft_signedFreshAdv_eq_forkH5Body]
  simp only [forkH5Body, simulateQ_bind]
  have hk : simulateQ (forkWrappedUniformImpl F)
      (liftComp (dlogGenerable F g).gen (Fork.wrappedSpec F)) = (dlogGenerable F g).gen := by
    simpa [forkWrappedUniformImpl] using QueryImpl.simulateQ_liftComp_left_eq_of_apply
      (impl := forkWrappedUniformImpl F) (impl₁ := QueryImpl.id' unifSpec)
      (h := fun _ => rfl) (oa := (dlogGenerable F g).gen)
  rw [hk]
  simp only [dlogGenerable, bind_assoc, pure_bind]
  apply bind_congr
  intro x
  rw [forkLoggedProbImpl_run]
  exact forkLoggedProbImpl_run_bind_verify_eq_simulatedNma_aux (M := M)
    (Schnorr.sigma F G g) (Schnorr.simTranscript F G g) (x • g)
    ((A.toUnforgeableAdversary g).main (x • g))

end Schnorr.AGM
