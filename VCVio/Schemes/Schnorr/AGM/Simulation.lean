/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.Schnorr.AGM.Probability
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.Reduction

/-! # Schnorr signing-simulation bounds

Erasure preserves the explicit signing and hash budgets. Perfect Schnorr HVZK and uniform
simulator commitments instantiate the existing Fiat-Shamir signing-simulation comparison
with loss `qS * (qS + qH) / |F|`. This comparison retains the existing signature game's
freshness condition.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction DiffieHellman
open scoped ENNReal

namespace Schnorr

/-- Erasing explanations forwards exactly the counted signing and hash requests. -/
theorem AlgebraicAdversary.toUnforgeableAdversary_queryBound {F G M : Type}
    [Field F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G]
    [SampleableType G] [DecidableEq M] (A : AlgebraicAdversary F G M) (g pk : G)
    (qS qH : ℕ)
    (hS : IsQueryBoundP (A.main (AGM.initial g pk))
      (fun q => AGM.signRequest q = true) qS)
    (hH : IsQueryBoundP (A.main (AGM.initial g pk))
      (fun q => AGM.hashRequest q = true) qH) :
    FiatShamir.signHashQueryBound (M := M) (oa := (A.toUnforgeableAdversary g).main pk) qS qH := by
  constructor
  · apply (isQueryBoundP_map_iff _ _ _).mpr
    refine hS.simulateQ_of_step ?_ ?_
    · rintro ⟨⟨q, groups⟩, coeff⟩ hq
      cases q <;> simp_all [AGM.signRequest, AGM.oracle]
    · rintro ⟨⟨q, groups⟩, coeff⟩ hq
      cases q <;> simp_all [AGM.signRequest, AGM.oracle,
        isQueryBoundP_query_bind_iff, isQueryBoundP_pure]
  · apply (isQueryBoundP_map_iff _ _ _).mpr
    refine hH.simulateQ_of_step ?_ ?_
    · rintro ⟨⟨q, groups⟩, coeff⟩ hq
      cases q <;> simp_all [AGM.hashRequest, AGM.oracle,
        isQueryBoundP_query_bind_iff, isQueryBoundP_pure]
    · rintro ⟨⟨q, groups⟩, coeff⟩ hq
      cases q <;> simp_all [AGM.hashRequest, AGM.oracle]

/-- The original Schnorr EUF-CMA advantage is bounded by the existing freshness-preserving
Fiat-Shamir signing simulation and the standard programming-collision loss. -/
theorem unforgeableAdvantage_le_simulatedCma {F G M : Type}
    [Field F] [SampleableType F] [Fintype F]
    [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G] [DecidableEq M]
    (g : G) (hg : Function.Bijective (fun x : F => x • g))
    (A : AlgebraicAdversary F G M) (qS qH : ℕ)
    (hS : ∀ pk, IsQueryBoundP (A.main (AGM.initial g pk))
      (fun q => AGM.signRequest q = true) qS)
    (hH : ∀ pk, IsQueryBoundP (A.main (AGM.initial g pk))
      (fun q => AGM.hashRequest q = true) qH) :
    SignatureAlg.unforgeableAdvantage (FiatShamir.runtime (Commit := G) (Chal := F) M)
        (A.toUnforgeableAdversary g) ≤
      Pr{let b ← (FiatShamir.Stateful.cmaSim M G F (dlogGenerable F g)
          (simTranscript F G g)).runProb (FiatShamir.Stateful.cmaInit M G F G F)
          (FiatShamir.Stateful.signedFreshAdv (sigma F G g) (dlogGenerable F g) M
            (A.toUnforgeableAdversary g))}[b = true] +
        (qS : ℝ≥0∞) * (qS + qH) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have hQ := fun pk => A.toUnforgeableAdversary_queryBound g pk qS qH (hS pk) (hH pk)
  have h := FiatShamir.unforgeableAdvantage_le_cmaSim_add
    (sigma F G g) (dlogGenerable F g) M (simTranscript F G g) 0
    ((ChallengeVerifyProtocol.perfectHVZK_iff_hvzk_zero _ _).mp (sigma_hvzk F G g))
    (Fintype.card F : ℝ≥0∞)⁻¹ (sigma_simCommitPredictability F G g hg)
    (A.toUnforgeableAdversary g) qS qH hQ
  simp only [mul_zero, zero_add] at h
  exact h

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
  exact (cmaSim_runProb_signedFreshAdv_eq (σ := Schnorr.sigma F G g) (hr := dlogGenerable F g)
    (M := M) (A.toUnforgeableAdversary g) (Schnorr.simTranscript F G g)).trans
    (by simp [dlogGenerable])

end Schnorr.AGM
