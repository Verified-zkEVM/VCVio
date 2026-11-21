/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.PRFDerivedUnforgeability
public import HashSigTest.GXMSS.ActiveSecurity

/-!
# Empty-frontier projection controls

The filler projection is deliberately nonuniform. Full-range interval idealization uses only the
three queried complete projections; native transport to a three-family PRF domain is separate.
-/

public section
namespace GXMSS.PRFIdealizationProbe
open OracleComp OracleSpec GXMSS.IntervalMerkle
open GXMSS.Interval.PRFDerived.Unforgeability

/-- Uniform Boolean starts, unit seed/retry projections and a constant false filler. -/
@[expose] def projection : GXMSS.Interval.PRFDerived.Interpretation Unit Bool Unit Bool where
  publicParameter := fun _ => ()
  chainStart := id
  retryRandomizer := fun _ => ()
  fillerDigest := fun _ => false

/-- The actual seed sampler is the unit projection. -/
theorem seed_law : PublicSeedSamplingLaw ActiveSecurityProbe.hash projection := by
  simp [PublicSeedSamplingLaw, GXMSS.PRFDerived.Unforgeability.PublicSeedSamplingLaw,
    projection, ActiveSecurityProbe.hash]

/-- The queried start projection has exactly the native Boolean law. -/
theorem start_law : ChainStartSamplingLaw projection := by
  simp [ChainStartSamplingLaw, GXMSS.PRFDerived.Unforgeability.ChainStartSamplingLaw, projection]

/-- Unit retries have the native unit law. -/
theorem retry_law : RetrySamplingLaw projection := by
  let : MeasurableSpace Unit := ⊤
  have hu : 𝒟[$ᵗ Unit] = MeasureTheory.Measure.dirac () := by
    apply MeasureTheory.Measure.ext_of_singleton
    rintro ⟨⟩
    simp
  simpa [RetrySamplingLaw, GXMSS.PRFDerived.Unforgeability.RetrySamplingLaw, projection]
    using hu.symm

/-- The omitted global filler law is actually false in this fixture. -/
theorem no_global_filler : ¬ FillerSamplingLaw projection := by
  intro h
  let : MeasurableSpace Bool := ⊤
  change 𝒟[(fun _ : Bool => false) <$> ($ᵗ Bool)] = 𝒟[$ᵗ Bool] at h
  have htrue := congrArg (fun μ : MeasureTheory.Measure Bool => μ {true}) h
  norm_num at htrue
  have hn : (2 : ENNReal)⁻¹ ≠ 0 := by simp
  exact hn htrue.symm

/-- The full interval imposes no law at an unqueried filler coordinate. -/
theorem used_filler : UsedFillerSamplingLaw (Interval.full 0) projection :=
  usedFillerSamplingLaw_full projection

/-- Actual full-interaction idealization applies despite the false global filler premise. -/
theorem native_interaction [DecidableEq (GXMSS.Interval.PRFDerived.Query Unit Unit 0 1)] :
    IdealInteractionCorrespondence ActiveSecurityProbe.hash ActiveSecurityProbe.encoding
      projection 1 (Interval.full 0) ActiveSecurityProbe.adversary := by
  exact ideal_interaction_correspondence_of_used_frontier ActiveSecurityProbe.hash
    ActiveSecurityProbe.encoding projection 1 (Interval.full 0) ActiveSecurityProbe.adversary
    seed_law start_law retry_law used_filler

/-- The whole returned strong-game measure also needs no global filler law at full range. -/
theorem native_strong_measure [DecidableEq (GXMSS.Interval.PRFDerived.Query Unit Unit 0 1)] :
    𝒟[PRFScheme.prfIdealExperiment (randgenPRFReduction ActiveSecurityProbe.hash
      ActiveSecurityProbe.encoding projection 1 (Interval.full 0) ActiveSecurityProbe.adversary)] =
      SyncSignatureUnforgeability.strongUnforgeableExp
        (GXMSS.Interval.scheme ActiveSecurityProbe.hash ActiveSecurityProbe.encoding
          1 (Interval.full 0)) ProbCompRuntime.probComp ActiveSecurityProbe.adversary := by
  exact ideal_adaptive_strong_correspondence_of_used_frontier ActiveSecurityProbe.hash
    ActiveSecurityProbe.encoding projection 1 (Interval.full 0) ActiveSecurityProbe.adversary
    seed_law start_law retry_law used_filler

end GXMSS.PRFIdealizationProbe
