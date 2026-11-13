/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.PRFDerived.Query
public import HashSig.GXMSS.HashInstance
public import VCVio.OracleComp.EvalDist.Measure

/-!
# GXMSS response projection laws

Public-parameter projection uses the actual tweakable-hash seed sampler. Start and retry
projections use their native uniform sampling laws, independently of evaluator-key sampling.
-/

public section
namespace GXMSS.PRFDerived.Unforgeability
open OracleComp OracleSpec ProbabilityTheory MeasureTheory
variable {PP T X H M R Response : Type} {h w v : ℕ}

/-- The distinguished response has exactly the THF public-seed sampling law. -/
@[expose] def PublicSeedSamplingLaw [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) : Prop :=
  letI : MeasurableSpace PP := ⊤
  𝒟[projection.publicParameter <$> ($ᵗ Response)] =
    𝒟[(HashInstance.thf hash).seedGen]

/-- Each distinct chain-start response projects to the canonical uniform start law. -/
@[expose] def ChainStartSamplingLaw [SampleableType Response] [SampleableType H]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) : Prop :=
  letI : MeasurableSpace H := ⊤
  𝒟[projection.chainStart <$> ($ᵗ Response)] = 𝒟[$ᵗ H]

/-- One projected response has exactly the canonical uniform retry-randomizer law. -/
@[expose] def RetrySamplingLaw [SampleableType Response] [SampleableType R]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) : Prop :=
  letI : MeasurableSpace R := ⊤
  𝒟[projection.retryRandomizer <$> ($ᵗ Response)] = 𝒟[$ᵗ R]

end GXMSS.PRFDerived.Unforgeability
