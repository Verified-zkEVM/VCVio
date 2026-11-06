/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.PRFDerivedScheme
import all HashSig.GXMSS.PRFDerivedScheme
public import HashSig.GXMSS.Security.Auxiliary.SigningQueries
import all HashSig.GXMSS.Security.Auxiliary.SigningQueries
public import HashSig.GXMSS.Security.PRFDerived.ResponseCache
import all HashSig.GXMSS.Security.PRFDerived.ResponseCache
public import HashSig.GXMSS.Security.PRFDerived.RetrySampling
import all HashSig.GXMSS.Security.PRFDerived.RetrySampling
public import HashSig.GXMSS.Security.PRFDerived.SigningSimulation
import all HashSig.GXMSS.Security.PRFDerived.SigningSimulation
public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling

/-!
# Complete-tree PRF oracle queries

The named shared PRF and public-seed/start projection laws use the actual hash seed sampler.
Setup queries are parameterized by the complete three-family query domain.
-/

public section

namespace GXMSS.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding ENNReal GXMSS ProbabilityTheory MeasureTheory TweakableHash
open OracleComp.ProgramLogic.Relational
open GXMSS.PRFDerived.ResponseCache GXMSS.PRFDerived.RetrySampling
open GXMSS.PRFDerived.SigningSimulation

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- One keyed PRF supplies every query family through a common abstract response. -/
abbrev SharedPRF (Key PP M Response : Type) (h v : ℕ) :=
  PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response

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

/-- A function-oracle query for the public parameter. -/
@[expose] def publicSeedQuery (projection : GXMSS.PRFDerived.Interpretation PP H R Response) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v)
      Response) PP :=
  projection.publicParameter <$> PRFScheme.functionQuery .publicSeed

/-- A function-oracle query for one start under the derived public parameter. -/
@[expose] def startQuery (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (pp : PP)
    (epoch : Fin (2 ^ h)) (chain : Fin v) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v)
      Response) H :=
  projection.chainStart <$> PRFScheme.functionQuery (.start pp epoch chain)

/-- Read all starts under the parameter obtained from the first query. -/
@[expose] def startQueries
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v)
      Response) (Fin (2 ^ h) → Fin v → H) :=
  (Fin.mOfFn (2 ^ h * v) fun index =>
    startQuery projection pp (Fin.divNat index) (Fin.modNat index)).map
      fun starts epoch chain => starts (finProdFinEquiv (epoch, chain))

end GXMSS.PRFDerived.Unforgeability
