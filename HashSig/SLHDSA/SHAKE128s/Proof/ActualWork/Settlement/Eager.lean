/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings
import HashSig.SLHDSA.Security.Transport
import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
import VCVio.OracleComp.SimSemantics.WriterT.Core
import all HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Pure
import all HashSig.SLHDSA.Security.CoverageRun
import all HashSig.SLHDSA.Security.NativeCounts
import all HashSig.SLHDSA.Security.NativeRelative
import all HashSig.SLHDSA.Security.SeedCoupling
import all VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.WinningEvent
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Tapes
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Tapes
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.KeySampler
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Counters
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.DeferredLaw
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.CacheOrigins
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.KeyMarginal
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Relabel
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Support
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Support

/-!
# Recovering eager executions from completed guarded runs

On a surviving eager run with no graph conflict or public hit on an encoded secret point,
equality of observations recovers support for the fixed secret.
-/

public section

section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open MeasureTheory
open SLHDSA.Security.CanonicalGames SLHDSA.DigestTransport
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill

/-- Transfer a supported nonaborted marked result through the eager observation equality. -/
theorem realSupport_of_eager_lab (s : FIPS205.core.PkSeed)
    (free : OracleComp (deriveSpec FIPS205.core) Value) (lab checked : OracleComp Lab Value)
    (val : Value) (filled : LabState FIPS205.core) (secret : Secret)
    (nb : val.1.1.2.2.2 = false) (sameLab : lab = checked)
    (sameObs : ∀ event : Observation → LabState FIPS205.core → Prop,
      Pr{let x ← (simulateQ (slhGraph FIPS205.core s).eagerImpl
        (liftComp free Lab)).run (∅, ∅)}[event (observe x.1) x.2] =
      Pr{let x ← (simulateQ (slhGraph FIPS205.core s).eagerImpl
        lab).run (∅, ∅)}[event (observe x.1) x.2])
    (hchecked : (val, filled) ∈ support
      ((simulateQ (slhGraph FIPS205.core s).eagerImpl checked).run (∅, ∅)))
    (hc : ¬(slhGraph FIPS205.core s).Conflict filled)
    (hh : ¬∃ x, (((slhGraph FIPS205.core s).toSplitCache filled).1
      ((secretEncoding FIPS205.core (Equiv.refl _) s).enc secret x)).isSome) :
    (val, (secretEncoding FIPS205.core (Equiv.refl _) s).merge secret
      ((slhGraph FIPS205.core s).toSplitCache filled)) ∈ support
      ((simulateQ ((secretEncoding FIPS205.core (Equiv.refl _) s).realImpl secret) free).run
        ∅) := by
  subst checked
  apply realSupport_of_relabel s free val filled secret _ hc hh
  rw [← (slhGraph FIPS205.core s).simulateQ_eagerImpl_liftComp]
  exact mem_of_observed sameObs val filled nb hchecked

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill
end
