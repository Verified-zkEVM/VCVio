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
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Eager
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Relabel
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Support
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Support

/-!
# Eager support of a terminal block and its oracle cache

Outside a graph conflict or public query to an encoded secret point, a completed block
can be replayed with the same output in the original fixed-secret program.
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

/-- A supported nonaborted, nonconflicting native block with a final fill lifts to the
original program at a fixed private secret whenever that secret was never queried publicly. -/
theorem realSupport_of_block
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) (L R : Nat)
    (block : (List HashOutput × List HashOutput) × Native.NativeTerminal)
    (hblock : block ∈ support (NoticingTape.blockRunOf
      (Native.nativeRun s adv reserve caps fallback) L R))
    (filled : LabState FIPS205.core) (secret : Secret)
    (hfilled : filled ∈ support (RelabelState.endFill block.2.2.1.1.2.1))
    (nb : block.2.2.2.2 = false)
    (hnoConflict : ¬(slhGraph FIPS205.core s).Conflict filled)
    (hnoSecretHit : ¬∃ x, (((slhGraph FIPS205.core s).toSplitCache filled).1
      ((secretEncoding FIPS205.core (Equiv.refl _) s).enc secret x)).isSome) :
    let val := (eraseTapes (block, filled, secret)).1.1
    let G := slhGraph FIPS205.core s
    let E := secretEncoding FIPS205.core (Equiv.refl _) s
    (val, E.merge secret (G.toSplitCache filled)) ∈ support
      ((simulateQ (E.realImpl secret) (freeProgram s adv reserve true caps)).run ∅) := by
  dsimp only [eraseTapes]
  let val : Value := (((block.2.1, (PUnit.unit, block.2.2.2)), block.2.2.1.1.1),
    block.2.2.1.1.2.2)
  with_reducible
    exact realSupport_of_eager_lab s (freeProgram s adv reserve true caps)
      (labProgram s adv reserve true caps fallback)
      (Native.deferredProgram s adv reserve caps fallback)
      val filled secret nb (labProgram_eq_native s adv reserve caps fallback)
      (eager_joint s adv reserve true caps fallback)
      (Native.filled_native_mem_support_eager s adv reserve caps fallback L R block hblock
        filled hfilled hnoConflict) hnoConflict hnoSecretHit

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill
end
