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
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.EagerBlocks
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.ReplyLog
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Physical
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Deferred
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.WinningEvent
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Tapes
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Tapes
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.KeySampler
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Counters
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.DeferredLaw
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.CacheOrigins
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.KeyMarginal
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Support

/-!
# Reconstructing a typed winning output and its signing log

The physical replay and the deferred hidden-cell invariant apply to the same winning block.
Together they provide the typed signature and signing log used in the FORS argument.
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

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
set_option maxHeartbeats 180000 in
-- The source settlement retains the real typed replay and all raw signing replies.
/-- A non-aborted winning wire transcript has settled typed replays and undrawn hidden cells. -/
theorem native_nonabort_winning_settled
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) (L R : Nat)
    (block : (List HashOutput × List HashOutput) × NativeTerminal)
    (hblock : block ∈ support
      (NoticingTape.blockRunOf (nativeRun s adv reserve caps fallback) L R))
    (filled : LabState FIPS205.core)
    (hfilled : filled ∈ support (RelabelState.endFill block.2.2.1.1.2.1))
    (secret : Secret) :
    let terminal := block.2
    let G := slhGraph FIPS205.core s
    let E := secretEncoding FIPS205.core (Equiv.refl _) s
    let split := G.toSplitCache filled
    let cache := (E.merge secret split).fst
    terminal.2.2.2 = false → SigningView.Wins id terminal.1.2 →
    ¬G.Conflict filled → ¬(∃ cell, (split.1 (E.enc secret cell)).isSome) →
    let typedLog : QueryLog
        (List Byte →ₒ GeneralScheme.SignatureCore FIPS205.params FIPS205.core) :=
      terminal.1.2.rawLog.filterMap fun entry => do
        let message ← (External.encodePureMessage entry.1.context entry.1.message).toOption
        let wire ← entry.2
        let signature ← (SLHDSA.decodeSignature FIPS205.params
          (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption
        pure ⟨message, signature⟩
    terminal.1.1.1.pkSeed = s ∧
      ∃ (message : List Byte)
        (signature : GeneralScheme.SignatureCore FIPS205.params FIPS205.core),
        (External.encodePureMessage terminal.1.2.forgery.1.context
          terminal.1.2.forgery.1.message).toOption = some message ∧
        (SLHDSA.decodeSignature FIPS205.params
          (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)
          terminal.1.2.forgery.2).toOption = some signature ∧
        let outcome : RomOutcome FIPS205.params FIPS205.core :=
          ⟨terminal.1.1.1, fillSecretKey FIPS205.core secret terminal.1.1.2,
            typedLog, message, signature, true⟩
        let provider := oracleSecret FIPS205.core (Equiv.refl _) s secret.1
        (⟨outcome.msg, outcome.sig⟩ ∉ outcome.log) ∧
          HiddenUndrawn FIPS205.core outcome.pk outcome.log terminal.2.1.1.2.1.1 ∧
          simulateQ cache.toPartialImpl
            (GeneralScheme.keygenInternalWithSecretM FIPS205.core provider
              outcome.pk.pkSeed) = some outcome.pk.pkRoot ∧
          (∀ entry ∈ outcome.log, simulateQ cache.toPartialImpl
            (GeneralScheme.signInternalWithSecretRandomizerM FIPS205.core provider
              entry.1 outcome.pk.pkSeed outcome.pk.pkRoot entry.2.randomness) = some entry.2) ∧
          simulateQ cache.toPartialImpl
            (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core
              outcome.msg outcome.sig outcome.pk) = some true := by
  dsimp only
  intro hnotAborted hwins hnoConflict hnoSecretHit
  let terminal := block.2
  let typedLog : QueryLog
      (List Byte →ₒ GeneralScheme.SignatureCore FIPS205.params FIPS205.core) :=
    terminal.1.2.rawLog.filterMap fun entry => do
      let message ← (External.encodePureMessage entry.1.context entry.1.message).toOption
      let wire ← entry.2
      let signature ← (SLHDSA.decodeSignature FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption
      pure ⟨message, signature⟩
  let project := fun result : NativeTerminal =>
    ((((result.1, (PUnit.unit, result.2.2)), result.2.1.1.1), result.2.1.1.2.2),
      result.2.1.1.2.1)
  have hdeferred : project terminal ∈ support
      ((simulateQ (slhGraph FIPS205.core s).deferredImpl
        (deferredProgram s adv reserve caps fallback)).run ((∅, ∅), [])) := by
    have marginal := native_deferred_marginal s adv reserve caps fallback L R
    dsimp only at marginal
    rw [← support_eq_of_evalDistEq marginal, support_map]
    exact ⟨block, hblock, rfl⟩
  have freshDecoded (message : List Byte)
      (signature : GeneralScheme.SignatureCore FIPS205.params FIPS205.core)
      (framed : (External.encodePureMessage terminal.1.2.forgery.1.context
        terminal.1.2.forgery.1.message).toOption = some message)
      (decoded : (SLHDSA.decodeSignature FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)
        terminal.1.2.forgery.2).toOption = some signature) :
      ⟨message, signature⟩ ∉ typedLog :=
    SLHDSA.SHAKE128s.Settlement.fresh_decoded _ _ _ _ _ framed decoded hwins.2
  have hidden := deferred_nonabort_hidden_log s adv reserve caps fallback
    (project terminal) hdeferred hnotAborted
  have keySeed : terminal.1.1.1.pkSeed = s := hidden.1
  have hiddenLog : HiddenUndrawn FIPS205.core terminal.1.1.1 typedLog
      terminal.2.1.1.2.1.1 := hidden.2
  let G := slhGraph FIPS205.core s
  let E := secretEncoding FIPS205.core (Equiv.refl _) s
  have settled := real_cache_settles_unresolved_source s adv reserve caps secret
  obtain ⟨message, signature, framed, decoded, _seed, rootReplay, logReplay, verifyReplay⟩ :=
    settled ((project terminal).1, E.merge secret (G.toSplitCache filled))
      (by
        have same : (GuardedFill.eraseTapes (block, filled, secret)).1.1 = (project terminal).1 :=
          rfl
        let supported := fun val : GuardedFill.Value =>
          (val, E.merge secret (G.toSplitCache filled)) ∈ support
            ((simulateQ (E.realImpl secret)
              (GuardedFill.freeProgram s adv reserve true caps)).run ∅)
        with_reducible
          exact Eq.mp (congrArg supported same)
            (GuardedFill.realSupport_of_block s adv reserve caps fallback L R block
              hblock filled secret hfilled hnotAborted hnoConflict hnoSecretHit)) hnotAborted hwins
  exact ⟨keySeed, message, signature, framed, decoded,
    freshDecoded message signature framed decoded, hiddenLog,
    rootReplay, logReplay, verifyReplay⟩

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end
