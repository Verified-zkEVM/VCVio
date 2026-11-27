/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.FiredCoverage
public import HashSig.SLHDSA.Security.NativeRelative
public import HashSig.SLHDSA.Security.CoverageRun
public import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings
public import HashSig.SLHDSA.Security.Transport
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
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.WinningOutput
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.RoleInvariant
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.WinningOutput
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.CacheOrigins
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.Program
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coverage.Forgery
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Tapes
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded

/-! # FORS witnesses for successful forgeries with no charged hazard -/

public section

section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open MeasureTheory
open SLHDSA.Security.CanonicalGames SLHDSA.DigestTransport
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
set_option maxHeartbeats 900000 in
-- The descent classifies the same decoded log against the prefill and final merged caches.
/-- Every uncharged original wire winner supplies all FORS leaves on used native tapes. -/
theorem fired_of_uncharged_winner (q : Nat)
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (block : (List HashOutput × List HashOutput) × NativeTerminal)
    (hblock : block ∈ support (NoticingTape.blockRunOf
      (nativeRun s adv true (32 * q - 1, 2 ^ 64) fallback) (2 ^ 64 + 1) (16 * 2 ^ 128)))
    (hS64 : block.2.2.1.2.2.1.cnt .signer ≤ 2 ^ 64)
    (hNfR : block.2.2.1.2.2.1.cnt .forger ≤ 16 * 2 ^ 128)
    (filled : LabState FIPS205.core) (secret : Secret)
    (hfilled : filled ∈ support (RelabelState.endFill block.2.2.1.1.2.1)) :
    let G := slhGraph FIPS205.core s
    let split := G.toSplitCache filled
    let E := secretEncoding FIPS205.core (Equiv.refl _) s
    block.2.2.2.2 = false → SigningView.Wins id block.2.1.2 →
      ¬G.Conflict filled → ¬(slhNodeKeys FIPS205.core s).TCHazard filled →
      ¬(∃ cell, (split.1 (E.enc secret cell)).isSome) →
      FiredCoverage.FiredCovered
        (fun t : NativeTerminal => t.2.1.2.2.1.cnt .forger)
        (fun t index => Coverage.ActualKeyPotential.Fired FIPS205.core t.1.1.1 t.2.1.2 index)
        (block.2.2.1.2.2.1.next .signer) (16 * 2 ^ 128) block := by
  classical
  intro G split E notAborted wins conflict noTC encoded
  let terminal := block.2
  let typed := E.merge secret split
  let hd : FIPS205.core.KeyDiscipline FIPS205.params :=
    Concrete.keyDiscipline_approvedPrimitives .SLHDSA_SHAKE_128s
  have settled := SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.native_nonabort_winning_settled
    s adv true (32 * q - 1, 2 ^ 64) fallback
    (2 ^ 64 + 1) (16 * 2 ^ 128) block hblock filled hfilled secret
  dsimp only at settled
  obtain ⟨seed, message, signature, framed, decoded, fresh,
    hidden, rootReplay, logReplay, verifierReplay⟩ :=
      settled notAborted wins conflict encoded
  have sameSeed : terminal.1.1.1.pkSeed = s := seed
  let typedLog : QueryLog
      (List Byte →ₒ GeneralScheme.SignatureCore FIPS205.params FIPS205.core) :=
    terminal.1.2.rawLog.filterMap fun entry => do
      let message ← (External.encodePureMessage entry.1.context entry.1.message).toOption
      let wire ← entry.2
      let signature ← (SLHDSA.decodeSignature FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption
      pure ⟨message, signature⟩
  let outcome : RomOutcome FIPS205.params FIPS205.core :=
    ⟨terminal.1.1.1, fillSecretKey FIPS205.core secret terminal.1.1.2,
      typedLog, message, signature, true⟩
  let provider : Adrs → OracleComp (publicHashSpec FIPS205.core) FIPS205.core.Y :=
    oracleSecret FIPS205.core (Equiv.refl _) s secret.1
  have classified := bad_event_or_logged_of_settled
    (core := FIPS205.core) (Concrete.shakePrimitives_byteLaws FIPS205.params.params)
    provider outcome typed.fst rootReplay logReplay verifierReplay
  rcases classified with targetCollision | hiddenHit | coverage | logged
  · let deriveOutcome : DeriveOutcome FIPS205.core :=
      ⟨terminal.1.1.1, terminal.1.1.2, typedLog, message, signature, true⟩
    have targetRun : RunTargetCollision FIPS205.core (Equiv.refl _)
        (DeriveOutcome.fill FIPS205.core secret deriveOutcome, typed) := by
      simp only [RunTargetCollision, DeriveOutcome.fill_pk,
        DeriveOutcome.fill_sk_skSeed, deriveOutcome]
      rw [sameSeed]
      change TargetCollision provider terminal.1.1.1.pkSeed typed.fst at targetCollision
      rwa [sameSeed] at targetCollision
    exact (noTC (tcHazard_of_runTargetCollision_fill
      (pkSeed := s) (s := secret) (st := filled) hd seed targetRun)).elim
  · have leFill := RelabelState.le_of_mem_support_endFill hfilled
    have publicSame := RelabelState.fst_eq_of_mem_support_endFill hfilled
    have prefillGood : ¬G.Conflict terminal.2.1.1.2.1.1 := by
      intro bad
      exact conflict (CanonicalGraph.Conflict.mono G leFill bad)
    have noPublicEncoded : ¬∃ cell,
        (filled.1 (E.enc secret cell)).isSome :=
      ((exists_isSome_toSplitCache_fst_secretEncoding_enc_iff
        (e := Equiv.refl _) (pkSeed := s) (s := secret) (st := filled)
        hd.keySeparated).not).1 encoded
    have noPrefillEncoded : ¬∃ cell,
        (terminal.2.1.1.2.1.1.1 (E.enc secret cell)).isSome := by
      simpa only [publicSame] using noPublicEncoded
    let project := fun t : NativeTerminal =>
      ((((t.1, (PUnit.unit, t.2.2)), t.2.1.1.1), t.2.1.1.2.2), t.2.1.1.2.1)
    have deferredSupport : project terminal ∈ support
        ((simulateQ G.deferredImpl
          (deferredProgram s adv true (32 * q - 1, 2 ^ 64) fallback)).run
            ((∅, ∅), [])) := by
      have marginal := native_deferred_marginal s adv true
        (32 * q - 1, 2 ^ 64) fallback (2 ^ 64 + 1) (16 * 2 ^ 128)
      dsimp only at marginal
      rw [← support_eq_of_evalDistEq marginal, support_map]
      exact ⟨block, hblock, rfl⟩
    have prefillCore :=
      SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.deferred_nonabort_hidden_log_and_verify
      s adv true (32 * q - 1, 2 ^ 64) fallback (project terminal)
      deferredSupport notAborted
    dsimp only at prefillCore
    have prefillReplay := prefillCore.2.2 secret prefillGood noPrefillEncoded
      message signature framed decoded
    have verifierTrue : simulateQ
        ((E.merge secret (G.toSplitCache terminal.2.1.1.2.1.1)).fst).toPartialImpl
        (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core
          message signature terminal.1.1.1) = some true := by
      exact prefillReplay.trans (congrArg some wins.1)
    have actualHit : HiddenHit
        (oracleSecret FIPS205.core (Equiv.refl _)
          outcome.pk.pkSeed outcome.sk.skSeed) outcome typed.fst := by
      change HiddenHit (oracleSecret FIPS205.core (Equiv.refl _) terminal.1.1.1.pkSeed
        secret.1) outcome typed.fst
      rw [sameSeed]
      exact hiddenHit
    apply False.elim
    apply conflict
    apply conflict_of_hiddenHit (core := FIPS205.core) (vp := FIPS205.params)
      (e := Equiv.refl _) (pkSeed := s) (s := secret)
      (st₀ := terminal.2.1.1.2.1.1) (st := filled) hd leFill publicSame
      (o := outcome) (b := true) sameSeed rfl hidden verifierTrue
    with_reducible exact actualHit
  · have fired := native_fired_coverage_of_itsr_of_count_bounds
      q s adv fallback block hblock hS64 hNfR filled hfilled secret message signature
    dsimp only at fired
    exact fired notAborted coverage
  · exact (fresh logged).elim
end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
end
