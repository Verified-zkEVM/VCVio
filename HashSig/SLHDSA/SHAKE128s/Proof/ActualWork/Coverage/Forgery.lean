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
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coverage.ExpectedCredit
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coverage.DigestMirror
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.RoleInvariant
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.CacheOrigins
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.Program

/-!
# FORS coverage witnessed by a cached typed forgery

A cached typed forgery with a fresh covered digest identifies a consumed forger position. The
bound uses the signing and forgery counts of that run.
-/

public section

section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open MeasureTheory
open SLHDSA.Security.CanonicalGames SLHDSA.DigestTransport
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
/-- A fresh covered forgery on a nonaborted run reaches a fired forger slot within the signer and
forger count bounds. -/
theorem native_fired_coverage_of_itsr_of_count_bounds
    (q : Nat)
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (block : (List HashOutput × List HashOutput) × NativeTerminal)
    (hblock : block ∈ support (NoticingTape.blockRunOf
      (nativeRun s adv true (32 * q - 1, 2 ^ 64) fallback)
      (2 ^ 64 + 1) (16 * 2 ^ 128)))
    (hS64 : block.2.2.1.2.2.1.cnt .signer ≤ 2 ^ 64)
    (hNfR : block.2.2.1.2.2.1.cnt .forger ≤ 16 * 2 ^ 128)
    (filled : LabState FIPS205.core)
    (hfilled : filled ∈ support (RelabelState.endFill block.2.2.1.1.2.1))
    (secret : Secret) (message : List Byte)
    (signature : GeneralScheme.SignatureCore FIPS205.params FIPS205.core) :
    let terminal := block.2
    let G := slhGraph FIPS205.core s
    let E := secretEncoding FIPS205.core (Equiv.refl _) s
    let cache := (E.merge secret (G.toSplitCache filled)).fst
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
    terminal.2.2.2 = false →
    (ItsrCovered outcome cache ∧
      (signature.randomness, message) ∉ typedLog.map
        (fun entry => (entry.2.randomness, entry.1))) →
    FiredCoverage.FiredCovered
      (fun result : NativeTerminal => result.2.1.2.2.1.cnt .forger)
      (fun result index => Coverage.ActualKeyPotential.Fired FIPS205.core
        result.1.1.1 result.2.1.2 index)
      (terminal.2.1.2.2.1.next .signer) (16 * 2 ^ 128) block := by
  classical
  dsimp only
  intro hnotAborted hcoverage
  have hterminal : block.2 ∈ support
      (nativeRun s adv true (32 * q - 1, 2 ^ 64) fallback block.1.1 block.1.2) :=
    (NoticingTape.mem_support_blockRunOf
      (nativeRun s adv true (32 * q - 1, 2 ^ 64) fallback)
      (2 ^ 64 + 1) (16 * 2 ^ 128) block hblock).2.2
  have actualTerminalSupport := hterminal
  simp only [nativeRun, bind_pure_comp, support_map] at hterminal
  obtain ⟨nested, hnested, hterminalEq⟩ := hterminal
  let tapes : (which : Coverage.TapeClass) →
      List (Coverage.tapeClassRange FIPS205.core which)
    | .signer => block.1.1.map Bridge.answerEquiv
    | .forger => block.1.2.map Bridge.answerEquiv
    | .other => []
  let program := (simulateQ
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
    (guardedRoutedSource s adv true (32 * q - 1, 2 ^ 64) fallback)).run
      (((∅, ∅), []), (0, SigningView.Phase.keygen))
  let initial : Coverage.RoleState FIPS205.core :=
    ((∅, tapes), (AnswerTape.ClassPos.init, ∅))
  change nested ∈ support
    ((simulateQ (Coverage.roleRunImpl FIPS205.core) program).run initial) at hnested
  have hinitial : AnswerTape.HitInv (Coverage.tapeClass FIPS205.core) tapes initial :=
    ⟨AnswerTape.ClassPosInv.empty (Coverage.tapeClass FIPS205.core) tapes,
      fun _ hit => hit.elim⟩
  have hhit : AnswerTape.HitInv (Coverage.tapeClass FIPS205.core) tapes nested.2 := by
    refine simulateQ_run_preserves_inv_of_query (Coverage.roleRunImpl FIPS205.core)
      (AnswerTape.HitInv (Coverage.tapeClass FIPS205.core) tapes) ?_
      program initial hinitial nested hnested
    intro input before hbefore after hafter
    exact AnswerTape.hitInv_of_mem_support_classPosImplFwd_run
      (Coverage.IsRandPoint FIPS205.core) (Coverage.randRel FIPS205.core)
      (Coverage.tapeClass FIPS205.core) (Coverage.range_eq_tapeClassRange FIPS205.core)
      hbefore hafter
  have actualHit : AnswerTape.HitInv (Coverage.tapeClass FIPS205.core) tapes
      block.2.2.1.2 := by
    rw [← hterminalEq]
    exact hhit
  let initialState : CoverageDeferred.S FIPS205.core :=
    (((∅, ∅), []), (0, SigningView.Phase.keygen))
  let linked := QueryImpl.Stateful.link
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
    (Coverage.roleRunImpl FIPS205.core)
  have hlinked : (nested.1.1, (nested.1.2, nested.2)) ∈ support
      ((simulateQ linked
        (guardedRoutedSource s adv true (32 * q - 1, 2 ^ 64) fallback)).run
          (initialState, initial)) := by
    rw [QueryImpl.Stateful.simulateQ_link_run, support_map]
    refine ⟨nested, ?_, ?_⟩
    · simpa only [program, initialState] using hnested
    · simp only [QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
        PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put]
  have nestedMirror : CoverageDeferred.PartialHmsgMirror FIPS205.core
      (nested.1.2, nested.2) :=
    CoverageDeferred.PartialHmsgMirror.of_mem_support_run FIPS205.core s (metadataCost true s)
      (guardedRoutedSource s adv true (32 * q - 1, 2 ^ 64) fallback)
      (initialState, initial) (nested.1.1, (nested.1.2, nested.2))
      (CoverageDeferred.PartialHmsgMirror.init FIPS205.core tapes) hlinked
  have actualMirror : CoverageDeferred.PartialHmsgMirror FIPS205.core
      (block.2.2.1.1.2, block.2.2.1.2) := by
    rw [← hterminalEq]
    exact nestedMirror
  have publicFilledMirror := CoverageDeferred.PartialHmsgMirror.endFill FIPS205.core
    (block.2.2.1.1.2, block.2.2.1.2) filled actualMirror hfilled
  have filledMirror (r : FIPS205.core.Y) (seed : FIPS205.core.PkSeed)
      (root : FIPS205.core.Y) (message : List Byte) :
      ((secretEncoding FIPS205.core (Equiv.refl _) s).merge secret
        ((slhGraph FIPS205.core s).toSplitCache filled)).fst
          (.hmsg r seed root message) =
        block.2.2.1.2.1.1 (.inl (.inl (.hmsg r seed root message))) := by
    exact (merge_fst_hmsg (e := Equiv.refl _) (pkSeed := s) (s := secret) (st := filled)
      r seed root message).trans (publicFilledMirror r seed root message)
  let terminal := block.2
  let pk := terminal.1.1.1
  let typedLog : QueryLog
      (List Byte →ₒ GeneralScheme.SignatureCore FIPS205.params FIPS205.core) :=
    terminal.1.2.rawLog.filterMap fun entry => do
      let message ← (External.encodePureMessage entry.1.context entry.1.message).toOption
      let wire ← entry.2
      let signature ← (SLHDSA.decodeSignature FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption
      pure ⟨message, signature⟩
  have runInv : Coverage.RunInv FIPS205.core pk typedLog terminal.2.1.2 :=
    native_nonabort_terminal_runInv s adv true (32 * q - 1, 2 ^ 64) fallback
      block.1.1 block.1.2 terminal actualTerminalSupport hnotAborted
  have blockLengths := NoticingTape.mem_support_blockRunOf
    (nativeRun s adv true (32 * q - 1, 2 ^ 64) fallback)
    (2 ^ 64 + 1) (16 * 2 ^ 128) block hblock
  have hleftLength : block.1.1.length = 2 ^ 64 + 1 :=
    DigestTape.padding_length _ _ blockLengths.1
  have hrightLength : block.1.2.length = 16 * 2 ^ 128 :=
    DigestTape.padding_length _ _ blockLengths.2.1
  let outcome : RomOutcome FIPS205.params FIPS205.core :=
    ⟨pk, fillSecretKey FIPS205.core secret terminal.1.1.2,
      typedLog, message, signature, true⟩
  have roleCoverage : ItsrCovered outcome terminal.2.1.2.1.1.fst.fst := by
    obtain ⟨digest, hdigest, covered⟩ := hcoverage.1
    refine ⟨digest, ?_, ?_⟩
    · change _ = some digest at hdigest
      change terminal.2.1.2.1.1
        (.inl (.inl (.hmsg signature.randomness pk.pkSeed pk.pkRoot message))) = some digest
      exact (filledMirror signature.randomness pk.pkSeed pk.pkRoot message).symm.trans hdigest
    · intro coordinate hcoordinate
      obtain ⟨entry, hentry, coverDigest, hlogged, hmatch⟩ := covered coordinate hcoordinate
      refine ⟨entry, hentry, coverDigest, ?_, hmatch⟩
      change _ = some coverDigest at hlogged
      change terminal.2.1.2.1.1
        (.inl (.inl (.hmsg entry.2.randomness pk.pkSeed pk.pkRoot entry.1))) = some coverDigest
      exact (filledMirror entry.2.randomness pk.pkSeed pk.pkRoot entry.1).symm.trans hlogged
  obtain ⟨targetIndex, digest, targetLength, _targetNext, targetReached,
      _targetClass, _targetPosition, targetValue, _targetDigest, coverers⟩ :=
    Coverage.exists_coverage_positions_of_runInv_classPosInv FIPS205.core outcome tapes
      terminal.2.1.2 runInv actualHit.1
      (by simpa only [tapes, List.length_map, hrightLength] using hNfR)
      (by simpa only [tapes, List.length_map, hleftLength] using hS64.trans (Nat.le_succ _))
      roleCoverage hcoverage.2
  have originalValue (tape : List HashOutput) (index : Nat) (value : FIPS205.Answer)
      (hvalue : (tape.map Bridge.answerEquiv)[index]? = some value) :
      ∃ answer, tape[index]? = some answer ∧ Bridge.answerEquiv answer = value := by
    rw [List.getElem?_map] at hvalue
    exact Option.map_eq_some_iff.mp hvalue
  obtain ⟨targetAnswer, targetCell, targetAnswerEq⟩ :=
    originalValue block.1.2 targetIndex digest (by simpa only [tapes] using targetValue)
  have supplies (tape : List HashOutput) (index : Nat) (answer : HashOutput)
      (value : FIPS205.Answer) (tree : ForsCoverage.Tree)
      (hcell : tape[index]? = some answer) (hanswer : Bridge.answerEquiv answer = value)
      (hinstance : (DigestTransport.coveringDigest FIPS205.params value).1 =
        (DigestTransport.coveringDigest FIPS205.params digest).1)
      (hleaf : (DigestTransport.coveringDigest FIPS205.params value).2 tree =
        (DigestTransport.coveringDigest FIPS205.params digest).2 tree) :
      FiredCoverage.Supplies (FiredCoverage.cellView tape index)
        (FiredCoverage.cellView block.1.2 targetIndex) tree := by
    rw [← hanswer, ← targetAnswerEq] at hinstance hleaf
    obtain ⟨htree, hposition⟩ :=
      (DigestTransport.coveringDigest_fst_eq_iff FIPS205.params _ _).1 hinstance
    have htreeBits : MessageDigest.treeIndex answer = MessageDigest.treeIndex targetAnswer := by
      apply BitVec.eq_of_toNat_eq
      simpa only [← Bridge.idxTree_val_parts] using congrArg Fin.val htree
    have hleafBits : MessageDigest.leafIndex answer = MessageDigest.leafIndex targetAnswer := by
      apply BitVec.eq_of_toNat_eq
      simpa only [← Bridge.idxLeaf_val_parts] using congrArg Fin.val hposition
    have hindex : MessageDigest.forsIndices answer tree =
        MessageDigest.forsIndices targetAnswer tree := by
      apply Fin.ext
      have read (value : HashOutput) :
          ((DigestTransport.coveringDigest FIPS205.params (Bridge.answerEquiv value)).2 tree).val =
            (MessageDigest.forsIndices value tree).val :=
        (DigestTransport.coveringDigest_snd_val FIPS205.params
          (Bridge.answerEquiv value) tree).trans
          (Bridge.forsIdx_parts value tree)
      exact (read answer).symm.trans ((congrArg Fin.val hleaf).trans (read targetAnswer))
    simp only [FiredCoverage.Supplies, FiredCoverage.cellView,
      List.getD_eq_getElem?_getD, hcell, targetCell, Option.getD_some,
      MessageDigest.parse, htreeBits, hleafBits, hindex]
    exact ⟨rfl, trivial⟩
  refine ⟨targetIndex, ?_, targetReached, ?_⟩
  · simpa only [tapes, List.length_map, hrightLength] using targetLength
  · intro tree
    obtain ⟨entry, value, _hentry, _hlogged, hinstance, hleaf, coverer⟩ := coverers tree
    rcases coverer with
      ⟨index, _hlength, hconsumed, _pointClass, _hposition, htape⟩ |
      ⟨index, hlength, _hnext, hindexReached, hne, pointClass, hposition, hhit, htape⟩
    · obtain ⟨answer, hcell, hanswer⟩ := originalValue block.1.1 index value
        (by simpa only [tapes] using htape)
      exact Or.inl ⟨index, hconsumed,
        supplies block.1.1 index answer value tree hcell hanswer hinstance hleaf⟩
    · obtain ⟨answer, hcell, hanswer⟩ := originalValue block.1.2 index value
        (by simpa only [tapes] using htape)
      refine Or.inr ⟨index, ?_, hindexReached, hne,
        ⟨entry.2.randomness, entry.1, pointClass, hposition, hhit⟩,
        supplies block.1.2 index answer value tree hcell hanswer hinstance hleaf⟩
      simpa only [tapes, List.length_map, hrightLength] using hlength

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
end
