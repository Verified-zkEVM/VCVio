/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.GraphEntries
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.TapeLengths
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.DigestCache
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.Support

/-! # Terminal cache accounting on a complete guarded execution -/

public section
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open scoped ENNReal
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
open Guarded

/-- The actual native terminal funds its graph, digest cache and two class counters jointly. -/
theorem native_whole_reserve (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (caps : Nat × Nat) (fb : (i : LabCommon.Domain) → LabCommon.Range i) (a b : List HashOutput)
    (t : NativeTerminal) (mem : t ∈ support (nativeRun s adv true caps fb a b)) :
    let cache := t.2.1.1.2.1.1.1
    let paid := t.2.2.1
    let observed := t.2.1.1.2.2.1
    let cnt := t.2.1.2.2.1.cnt
    DeferredReserve.entries s cache + (31 * observed + 32 * paid.2 : Nat) ≤ (paid.1 : ℝ≥0∞) ∧
      {p | (cache p).isSome ∧ IsHmsgPoint (vp := FIPS205.params) (core := FIPS205.core) p}.encard
        ≤ (cnt .signer + cnt .forger : Nat) ∧ cnt .signer ≤ paid.2 ∧
      paid.2 + cnt .forger ≤ paid.1 ∧ paid ≤ caps ∧
      (¬IsWeakKey FIPS205.params t.1.1.1 → cnt .forger ≤ observed) := by
  have graph := DeferredReserve.whole_graph_reserve s adv caps fb _
    (projected_mem_deferred s adv caps fb a b t mem)
  let tapes : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j)
    | .signer => a.map Bridge.answerEquiv
    | .forger => b.map Bridge.answerEquiv
    | .other => []
  let rel : CoverageDeferred.S FIPS205.core := (((∅, ∅), []), (0, .keygen))
  change t ∈ support (SLHDSA.SHAKE128s.MarkedPrefix.wholeRun s adv caps fb rel tapes >>= _) at mem
  rw [mem_support_bind_iff] at mem
  obtain ⟨z, hz, last⟩ := mem
  simp only [support_pure, Set.mem_singleton_iff] at last
  subst t
  have cnt := SigningCounts.marked_whole_count_bounds s adv caps fb rel tapes z hz
  exact ⟨graph.1, CacheCardinality.whole_digest_cache_card s adv caps fb tapes z hz,
    cnt.1, cnt.2.1, graph.2, cnt.2.2⟩

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
