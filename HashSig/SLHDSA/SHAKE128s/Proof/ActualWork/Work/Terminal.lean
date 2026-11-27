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

/-- Resources of a single guarded native terminal that pay for its cache and marked events. -/
structure TerminalReserve (s : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (t : NativeTerminal) : Prop where
  graph : DeferredReserve.entries s t.2.1.1.2.1.1.1 +
    (31 * t.2.1.1.2.2.1 + 32 * t.2.2.1.2 : Nat) ≤ (t.2.2.1.1 : ℝ≥0∞)
  digests : {p | (t.2.1.1.2.1.1.1 p).isSome ∧
    IsHmsgPoint (vp := FIPS205.params) (core := FIPS205.core) p}.encard ≤
      (t.2.1.2.2.1.cnt .signer + t.2.1.2.2.1.cnt .forger : Nat)
  signer : t.2.1.2.2.1.cnt .signer ≤ t.2.2.1.2
  forger : t.2.2.1.2 + t.2.1.2.2.1.cnt .forger ≤ t.2.2.1.1
  paid_le : t.2.2.1 ≤ caps
  nonweak : ¬IsWeakKey FIPS205.params t.1.1.1 → t.2.1.2.2.1.cnt .forger ≤ t.2.1.1.2.2.1

/-- The actual native terminal funds its graph, digest cache and two class counters jointly. -/
theorem native_whole_reserve (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (caps : Nat × Nat) (fb : (i : LabCommon.Domain) → LabCommon.Range i) (a b : List HashOutput)
    (t : NativeTerminal) (mem : t ∈ support (nativeRun s adv true caps fb a b)) :
    TerminalReserve s caps t := by
  have graph := DeferredReserve.whole_graph_reserve s adv caps fb _
    (projected_mem_deferred s adv caps fb a b t mem)
  have hz := marked_mem_of_native_mem mem
  have cnt := SigningCounts.marked_whole_count_bounds s adv caps fb _ _ _ hz
  exact ⟨graph.1, CacheCardinality.whole_digest_cache_card s adv caps fb _ _ hz,
    cnt.1, cnt.2.1, graph.2, cnt.2.2⟩

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
