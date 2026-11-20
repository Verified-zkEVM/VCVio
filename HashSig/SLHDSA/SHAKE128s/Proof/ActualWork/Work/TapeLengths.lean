/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.Program
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Signing

/-! # Tape lengths for a guarded execution under a joint work cap -/

public section
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
open Guarded

/-- Every supported paid native run fits the two class-tape lengths in the small-q regime. -/
theorem native_counts_le_tape_lengths (q : Nat) (hq : 2 * q < 2 ^ 128)
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (fb : (i : LabCommon.Domain) → LabCommon.Range i) (a b : List HashOutput)
    (terminal : NativeTerminal)
    (mem : terminal ∈ support (nativeRun s adv true (32 * q - 1, 2 ^ 64) fb a b)) :
    terminal.2.1.2.2.1.cnt .signer ≤ 2 ^ 64 ∧
      terminal.2.1.2.2.1.cnt .forger ≤ 16 * 2 ^ 128 := by
  let tapes : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j)
    | .signer => a.map Bridge.answerEquiv
    | .forger => b.map Bridge.answerEquiv
    | .other => []
  let rel : CoverageDeferred.S FIPS205.core := (((∅, ∅), []), (0, .keygen))
  let caps : Nat × Nat := (32 * q - 1, 2 ^ 64)
  change terminal ∈ support
    (SLHDSA.SHAKE128s.MarkedPrefix.wholeRun s adv caps fb rel tapes >>= _) at mem
  rw [mem_support_bind_iff] at mem
  obtain ⟨z, hz, last⟩ := mem
  simp only [support_pure, Set.mem_singleton_iff] at last
  subst terminal
  have cnt := SigningCounts.marked_whole_count_bounds s adv caps fb rel tapes z hz
  have bound := SigningCounts.marked_whole_paid_le_caps s adv caps fb rel tapes z hz
  have hs : z.1.1.1.2.2.1.2 ≤ 2 ^ 64 := bound.2
  have hz : z.1.1.1.2.2.1.1 ≤ 32 * q - 1 := bound.1
  exact ⟨cnt.1.trans hs, by
    change z.2.2.1.cnt .forger ≤ 16 * 2 ^ 128
    have hnf := cnt.2.1
    omega⟩
end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
