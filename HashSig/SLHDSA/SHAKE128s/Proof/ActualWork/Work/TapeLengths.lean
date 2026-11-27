/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.Program
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Signing

/-!
# Tape lengths for a guarded execution under a joint work cap

The terminal counts of a supported native run bound its consumption of the two digest tapes
under the joint work cap in the small-budget range.
-/

public section
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
open Guarded

/-- Reinstating the bookkeeping unit in a supported native terminal recovers a marked
execution on exactly the supplied signer and forger tapes. -/
theorem marked_mem_of_native_mem {s : FIPS205.core.PkSeed} {adv : Game.Adversary FIPS205.Answer PK}
    {caps : Nat × Nat} {fb : (i : LabCommon.Domain) → LabCommon.Range i} {a b : List HashOutput}
    {t : NativeTerminal} (mem : t ∈ support (nativeRun s adv true caps fb a b)) :
    let tapes : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j)
      | .signer => a.map Bridge.answerEquiv
      | .forger => b.map Bridge.answerEquiv
      | .other => []
    ((((t.1, (PUnit.unit, t.2.2)), t.2.1.1.1), t.2.1.1.2), t.2.1.2) ∈ support
      (SLHDSA.SHAKE128s.MarkedPrefix.wholeRun s adv caps fb
        (((∅, ∅), []), (0, .keygen)) tapes) := by
  intro tapes
  change t ∈ support (SLHDSA.SHAKE128s.MarkedPrefix.wholeRun s adv caps fb _ tapes >>= _) at mem
  rw [mem_support_bind_iff] at mem
  obtain ⟨z, hz, last⟩ := mem
  simp only [support_pure, Set.mem_singleton_iff] at last
  subst t
  exact hz

/-- Every supported paid native run fits the two class-tape lengths in the small-q regime. -/
theorem native_counts_le_tape_lengths (q : Nat) (hq : 2 * q < 2 ^ 128)
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (fb : (i : LabCommon.Domain) → LabCommon.Range i) (a b : List HashOutput)
    (terminal : NativeTerminal)
    (mem : terminal ∈ support (nativeRun s adv true (32 * q - 1, 2 ^ 64) fb a b)) :
    terminal.2.1.2.2.1.cnt .signer ≤ 2 ^ 64 ∧
      terminal.2.1.2.2.1.cnt .forger ≤ 16 * 2 ^ 128 := by
  have hz := marked_mem_of_native_mem mem
  have cnt := SigningCounts.marked_whole_count_bounds s adv _ fb _ _ _ hz
  have cap := SigningCounts.marked_whole_paid_le_caps s adv _ fb _ _ _ hz
  have hs : terminal.2.2.1.2 ≤ 2 ^ 64 := cap.2
  have hw : terminal.2.2.1.1 ≤ 32 * q - 1 := cap.1
  exact ⟨cnt.1.trans hs, by
    have hf : terminal.2.2.1.2 + terminal.2.1.2.2.1.cnt .forger ≤ terminal.2.2.1.1 := cnt.2.1
    omega⟩

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
