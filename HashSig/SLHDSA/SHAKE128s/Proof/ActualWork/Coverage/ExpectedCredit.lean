/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.SampleSpaces
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coverage.ConsumedCredit
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Expected FORS credit of the consumed signing and forgery prefixes

The signer and forger prefixes consumed on a run determine its FORS coverage event. Their
expected credit bounds the probability of that event on the joint tape block.
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill

open SLHDSA.SHAKE128s.MarkedPrefix

/-- The signer-prefix and forger counts in the FORS event belong to this same native block. -/
def actualCoverage (block : Block) : Prop :=
  FiredCoverage.FiredCovered (fun t : Native.NativeTerminal => t.2.1.2.2.1.cnt .forger)
    (fun t i => Coverage.ActualKeyPotential.Fired FIPS205.core t.1.1.1 t.2.1.2 i)
    (block.2.2.1.2.2.1.next .signer) (16 * 2^128) block

/-- Repack the native computation with the identical key, counts, raw log and role state. -/
def nativeOutput (r : Outcome) : Native.NativeTerminal :=
  (r.1.1.1.1, (((r.1.1.2, r.1.2), r.2), r.1.1.1.2.2))

private theorem block_map {α β : Type} (src : List HashOutput → List HashOutput → ProbComp α)
    (dest : List HashOutput → List HashOutput → ProbComp β) (f : α → β) (L R : Nat)
    (h : ∀ a b, dest a b = f <$> src a b) :
    NoticingTape.blockRunOf dest L R =
      (fun b => (b.1, f b.2)) <$> NoticingTape.blockRunOf src L R := by
  unfold NoticingTape.blockRunOf
  simp only [map_bind]
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  rw [h]
  simp only [Functor.map_map]

/-- Fired coverage is paid on the actual guarded native blocks by the probability of two
signer queries and the expected forger count, over the same PK and transcript. -/
theorem actualCoverage_le_paid (q : Nat) (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    let blocks := NoticingTape.blockRunOf
      (Native.nativeRun s adv true (32*q-1, 2^64) fallback) (2^64+1) (16*2^128)
    Pr{let b ← blocks}[actualCoverage b] ≤
      ((1 : ℝ≥0∞) / ((8*2^128 : Nat) : ℝ≥0∞)) *
        Pr{let b ← blocks}[2 ≤ b.2.2.1.2.2.1.cnt .signer] +
      (∫⁻ k, k ∂𝒟[(fun b : Block => (b.2.2.1.2.2.1.cnt .forger : ℝ≥0∞)) <$> blocks]) *
        ((((9*2^99 : Nat) : ℝ≥0∞) / ((2^231 : Nat) : ℝ≥0∞)) +
          ((16*2^128 : Nat) : ℝ≥0∞) / ((2^303 : Nat) : ℝ≥0∞)) := by
  intro blocks
  let relative : CoverageDeferred.S FIPS205.core := (((∅, ∅), []), (0, .keygen))
  let caps := (32*q-1, 2^64)
  let run := SLHDSA.SHAKE128s.MarkedPrefix.run s adv caps fallback relative
  let marked := NoticingTape.blockRunOf run (2^64+1) (16*2^128)
  let bmap := fun b : (List HashOutput × List HashOutput) × Outcome => (b.1, nativeOutput b.2)
  have component (a b : List HashOutput) :
      Native.nativeRun s adv true caps fallback a b = nativeOutput <$> run a b := by
    simp only [Native.nativeRun, bind_pure_comp]
    rfl
  have same : blocks = bmap <$> marked :=
    block_map run (Native.nativeRun s adv true caps fallback) nativeOutput _ _ component
  have paid := marked_whole_consumed_credit s adv caps fallback relative (16*2^128)
  let T := (List HashOutput × List HashOutput) × Outcome
  let _ : MeasurableSpace T := ⊤
  have expectation :
      (∫⁻ k, k ∂𝒟[(fun b : Block => (b.2.2.1.2.2.1.cnt .forger : ℝ≥0∞)) <$> blocks]) =
      ∑' t, Pr{let u ← marked}[u = t] * (forgerCount t.2 : ℝ≥0∞) := by
    rw [same, Functor.map_map, lintegral_id_evalDist_map, lintegral_evalDist_eq_tsum]
    rfl
  rw [expectation, same, prEvent_map, prEvent_map]
  exact paid

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill
