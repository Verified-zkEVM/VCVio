/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Encoding.ActivatedClash
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.RootKey

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.SampleSpaces

/-! # Paying the root weak-key term and active key-encoding clashes -/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open scoped SLHDSA.SHAKE128s.Bridge.SharedExperiment.SampleSpaces
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical

/-- The two original joint resource conditions bound the real FIPS experiment by its remaining
uncharged winners or weak keys, the same-run graph and activated key charge, and the original
physical weak-key escape. -/
theorem original_win_le_remaining_charge_mass (adv : Game.Adversary FIPS205.Answer PK) (q : Nat)
    (hlimit : Game.WithinSigningLimit FIPS205.scheme adv)
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q)
    (fallback : (s : FIPS205.core.PkSeed) →
      (input : LabCommon.Domain) → LabCommon.Range input) :
    Pr{let out ← (Game.securityGame FIPS205.scheme).experiment () adv}[out.1 = true] ≤
      (∫⁻ s, let G := slhGraph FIPS205.core s
             let nk := slhNodeKeys FIPS205.core s
             let program := GuardedFill.labProgram s adv true true (32*q-1, 2^64) (fallback s)
             Pr{let r ← G.deferredFillDraw ($ᵗ GuardedFill.Secret) program}[
               ((∃ out, (GuardedFill.observe r.1.1).2.1 = some out ∧ SigningView.Wins id out) ∨
                 IsWeakKey FIPS205.params r.1.1.1.1.1.1.1) ∧
                 ¬((G.Conflict r.2.1 ∨ nk.TCHazard r.2.1) ∨
                   GuardedFill.keyHazard s r.1.1 r.2.2 r.2.1)] +
               ∫⁻ charge, charge ∂𝒟[(fun r =>
                 2 * ((nk.keyEntries r.2.1.1).encard : ℝ≥0∞) / Nat.card FIPS205.core.Y +
                   GuardedFill.keyCharge s r.1 r.2.1.1) <$>
                 (simulateQ G.deferredImpl program).run ((∅, ∅), [])]
        ∂𝒟[($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)]) +
        (1591788895347057694892543 : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  apply (original_win_le_filled_add_address_mass adv q hlimit hbound fallback).trans
  apply add_le_add _ le_rfl
  rw [prEvent_bind_bind_eq_lintegral_of_discrete]
  exact lintegral_mono fun s =>
    GuardedFill.filled_le_remaining_add_charge s adv true (32*q-1, 2^64) (fallback s)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical
