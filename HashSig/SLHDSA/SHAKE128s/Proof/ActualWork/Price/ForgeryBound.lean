/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Reserve
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Combined

/-!
# A joint-work forgery bound from covered residual winners
-/

public section
open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open scoped SLHDSA.SHAKE128s.Bridge.SharedExperiment.SampleSpaces
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical

/-- In the nontrivial budget range, a surviving win covered on the actual native block gives
the strict-cap upper bound on the original real game, including both initial weak-key payments. -/
theorem strict_bound_of_residual_covered (adv : Game.Adversary FIPS205.Answer PK) (q : Nat)
    (small : 2 * q < 2 ^ 128)
    (hlimit : Game.WithinSigningLimit FIPS205.scheme adv)
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q)
    (fb : Seed → LabFallback)
    (covered : ∀ s, Pr{let r ← ((slhGraph FIPS205.core s).deferredFillDraw ($ᵗ GuardedFill.Secret)
        (GuardedFill.labProgram s adv true true (32 * q - 1, 2 ^ 64) (fb s)))}[residual s r] ≤
      Pr{let b ← (NoticingTape.blockRunOf (Native.nativeRun s adv true (32 * q - 1, 2 ^ 64)
        (fb s)) (2 ^ 64 + 1) (16 * 2 ^ 128))}[GuardedFill.actualCoverage b]) :
    (Game.securityGame FIPS205.scheme).advantage () adv ≤
      ((32 * q - 1 : Nat) : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) + 34 * weakMass := by
  let L := 2 ^ 64 + 1
  let R := 16 * 2 ^ 128
  let caps := (32 * q - 1, 2 ^ 64)
  apply (original_win_le_tape_price adv q hlimit hbound fb L R).trans
  apply le_trans _ (native_price_with_escapes_le_strict_cap q small adv fb L)
  apply add_le_add _ le_rfl
  apply lintegral_mono
  intro s
  dsimp only
  apply le_trans _ (covered_plus_graph_le_price s adv q (fb s))
  apply add_le_add _ le_rfl
  have proj := (GuardedFill.eraseTapes_tapedFill s adv true caps (fb s) L R).prEvent_eq (residual s)
  rw [prEvent_map] at proj
  exact proj.trans_le (covered s)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical
