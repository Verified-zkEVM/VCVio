/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.WinningEvent
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Tapes
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Tapes

/-!
# Averaging graph charges and weak keys over terminal blocks
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal NNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open scoped SLHDSA.SHAKE128s.Bridge.SharedExperiment.SampleSpaces
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical
open GuardedFill

/-- The two sampled digest tapes paired with their terminal native execution. -/
abbrev Block := GuardedFill.Block
/-- The public seed sampled before the joint-work experiment. -/
abbrev Seed := FIPS205.core.PkSeed
/-- Answers supplied to the marked oracle computation when its budget guard rejects a query. -/
abbrev LabFallback := (input : LabCommon.Domain) → LabCommon.Range input
/-- A sampled block together with the filled graph state and the secret used to interpret it. -/
abbrev BlockFill := Block × LabState FIPS205.core × Secret

/-- A winning observation with a nonweak key, no graph conflict and no hash or key hazard. -/
abbrev residual (s : Seed) (r : Filled.{0}) : Prop :=
  (∃ out, (observe r.1.1).2.1 = some out ∧ SigningView.Wins id out) ∧
    ¬IsWeakKey FIPS205.params r.1.1.1.1.1.1.1 ∧
    ¬(((slhGraph FIPS205.core s).Conflict r.2.1 ∨
      (slhNodeKeys FIPS205.core s).TCHazard r.2.1) ∨ keyHazard s r.1.1 r.2.2 r.2.1)

/-- The sum of the node-key collision charge and the encoding charge on the terminal cache. -/
@[expose] noncomputable def graphPrice (s : Seed) (r : Block) : ℝ≥0∞ :=
  let t := r.2
  let v : Value.{0} := (((t.1, (PUnit.unit, t.2.2)), t.2.1.1.1), t.2.1.1.2.2)
  let cache := t.2.1.1.2.1.1.1
  2 * (((slhNodeKeys FIPS205.core s).keyEntries cache).encard : ℝ≥0∞) /
    Nat.card FIPS205.core.Y + keyCharge s v cache

/-- The honest-address count divided by the square of the SHAKE-128s seed-space size. -/
noncomputable abbrev weakMass : ℝ≥0∞ :=
  (1591788895347057694892543 : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞)

/-- On any tape lengths the physical game pays a residual event and an expectation on the same
native block, plus the two weak-key marginals. -/
theorem original_win_le_tape_price (adv : Game.Adversary FIPS205.Answer PK)
    (q : Nat) (hlimit : Game.WithinSigningLimit FIPS205.scheme adv)
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q)
    (fb : Seed → LabFallback) (L R : Nat) :
    let caps := (32*q-1, 2^64)
    let blocks := fun s => NoticingTape.blockRunOf (Native.nativeRun s adv true caps (fb s)) L R
    (Game.securityGame FIPS205.scheme).advantage () adv ≤
      (∫⁻ s, Pr{let r ← tapedFill s adv true caps (fb s) L R}[residual s (eraseTapes r)] +
        (∫⁻ price, price ∂𝒟[graphPrice s <$> blocks s])
        ∂𝒟[($ᵗ Seed : ProbComp Seed)]) + 2 * weakMass := by
  intro caps blocks
  apply (original_win_le_uncharged_charge_two_weak adv q hlimit hbound fb).trans
  apply add_le_add _ le_rfl
  apply lintegral_mono
  intro s
  apply add_le_add
  · dsimp only
    have h := (eraseTapes_tapedFill s adv true caps (fb s) L R).prEvent_eq (residual s)
    simpa only [residual, prEvent_map] using h.symm.le
  · let price := fun z : Value × LabState FIPS205.core × List (DeriveQuery FIPS205.core ⊕
        NodeKey FIPS205.core) => 2 * (((slhNodeKeys FIPS205.core s).keyEntries z.2.1.1).encard :
        ℝ≥0∞) / Nat.card FIPS205.core.Y + keyCharge s z.1 z.2.1.1
    dsimp only
    rw [labProgram_eq_native]
    have h := (Native.native_deferred_marginal s adv true caps (fb s) L R).map price
    simp only [Functor.map_map] at h
    have eq := h.evalDist_eq
    exact le_of_eq (congrArg (fun m : Measure ℝ≥0∞ => ∫⁻ x : ℝ≥0∞, x ∂m) eq.symm)

/-- The weak initial native key marginal is the same for every tape length. -/
theorem native_block_weak_average (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat) (fb : Seed → LabFallback) (L R : Nat) :
    (∫⁻ s, Pr{let block ← NoticingTape.blockRunOf (Native.nativeRun s adv reserve caps (fb s)) L R}[
      IsWeakKey FIPS205.params block.2.1.1.1] ∂𝒟[($ᵗ Seed : ProbComp Seed)]) ≤ weakMass := by
  apply le_trans _ (deferred_weak_mass adv reserve caps fb)
  apply lintegral_mono
  intro s
  let weak := fun block : Block => IsWeakKey FIPS205.params block.2.1.1.1
  have h := (eraseTapes_tapedFill s adv reserve caps (fb s) L R).prEvent_eq
    (fun r => IsWeakKey FIPS205.params r.1.1.1.1.1.1.1)
  dsimp only
  rw [← h, prEvent_map]
  simpa only [prEvent_map, weak, eraseTapes] using
    ((fst_tapedFill s adv reserve caps (fb s) L R).prEvent_eq weak).symm.le

/-- The unit left by the strict cap pays 34 full weak-key address masses. -/
theorem reserve_pays_weak (q : Nat) (hq : 1 ≤ q) :
    ((32*q-1 : Nat) : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) + 34 * weakMass ≤
      (q : ℝ≥0∞) / ((2^127 : Nat) : ℝ≥0∞) := by
  have weak : 34 * weakMass ≤ (1 : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) := by
    have hn : (34 : ℝ≥0) * (1591788895347057694892543 / (2 ^ 256)) ≤ 1 / (16 * 2 ^ 128) := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      norm_num
    have hc := ENNReal.coe_le_coe.mpr hn
    push_cast [ENNReal.coe_div (by positivity : (2:NNReal)^256 ≠ 0),
      ENNReal.coe_div (by positivity : (16:NNReal)*2^128 ≠ 0)] at hc
    simpa only [weakMass, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul] using hc
  let K := 32*q-1
  have gap : K + 1 = 32 * q := by dsimp only [K]; omega
  calc
    _ ≤ (K : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) := add_le_add le_rfl weak
    _ = ((K + 1 : Nat) : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) := by
      rw [Nat.cast_add, Nat.cast_one, ENNReal.add_div]
    _ = (q : ℝ≥0∞) * (32 / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞)) := by
      rw [gap, Nat.cast_mul]
      simp only [Nat.cast_ofNat, mul_div_assoc, mul_comm]
    _ = (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
      rw [div_eq_mul_inv]
      congr 1
      have hn : (32 : NNReal) / (16 * 2 ^ 128) = (2 ^ 127)⁻¹ := by norm_num
      have hc := congrArg (fun x : NNReal => (x : ℝ≥0∞)) hn
      push_cast [ENNReal.coe_div (by positivity : (16:NNReal)*2^128 ≠ 0),
        ENNReal.coe_inv (by positivity : (2:NNReal)^127 ≠ 0)] at hc
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using hc

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical
