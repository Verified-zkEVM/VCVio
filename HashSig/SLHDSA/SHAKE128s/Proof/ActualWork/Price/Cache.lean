/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Terminal
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Arithmetic
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Graph
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Graph
import Mathlib.Tactic.NormNum

/-! # Graph, private-key and FORS charges on the terminal cache -/

public section
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open scoped ENNReal
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
open Guarded
/-- Node-key, derivable-public and Hmsg cache contributions at the native seed. -/
@[expose] noncomputable def cacheCharge (s : FIPS205.core.PkSeed) (cache : H.QueryCache) :
    ℝ≥0∞ :=
  2 * (((slhNodeKeys FIPS205.core s).keyEntries cache).encard : ℝ≥0∞) /
      Nat.card FIPS205.core.Y +
    seedCharge FIPS205.core s cache + hmsgCharge FIPS205.core cache

open Classical in
/-- Complete native charge from cache ownership, admitted attempts and full role counts. -/
@[expose] noncomputable def completeCharge (s : FIPS205.core.PkSeed) (rightLength : Nat)
    (terminal : NativeTerminal) : ℝ≥0∞ :=
  let publicCache := terminal.2.1.1.2.1.1.1
  let position := terminal.2.1.2.2.1
  let admittedS := terminal.2.2.1.2
  let signerC := position.cnt .signer
  let forgerNf := position.cnt .forger
  cacheCharge s publicCache +
    (if 1 ≤ admittedS then 1 else 0) / (Nat.card FIPS205.core.SkPrf : ℝ≥0∞) +
    (forgerNf : ℝ≥0∞) *
      (((9 * 2 ^ 99 : Nat) : ℝ≥0∞) / ((2 ^ 231 : Nat) : ℝ≥0∞) +
        (rightLength : ℝ≥0∞) / ((2 ^ 303 : Nat) : ℝ≥0∞)) +
    (if 2 ≤ signerC then 1 else 0) / ((8 * 2 ^ 128 : Nat) : ℝ≥0∞) +
    (if IsWeakKey FIPS205.params terminal.1.1.1 then 1 else 0)

open Classical in
/-- The complete native charge is funded on every supported cold execution. -/
theorem complete_charge_reserve :
  ∀ (q : Nat), 2 * q < 2 ^ 128 →
  ∀ (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (leftTape rightTape : List HashOutput),
    ∀ terminal ∈ support
        (nativeRun s adv true (32 * q - 1, 2 ^ 64) fallback leftTape rightTape),
      completeCharge s (16 * 2 ^ 128) terminal ≤
        (terminal.2.2.1.1 : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) +
          32 * (if IsWeakKey FIPS205.params terminal.1.1.1 then 1 else 0) := by
  classical
  intro q hqSmall s adv fallback leftTape rightTape t ht
  let cache := t.2.1.1.2.1.1.1
  let A := (slhNodeKeys FIPS205.core s).keyEntries cache
  let B := {point | (cache point).isSome ∧
    IsDerivablePublicQuery FIPS205.core s (.inl (.inr point))}
  let H := {point | (cache point).isSome ∧ IsHmsgPoint point}
  let M := t.2.1.1.2.2.1
  let S := t.2.2.1.2
  let Z := t.2.2.1.1
  let Nf := t.2.1.2.2.1.cnt .forger
  let C := t.2.1.2.2.1.cnt .signer
  let weak := decide (IsWeakKey FIPS205.params t.1.1.1)
  have owned := native_whole_reserve s adv (32 * q - 1, 2 ^ 64) fallback leftTape rightTape t ht
  obtain ⟨hbudget, hcard, hCS, hSNfZ, cap, hnonweak⟩ := owned
  change 32 * (A.encard : ℝ≥0∞) + 16 * (B.encard : ℝ≥0∞) +
      (31 * M + 32 * S : Nat) ≤ (Z : ℝ≥0∞) at hbudget
  change S + Nf ≤ Z at hSNfZ
  change C ≤ S at hCS
  change H.encard ≤ (C + Nf : Nat) at hcard
  have hA : A.Finite := by
    by_contra h
    rw [Set.Infinite.encard_eq h] at hbudget
    simp at hbudget
  have hB : B.Finite := by
    by_contra h
    rw [Set.Infinite.encard_eq h] at hbudget
    simp at hbudget
  have hH : H.Finite := Set.finite_of_encard_le_coe hcard
  have hZcap : Z ≤ 32 * q - 1 := cap.1
  have hHC : H.encard ≤ (Nf + C : Nat) := by
    simpa only [Nat.add_comm Nf C] using hcard
  obtain ⟨a, ha⟩ := hA.exists_encard_eq_coe
  obtain ⟨b, hb⟩ := hB.exists_encard_eq_coe
  obtain ⟨h, hh⟩ := hH.exists_encard_eq_coe
  have hAc : (A.encard : ℝ≥0∞) = a := by
    simpa using congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) ha
  have hBc : (B.encard : ℝ≥0∞) = b := by
    simpa using congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) hb
  have hHc : (H.encard : ℝ≥0∞) = h := by
    simpa using congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) hh
  rw [hAc, hBc] at hbudget
  rw [hh] at hHC
  have hbudgetNat : 32 * a + 16 * b + 31 * M + 32 * S ≤ Z := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ← add_assoc] at hbudget
    exact_mod_cast hbudget
  have hHNat : h ≤ Nf + C := by exact_mod_cast hHC
  have hNfZ : Nf ≤ Z := by omega
  have hZR : Z ≤ 16 * 2 ^ 128 := by omega
  have hweak : weak = false → Nf ≤ M := by
    intro hw
    exact hnonweak (by simpa [weak] using hw)
  have hcardY : Nat.card FIPS205.core.Y = 2 ^ 128 := by
    change Nat.card (Concrete.shakePrimitives FIPS205.params.params).core.Y = 2 ^ 128
    rw [Concrete.natCard_shakePrimitives_y]
    change 256 ^ 16 = 2 ^ 128
    norm_num
  have hcardPrf : Nat.card FIPS205.core.SkPrf = 2 ^ 128 := by
    change Nat.card FIPS205.core.Y = 2 ^ 128
    exact hcardY
  have numeric := complete_charge_numeric_bound a b h M S C Nf Z weak
    hbudgetNat hHNat hCS hNfZ hZR hweak
  change
    2 * (A.encard : ℝ≥0∞) / Nat.card FIPS205.core.Y +
      (B.encard : ℝ≥0∞) / Nat.card FIPS205.core.Y +
      (H.encard : ℝ≥0∞) / Nat.card FIPS205.core.Y +
      (if 1 ≤ S then 1 else 0) / (Nat.card FIPS205.core.SkPrf : ℝ≥0∞) +
      (Nf : ℝ≥0∞) *
        (((9 * 2 ^ 99 : Nat) : ℝ≥0∞) / ((2 ^ 231 : Nat) : ℝ≥0∞) +
          ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) / ((2 ^ 303 : Nat) : ℝ≥0∞)) +
      (if 2 ≤ C then 1 else 0) / ((8 * 2 ^ 128 : Nat) : ℝ≥0∞) +
      (if IsWeakKey FIPS205.params t.1.1.1 then 1 else 0) ≤
    (Z : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) +
      32 * (if IsWeakKey FIPS205.params t.1.1.1 then 1 else 0)
  rw [hAc, hBc, hHc, hcardY, hcardPrf]
  have hweakI : (((if weak then 1 else 0) : Nat) : ℝ≥0∞) =
      (if IsWeakKey FIPS205.params t.1.1.1 then 1 else 0) := by
    by_cases hw : IsWeakKey FIPS205.params t.1.1.1 <;> simp [weak, hw]
  simpa only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, hweakI] using numeric

/-- The activated graph/key charge used by the filled game fits the cache and alias terms of the
same native terminal. -/
theorem joint_charge_le_cache_alias (s : FIPS205.core.PkSeed) (t : NativeTerminal) :
    let out : GuardedFill.Value := (((t.1, (PUnit.unit, t.2.2)), t.2.1.1.1), t.2.1.1.2.2)
    let C := t.2.1.1.2.1.1.1
    2 * (((slhNodeKeys FIPS205.core s).keyEntries C).encard : ℝ≥0∞) / Nat.card FIPS205.core.Y +
      GuardedFill.keyCharge s out C ≤ cacheCharge s C +
        (if 1 ≤ t.2.2.1.2 then 1 else 0) / (Nat.card FIPS205.core.SkPrf : ℝ≥0∞) := by
  dsimp only
  by_cases active : 1 ≤ t.2.2.1.2
  · simp [GuardedFill.keyCharge, GuardedFill.signingActive, cacheCharge, active, one_div, add_assoc]
  · simp [GuardedFill.keyCharge, GuardedFill.signingActive, cacheCharge, active]

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
