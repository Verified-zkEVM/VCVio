/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteLinkedBound
public import HashSigTest.SLHDSA.Target
public import HashSigTest.SLHDSA.WeakKeyBound

/-!
# The events of the verifying run, bounded with a further charge, checked

`HashSig.SLHDSA.Security.ByteLinkedBound` bounds the events of the verifying run at `n = 32`,
with a further charge. This file checks it at SLH-DSA-SHAKE-256s, for an adversary making
`2 ^ 64` hash and `2 ^ 64` signing queries.

* **No further event.** The run against the verifying adversary fires a target collision, a
  mixed hidden-value hit, the key clash or coverage with probability at most
  `securityBound (2, 1) (2 ^ 64 + V) (2 ^ 64) + (2 ^ 64 + 1) / |Y|`, and that bound is below one
  (`rhs_vp256s_lt_one`, with `V = 8444` and `|Y| = 2 ^ 256`).
* **The hedged form with no further charge.** At every `n = 32` parameter set the hedged bound
  with the trivial charge is
  `securityBound (2, 1) (qh + V) qs + 1 / |Y| + qs · ε · (qh + V + qs + 1) / |Y|`
  (`prEvent_romSchemeRun_verifyingAdv_le_hedged`).
* **The hook.** With a further charge whose transport and budget hold, the strong advantage is at
  most that bound plus the cost `κ`, here `(2 ^ 64 + 1) / |Y|`, in the deterministic form, and the
  hedged form takes the same hook.
* **The run point.** The run point of a deferred point is the rebuilt transcript on the merged
  cache, by definition.
-/

public section

open OracleComp OracleSpec SignatureAlg KeyedHash.Covering
open scoped ENNReal

namespace SLHDSA.ByteLinkedBoundTest

open Concrete Security WeakKeyBoundTest TargetTest

/-- The key discipline at SLH-DSA-SHAKE-256s. -/
theorem keyDiscipline_vp256s : (shakeCore vp256s).KeyDiscipline vp256s :=
  keyDiscipline_shakePrimitives vp256s
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds

/-! ## No further event -/

/-- **The events of the verifying run at SLH-DSA-SHAKE-256s, with no further charge and a concrete
budget.** -/
theorem prEvent_romSchemeRun_verifyingAdv_le_vp256s
    {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    {pkSeed : (shakeCore vp256s).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    Pr{let z ← romSchemeRun (shakeCore vp256s) (Equiv.refl _) optRand (pure pkSeed)
        (verifyingAdv vp256s (by decide) (by decide) adv)}[
      ((RunTargetCollision (shakeCore vp256s) (Equiv.refl _) z ∨ RunHiddenHitMixed vp256s z) ∨
        RunPrfKeyClash id pkSeed pkSeed z) ∨ RunItsrCovered (shakeCore vp256s) z] ≤
    securityBound vp256s.params (Nat.card (shakeCore vp256s).Y) 2 1
        (2 ^ 64 + GeneralScheme.verifyInternalQueryBound vp256s.params) (2 ^ 64) +
      (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y :=
  prEvent_romSchemeRun_verifyingAdv_le keyDiscipline_vp256s rfl (by decide) adv hadv

/-- `Y` has `2 ^ 256` elements at SLH-DSA-SHAKE-256s. -/
theorem natCard_Y_vp256s : Nat.card (shakeCore vp256s).Y = 2 ^ 256 := by
  change Nat.card (Vector UInt8 32) = 2 ^ 256
  rw [Nat.card_congr (arrayVectorEquivFin UInt8 32), Nat.card_fun, Nat.card_eq_fintype_card,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

/-- The `r`-th term of the coverage sum at `h = 64`, `a = 14`, `k = 22` and `qs = 2 ^ 64`. -/
theorem coverTerm_vp256s (r : ℕ) :
    (((r + 1) * (2 ^ 64) ^ r * r ^ 22 : ℕ) : ℝ≥0∞) *
        ((((2 : ℝ≥0∞) ^ 64)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ 14)⁻¹) ^ 22)
      = (((r + 1) * r ^ 22 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 308)⁻¹ := by
  have h2 : ((2 ^ 64 : ℕ) : ℝ≥0∞) ^ r * ((2 : ℝ≥0∞) ^ 64)⁻¹ ^ r = 1 := by
    rw [← mul_pow, Nat.cast_pow, Nat.cast_ofNat,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_pow]
  rw [show (((2 : ℝ≥0∞) ^ 14)⁻¹) ^ 22 = ((2 : ℝ≥0∞) ^ 308)⁻¹ by
    rw [← ENNReal.inv_pow, ← pow_mul]]
  calc (((r + 1) * (2 ^ 64) ^ r * r ^ 22 : ℕ) : ℝ≥0∞) *
        (((2 : ℝ≥0∞) ^ 64)⁻¹ ^ r * ((2 : ℝ≥0∞) ^ 308)⁻¹)
      = (((r + 1) * r ^ 22 : ℕ) : ℝ≥0∞) *
          (((2 ^ 64 : ℕ) : ℝ≥0∞) ^ r * ((2 : ℝ≥0∞) ^ 64)⁻¹ ^ r) * ((2 : ℝ≥0∞) ^ 308)⁻¹ := by
        push_cast; ring
    _ = _ := by rw [h2, mul_one]

/-- **The bound at SLH-DSA-SHAKE-256s is below one.** -/
theorem rhs_vp256s_lt_one :
    securityBound vp256s.params (Nat.card (shakeCore vp256s).Y) 2 1
        (2 ^ 64 + GeneralScheme.verifyInternalQueryBound vp256s.params) (2 ^ 64) +
      (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y < 1 := by
  have hp : vp256s.params.h = 64 ∧ vp256s.params.a = 14 ∧ vp256s.params.k = 22 := by decide
  have hV : GeneralScheme.verifyInternalQueryBound vp256s.params = 8444 := by decide
  rw [securityBound, hp.1, hp.2.1, hp.2.2, hV, natCard_Y_vp256s]
  have hN : (∑ r ∈ Finset.range 23, ((r + 1) * r ^ 22 : ℕ)) < 2 ^ 104 := by decide
  have hw : ((2 ^ 64 + 8444 : ℕ) : ℝ≥0∞) * (((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞)) ≤
      1 := by
    rw [← mul_div_assoc, ← Nat.cast_mul]
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact_mod_cast (by norm_num : (2 ^ 64 + 8444) * 2 ^ 64 ≤ 2 ^ 256)
  have hI : weightedTargetCoverBound 64 14 22 (2 ^ 64) (2 ^ 64 + 8444)
      (((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞)) ≤
        ((2 ^ 104 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 308)⁻¹ := by
    refine (weightedTargetCoverBound_le _ _ _ _ _ _ Nat.one_le_two_pow hw).trans ?_
    simp_rw [coverTerm_vp256s, ← Finset.sum_mul, ← Nat.cast_sum]
    gcongr
  have key : (((2 ^ 64 + 8444 : ℕ) : ℝ≥0∞) + 1) *
        (((2 ^ 104 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 308)⁻¹) +
      ((2 : ℕ) * ((2 ^ 64 + 8444 : ℕ) : ℝ≥0∞) + (((1 + 1) * 8444 : ℕ) : ℝ≥0∞)) *
        (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ +
      (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) < 1 := by
    rw [show (2 : ℝ≥0∞) ^ 308 = 2 ^ 256 * 2 ^ 52 by rw [← pow_add]]
    rw [← ENNReal.toReal_lt_toReal (by finiteness) ENNReal.one_ne_top]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_div,
      ENNReal.toReal_ofNat, ENNReal.toReal_one, ENNReal.toReal_natCast]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one]
    norm_num
  refine lt_of_le_of_lt ?_ key
  gcongr

/-- **The event of the verifying run at SLH-DSA-SHAKE-256s has probability below one.** -/
theorem prEvent_romSchemeRun_verifyingAdv_lt_one_vp256s
    {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    {pkSeed : (shakeCore vp256s).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    Pr{let z ← romSchemeRun (shakeCore vp256s) (Equiv.refl _) optRand (pure pkSeed)
        (verifyingAdv vp256s (by decide) (by decide) adv)}[
      ((RunTargetCollision (shakeCore vp256s) (Equiv.refl _) z ∨ RunHiddenHitMixed vp256s z) ∨
        RunPrfKeyClash id pkSeed pkSeed z) ∨ RunItsrCovered (shakeCore vp256s) z] < 1 :=
  (prEvent_romSchemeRun_verifyingAdv_le_vp256s adv hadv).trans_lt rhs_vp256s_lt_one

/-! ## The hedged form with no further charge -/

/-- **The hedged events of the verifying run, with no further charge.** At `n = 32`, with
`optRand pk` equal to `PK.seed` with probability at most `ε` at every public key, the trivial
charge is within the hedged budget, and the bound is
`securityBound vp.params |Y| 2 1 (qh + V) qs + 1 / |Y| + qs · ε · (qh + V + qs + 1) / |Y|`. -/
theorem prEvent_romSchemeRun_verifyingAdv_le_hedged {vp : ValidatedParams}
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeed : (shakeCore vp).PkSeed} (hd : (shakeCore vp).KeyDiscipline vp)
    (h32 : vp.params.n = 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = pkSeed] ≤ ε) :
    Pr{let z ← romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
        (verifyingAdv vp h32.le hnm adv)}[
      ((RunTargetCollision (shakeCore vp) (Equiv.refl _) z ∨ RunHiddenHitMixed vp z) ∨
        RunPrfKeyClash id pkSeed pkSeed z) ∨ RunItsrCovered (shakeCore vp) z] ≤
    securityBound vp.params (Nat.card (shakeCore vp).Y) 2 1
        (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
      1 / Nat.card (shakeCore vp).Y +
      qs * ε * (((qh + GeneralScheme.verifyInternalQueryBound vp.params : ℕ) : ℝ≥0∞) + qs + 1) /
        Nat.card (shakeCore vp).Y := by
  refine (prEvent_mono _ _ _ fun z h ↦ h.imp_left (Or.imp_right .inl)).trans
    ((prEvent_romSchemeRun_verifyingAdv_le_add_hedged hd h32 hnm adv hadv hε (fun _ ↦ False)
      (.ofSeed (fun _ _ ↦ False) 0 fun _ ↦ by simp) 0 ENNReal.zero_ne_top
      (fun _ _ h ↦ h.elim) fun z hz ↦ ?_).trans_eq (add_zero _))
  have h := two_mul_encard_keyEntries_div_add_seedCharge_le_of_mem_support
    hd.keySeparated (romQueryBound_verifyingAdv h32.le hnm hadv) hz
  simp only [DeferredCharge.ofSeed, Pi.zero_apply, add_zero] at h ⊢
  calc _ = (2 * (((slhNodeKeys (shakeCore vp) pkSeed).keyEntries z.2.1.1).encard : ℝ≥0∞) /
        Nat.card (shakeCore vp).Y + seedCharge (shakeCore vp) pkSeed z.2.1.1) +
        (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹ := by ring
    _ ≤ 2 * (((qh + GeneralScheme.verifyInternalQueryBound vp.params : ℕ) : ℝ≥0∞) +
        GeneralScheme.verifyInternalQueryBound vp.params) / Nat.card (shakeCore vp).Y +
        (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹ := by gcongr
    _ = _ := by
      simp only [ENNReal.div_eq_inv_mul]
      push_cast
      ring

/-! ## The hook -/

/-- **The deterministic bound with a further charge at SLH-DSA-SHAKE-256s.** With the cost
`(2 ^ 64 + 1) / |Y|` covering a further charge whose transport and budget hold. -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    {pkSeed : (shakeCore vp256s).PkSeed}
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) (χ : DeferredCharge (shakeCore vp256s) pkSeed)
    (hX : χ.Charges (verifyingAdv vp256s (by decide) (by decide) adv.toUnforgeableAdversary)
      fun z ↦ VirtualHit vp256s z ∨ LinkedHonestInput vp256s z)
    (hbud : χ.WithinBudget (verifyingAdv vp256s (by decide) (by decide) adv.toUnforgeableAdversary)
      (fun C ↦ hmsgCharge (shakeCore vp256s) C + (Nat.card (shakeCore vp256s).Y : ℝ≥0∞)⁻¹)
      ((2 * (((2 ^ 64 : ℕ) : ℝ≥0∞) + 2 * GeneralScheme.verifyInternalQueryBound vp256s.params) +
          ((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y)) :
    shakeStrongAdvantage vp256s adv ≤
      securityBound vp256s.params (Nat.card (shakeCore vp256s).Y) 2 1
          (2 ^ 64 + GeneralScheme.verifyInternalQueryBound vp256s.params) (2 ^ 64) +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y :=
  shakeStrongAdvantage_pure_le_securityBound_add
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl (by decide) adv
    hadv χ _ (div_natCard_ne_top (by simp)) hX hbud

/-- **The hedged form takes the same hook.** -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    {pkSeed : (shakeCore vp256s).PkSeed}
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = pkSeed] ≤ ε)
    (χ : DeferredCharge (shakeCore vp256s) pkSeed) (κ : ℝ≥0∞) (hκ : κ ≠ ⊤)
    (hX : χ.Charges (verifyingAdv vp256s (by decide) (by decide) adv.toUnforgeableAdversary)
      fun z ↦ VirtualHit vp256s z ∨ LinkedHonestInput vp256s z)
    (hbud : χ.WithinBudget (verifyingAdv vp256s (by decide) (by decide) adv.toUnforgeableAdversary)
      (fun _ ↦ (Nat.card (shakeCore vp256s).Y : ℝ≥0∞)⁻¹)
      ((2 * (((2 ^ 64 : ℕ) : ℝ≥0∞) + 2 * GeneralScheme.verifyInternalQueryBound vp256s.params) +
          1) / Nat.card (shakeCore vp256s).Y + κ)) :
    shakeStrongAdvantage vp256s adv ≤
      securityBound vp256s.params (Nat.card (shakeCore vp256s).Y) 2 1
          (2 ^ 64 + GeneralScheme.verifyInternalQueryBound vp256s.params) (2 ^ 64) +
        1 / Nat.card (shakeCore vp256s).Y +
        ((2 ^ 64 : ℕ) : ℝ≥0∞) * ε * (((2 ^ 64 + GeneralScheme.verifyInternalQueryBound
          vp256s.params : ℕ) : ℝ≥0∞) + ((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) /
          Nat.card (shakeCore vp256s).Y + κ :=
  shakeStrongAdvantage_pure_le_securityBound_add_hedged
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl (by decide) adv
    hadv hε χ κ hκ hX hbud

/-! ## The run point -/

/-- The run point of a deferred point is the rebuilt transcript on the merged cache. -/
example {pkSeed : (shakeCore vp256s).PkSeed}
    (w : (DeriveOutcome (shakeCore vp256s) × LabState (shakeCore vp256s) ×
      List (DeriveQuery (shakeCore vp256s) ⊕ NodeKey (shakeCore vp256s))) ×
      LabState (shakeCore vp256s) × ((shakeCore vp256s).SkSeed × (shakeCore vp256s).SkPrf)) :
    deferredRunPoint pkSeed w = (DeriveOutcome.fill (shakeCore vp256s) w.2.2 w.1.1,
      (secretEncoding (shakeCore vp256s) (Equiv.refl _) pkSeed).merge w.2.2
        ((slhGraph (shakeCore vp256s) pkSeed).toSplitCache w.2.1)) :=
  rfl

end SLHDSA.ByteLinkedBoundTest
