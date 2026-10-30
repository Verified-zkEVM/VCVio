/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.WeakKeyBound
import HashSig.SLHDSA.EncodingLemmas
import HashSig.SLHDSA.Security.AddressKeys
import HashSig.SLHDSA.Security.ByteConformance

/-!
# The weak-key bound, checked

`HashSig.SLHDSA.Security.WeakKeyBound` bounds the weak-key event of the SHAKE256 router. This file
checks it at the parameters of FIPS 205.

* **The bound on the honest addresses** at the six SHAKE parameter sets, by evaluation of the
  closed form of `honestAdrsCount`: its value, the integer part of its binary logarithm, and its
  size against the union ledger `constructionAddresses`.
* **The bounds at all 12 FIPS 205 parameter sets**, with the address widths and `16 ≤ n`
  discharged: the public key of the run, the weak-key event per public seed, and its average.
* **Weak and strong seeds at SLH-DSA-SHAKE-256s.** The all-zero public seed is the key of the
  all-zero address, the first hash step of the first WOTS+ chain of the first instance, so it is a
  weak seed: every public key at it is weak. A seed carrying the type word `7` is the key of no
  honest address, so its weak-key mass is zero and so is the weak-key event of the run at it.
* **A weak key at SLH-DSA-SHAKE-128s**: the all-zero public seed and public root.
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal

namespace SLHDSA.WeakKeyBoundTest

open Concrete Security

/-- SLH-DSA-SHAKE-128s. -/
abbrev vp128s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_128s
/-- SLH-DSA-SHAKE-128f. -/
abbrev vp128f : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_128f
/-- SLH-DSA-SHAKE-192s. -/
abbrev vp192s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_192s
/-- SLH-DSA-SHAKE-192f. -/
abbrev vp192f : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_192f
/-- SLH-DSA-SHAKE-256s. -/
abbrev vp256s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_256s
/-- SLH-DSA-SHAKE-256f. -/
abbrev vp256f : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_256f

/-! ## The values of `honestAdrsCount` -/

/-- SLH-DSA-SHAKE-128s: `|A_hon| ≈ 2^80.40`. -/
example : honestAdrsCount vp128s = 1591788895347057694892543 := by
  rw [honestAdrsCount_eq]; decide

/-- SLH-DSA-SHAKE-128f: `|A_hon| ≈ 2^78.76`. -/
example : honestAdrsCount vp128f = 512534878340559730413511 := by
  rw [honestAdrsCount_eq]; decide

/-- SLH-DSA-SHAKE-192s: `|A_hon| ≈ 2^82.67`. -/
example : honestAdrsCount vp192s = 7714313990982286445273599 := by
  rw [honestAdrsCount_eq]; decide

/-- SLH-DSA-SHAKE-192f: `|A_hon| ≈ 2^80.68`. -/
example : honestAdrsCount vp192f = 1936665684817391308429255 := by
  rw [honestAdrsCount_eq]; decide

/-- SLH-DSA-SHAKE-256s: `|A_hon| ≈ 2^84.05`. -/
example : honestAdrsCount vp256s = 19966778066156452796772607 := by
  rw [honestAdrsCount_eq]; decide

/-- SLH-DSA-SHAKE-256f: `|A_hon| ≈ 2^83.74`. -/
example : honestAdrsCount vp256f = 16195218117312364562383887 := by
  rw [honestAdrsCount_eq]; decide

/-- The integer parts of the binary logarithms: `80, 78, 82, 80, 84, 83`. -/
example : 2 ^ 80 ≤ honestAdrsCount vp128s ∧ honestAdrsCount vp128s < 2 ^ 81 ∧
    2 ^ 78 ≤ honestAdrsCount vp128f ∧ honestAdrsCount vp128f < 2 ^ 79 ∧
    2 ^ 82 ≤ honestAdrsCount vp192s ∧ honestAdrsCount vp192s < 2 ^ 83 ∧
    2 ^ 80 ≤ honestAdrsCount vp192f ∧ honestAdrsCount vp192f < 2 ^ 81 ∧
    2 ^ 84 ≤ honestAdrsCount vp256s ∧ honestAdrsCount vp256s < 2 ^ 85 ∧
    2 ^ 83 ≤ honestAdrsCount vp256f ∧ honestAdrsCount vp256f < 2 ^ 84 := by
  simp only [honestAdrsCount_eq]; decide

/-- At every SHAKE parameter set, `honestAdrsCount` is below `3/2` times the length of the union
ledger. -/
example : ∀ vp ∈ [vp128s, vp128f, vp192s, vp192f, vp256s, vp256f],
    2 * honestAdrsCount vp < 3 * (constructionAddresses vp).length := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    honestAdrsCount_eq, constructionAddresses_length]
  decide

/-! ## At all 12 FIPS 205 parameter sets -/

/-- The public key of the run is `(PK.seed, uniform root)`, both signing modes. -/
example (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary
      (romScheme (shakeCore set.validatedParams) (Equiv.refl _) optRand (pure pkSeed)))
    (P : PublicKeyCore (shakeCore set.validatedParams) → Prop) :
    Pr{let z ← romSchemeRun (shakeCore set.validatedParams) (Equiv.refl _) optRand
        (pure pkSeed) adv}[P z.1.pk] ≤
      Pr{let r ← $ᵗ (shakeCore set.validatedParams).Y}[P ⟨pkSeed, r⟩] :=
  prEvent_romSchemeRun_pk_le
    (rootKeySeparated_shakeCore (fipsApprovedAddressBounds set).toCanonicalAddressBounds) _ _ _
    adv P

/-- The weak-key event per public seed. -/
example (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary
      (romScheme (shakeCore set.validatedParams) (Equiv.refl _) optRand (pure pkSeed))) :
    Pr{let z ← romSchemeRun (shakeCore set.validatedParams) (Equiv.refl _) optRand
        (pure pkSeed) adv}[IsWeakKey set.validatedParams z.1.pk] ≤
      weakKeyMass set.validatedParams pkSeed :=
  prEvent_romSchemeRun_isWeakKey_le (fipsApprovedAddressBounds set).toCanonicalAddressBounds _ _
    _ adv

/-- The weak-key mass averaged over a uniform public seed, with a seed-independent part. -/
example (set : FipsParameterSet) [MeasurableSpace (shakeCore set.validatedParams).PkSeed]
    [DiscreteMeasurableSpace (shakeCore set.validatedParams).PkSeed] (C : ℝ≥0∞) :
    ∫⁻ pkSeed, (C + weakKeyMass set.validatedParams pkSeed)
        ∂𝒟[($ᵗ (shakeCore set.validatedParams).PkSeed : ProbComp _)] ≤
      C + honestAdrsCount set.validatedParams / 2 ^ 256 :=
  lintegral_add_weakKeyMass_le set.sixteen_le_n C

/-! ## Weak and strong seeds at SLH-DSA-SHAKE-256s -/

/-- The all-zero address is the first hash step of the first WOTS+ chain of the first instance,
an address of the union ledger. -/
theorem zero_mem_constructionAddresses : Adrs.zero ∈ constructionAddresses vp256s := by
  have h := wotsChainAdrs_setHashAddress_mem_constructionAddresses
    (vp := vp256s) ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩ ⟨0, by decide⟩
    (t := 0) (by decide)
  exact h

/-- The all-zero public seed. -/
def zeroSeed : (shakeCore vp256s).PkSeed := Adrs.zero.toVector

/-- **A weak seed.** At SLH-DSA-SHAKE-256s every public key at the all-zero public seed is weak:
the seed is the key of the all-zero address. -/
theorem isWeakKey_zeroSeed (r : (shakeCore vp256s).Y) : IsWeakKey vp256s ⟨zeroSeed, r⟩ := by
  rw [isWeakKey_iff_of_n_eq_32 rfl]
  refine ⟨Adrs.zero, .inl zero_mem_constructionAddresses, ?_⟩
  change Adrs.toVector Adrs.zero = bytesOfList 32 (Adrs.toVector Adrs.zero).toList
  rw [bytesOfList_toList]

/-- The weak-key mass of the all-zero seed is one. -/
example : weakKeyMass vp256s zeroSeed = 1 :=
  (SampleableType.prEvent_uniformSample_eq_one_iff _).2 isWeakKey_zeroSeed

/-- An address carrying the type word `7`, which no SLH-DSA address has. -/
def typeSevenAdrs : Adrs := ⟨0, 0, 7, 0, 0, 0⟩

/-- A public seed carrying the type word `7`. -/
def typeSevenSeed : (shakeCore vp256s).PkSeed := typeSevenAdrs.toVector

/-- **A strong seed.** The type-`7` seed is the key of no honest address: honest addresses have
type at most `6`, and the SHAKE key carries the type word. -/
theorem not_isHonestKey_typeSevenSeed :
    ¬IsHonestKey vp256s (shakeCore vp256s)
      (adrsKeyOfList vp256s (Vector.toList (typeSevenSeed : Bytes 32))) := by
  rintro ⟨a, ha, hk⟩
  have hty : a.type ≤ 6 := by
    rcases ha with ha | ⟨b, -, hb⟩
    · exact (type_le_four_of_mem_constructionAddresses ha).trans (by decide)
    · rcases isSecretKey_of_inl_mem_childAdrs hb with h | h <;> rw [h] <;> decide
  have hk' : Adrs.toVector a = Adrs.toVector typeSevenAdrs := by
    refine hk.trans ?_
    change bytesOfList 32 (Adrs.toVector typeSevenAdrs).toList = _
    rw [bytesOfList_toList]
  have hbytes : a.toBytes = typeSevenAdrs.toBytes := by
    simpa [Adrs.toVector] using congrArg Vector.toList hk'
  obtain ⟨-, -, htype, -⟩ := toBytes_blocks hbytes
  have h := congrArg toInt htype
  simp only [Adrs.toBytesBE, toInt_toByte_mod, typeSevenAdrs] at h
  omega

/-- The weak-key mass of the type-`7` seed is zero. -/
example : weakKeyMass vp256s typeSevenSeed = 0 :=
  weakKeyMass_eq_zero_of_n_eq_32 rfl not_isHonestKey_typeSevenSeed

/-- The run at the type-`7` seed has no weak public key, against every adversary. -/
example (optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y)
    (adv : UnforgeableAdversary
      (romScheme (shakeCore vp256s) (Equiv.refl _) optRand (pure typeSevenSeed))) :
    Pr{let z ← romSchemeRun (shakeCore vp256s) (Equiv.refl _) optRand (pure typeSevenSeed)
        adv}[IsWeakKey vp256s z.1.pk] = 0 :=
  prEvent_romSchemeRun_isWeakKey_eq_zero_of_n_eq_32
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl _ _
    not_isHonestKey_typeSevenSeed
    adv

/-! ## A weak key at SLH-DSA-SHAKE-128s -/

/-- The all-zero 16-byte string. -/
def zero16 : Bytes 16 := Vector.replicate 16 0

/-- At SLH-DSA-SHAKE-128s the public key with all-zero seed and root is weak: `PK.seed ‖ PK.root`
is the all-zero address's key. -/
example : IsWeakKey vp128s ⟨zero16, zero16⟩ := by
  refine ⟨Adrs.zero, .inl ?_, ?_⟩
  · exact wotsChainAdrs_setHashAddress_mem_constructionAddresses
      (vp := vp128s) ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩ ⟨0, by decide⟩
      (t := 0) (by decide)
  · apply Vector.toList_inj.mp
    change Adrs.zero.toBytes = (bytesOfList 32 (zero16.toList ++ zero16.toList)).toList
    rw [toList_bytesOfList_of_le (by decide)]
    decide

end SLHDSA.WeakKeyBoundTest
