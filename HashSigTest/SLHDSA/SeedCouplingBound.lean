/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.SeedCouplingBound
public import HashSig.SLHDSA.Security.KeySeparation
public import HashSig.SLHDSA.Concrete.Codec

/-!
# The hidden-seed bound at the shipped bundles

`prEvent_romSchemeRun_pure_le_add` holds at every SHAKE bundle and at the SHA2-128-24
compatibility bundle `Concrete.shaPrimitives`, with both of its side conditions discharged: key
separation by `Concrete.keySeparated_shakePrimitives` and `Concrete.keySeparated_shaPrimitives`,
and `|Y| ≤ |SK.prf|` because both carriers are byte vectors of the same width. The loss is
`qh / 256 ^ n` (`natCard_shakePrimitives_y`), and `qh / 256 ^ 16` at the compatibility bundle
(`natCard_shaPrimitives_y`), so the bound is not vacuous.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.SeedCouplingBoundTest

open Security

/-- The node type of the SHAKE bundle has `256 ^ n` elements. -/
theorem natCard_shakePrimitives_y (p : Params) :
    Nat.card (Concrete.shakePrimitives p).core.Y = 256 ^ p.n := by
  change Nat.card (Vector UInt8 p.n) = 256 ^ p.n
  rw [Nat.card_congr (arrayVectorEquivFin UInt8 p.n), Nat.card_fun, Nat.card_eq_fintype_card,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

/-- The hidden-seed bound at a SHAKE bundle, with key separation and `|Y| ≤ |SK.prf|`
discharged: the loss is `qh / 256 ^ n`. -/
theorem prEvent_romSchemeRun_pure_le_add_shake (vp : ValidatedParams)
    (e : (Concrete.shakePrimitives vp.params).core.SkSeed ≃
      (Concrete.shakePrimitives vp.params).core.Y)
    (optRand : PublicKeyCore (Concrete.shakePrimitives vp.params).core →
      ProbComp (Concrete.shakePrimitives vp.params).core.Y)
    (pkSeed : (Concrete.shakePrimitives vp.params).core.PkSeed)
    {adv : UnforgeableAdversary
      (romScheme (Concrete.shakePrimitives vp.params).core e optRand (pure pkSeed))}
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs)
    (Q : RomOutcome vp (Concrete.shakePrimitives vp.params).core ×
      (hashSpec (Concrete.shakePrimitives vp.params).core).QueryCache → Prop) :
    Pr{let z ← romSchemeRun (Concrete.shakePrimitives vp.params).core e optRand (pure pkSeed)
        adv}[Q z] ≤
      Pr{let s ← $ᵗ ((Concrete.shakePrimitives vp.params).core.SkSeed ×
            (Concrete.shakePrimitives vp.params).core.SkPrf)
         let z ← (simulateQ (SecretEncoding.idealImpl
             (hashSpec (Concrete.shakePrimitives vp.params).core)
             (DeriveQuery (Concrete.shakePrimitives vp.params).core)
             (Concrete.shakePrimitives vp.params).core.Y)
           (unforgeableTranscriptExperiment
             (deriveAdversary (Concrete.shakePrimitives vp.params).core adv
               pkSeed))).run (∅, ∅)}[
        Q (DeriveOutcome.fill (Concrete.shakePrimitives vp.params).core s z.1,
          (secretEncoding (Concrete.shakePrimitives vp.params).core e pkSeed).merge s
            z.2)] +
        qh * ((256 ^ vp.params.n : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [← natCard_shakePrimitives_y]
  exact prEvent_romSchemeRun_pure_le_add
    (Concrete.keySeparated_shakePrimitives vp.params) le_rfl e optRand pkSeed hadv Q

/-- The core of the SHA2-128-24 compatibility bundle, indexed by its validated parameters. -/
abbrev shaCore : CorePrimitives Concrete.sha128_24Vp.params := Concrete.shaPrimitives.core

/-- The node type of the SHA2-128-24 compatibility bundle has `256 ^ 16` elements. -/
theorem natCard_shaPrimitives_y : Nat.card shaCore.Y = 256 ^ 16 := by
  change Nat.card (Vector UInt8 16) = 256 ^ 16
  rw [Nat.card_congr (arrayVectorEquivFin UInt8 16), Nat.card_fun, Nat.card_eq_fintype_card,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

/-- The hidden-seed bound at the SHA2-128-24 compatibility bundle, with key separation and
`|Y| ≤ |SK.prf|` discharged: the loss is `qh / 256 ^ 16`. -/
theorem prEvent_romSchemeRun_pure_le_add_sha (e : shaCore.SkSeed ≃ shaCore.Y)
    (optRand : PublicKeyCore shaCore → ProbComp shaCore.Y) (pkSeed : shaCore.PkSeed)
    {adv : UnforgeableAdversary (romScheme shaCore e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs)
    (Q : RomOutcome Concrete.sha128_24Vp shaCore × (hashSpec shaCore).QueryCache → Prop) :
    Pr{let z ← romSchemeRun shaCore e optRand (pure pkSeed) adv}[Q z] ≤
      Pr{let s ← $ᵗ (shaCore.SkSeed × shaCore.SkPrf)
         let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec shaCore) (DeriveQuery shaCore)
             shaCore.Y)
           (unforgeableTranscriptExperiment (deriveAdversary shaCore adv pkSeed))).run (∅, ∅)}[
        Q (DeriveOutcome.fill shaCore s z.1, (secretEncoding shaCore e pkSeed).merge s z.2)] +
        qh * ((256 ^ 16 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [← natCard_shaPrimitives_y]
  exact prEvent_romSchemeRun_pure_le_add Concrete.keySeparated_shaPrimitives le_rfl e optRand
    pkSeed hadv Q

end SLHDSA.SeedCouplingBoundTest
