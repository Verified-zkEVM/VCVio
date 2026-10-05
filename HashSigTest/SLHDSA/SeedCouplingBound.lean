/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.SeedCouplingBound
public import HashSig.SLHDSA.Security.KeySeparation

/-!
# The hidden-seed bound at the SHAKE bundles

`prEvent_romSchemeRun_pure_le_add` holds at every SHAKE bundle with both of its side
conditions discharged: key separation by `Concrete.keySeparated_shakePrimitives`, and
`|Y| ≤ |SK.prf|` because both carriers are `n`-byte vectors. The loss is `qh / 256 ^ n`
(`natCard_shakePrimitives_y`), so the bound is not vacuous.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.SeedCouplingBoundTest

open Security

/-- The node type of the SHAKE bundle samples as `n`-byte vectors. -/
instance (p : Params) : SampleableType (Concrete.shakePrimitives p).Y :=
  inferInstanceAs (SampleableType (Bytes p.n))

/-- The secret seed of the SHAKE bundle samples as `n`-byte vectors. -/
instance (p : Params) : SampleableType (Concrete.shakePrimitives p).SkSeed :=
  inferInstanceAs (SampleableType (Bytes p.n))

/-- The message-`PRF` key of the SHAKE bundle samples as `n`-byte vectors. -/
instance (p : Params) : SampleableType (Concrete.shakePrimitives p).SkPrf :=
  inferInstanceAs (SampleableType (Bytes p.n))

/-- Node equality of the SHAKE bundle. -/
instance (p : Params) : DecidableEq (Concrete.shakePrimitives p).Y :=
  inferInstanceAs (DecidableEq (Bytes p.n))

/-- Public-seed equality of the SHAKE bundle. -/
instance (p : Params) : DecidableEq (Concrete.shakePrimitives p).PkSeed :=
  inferInstanceAs (DecidableEq (Bytes p.n))

/-- Message-`PRF` key equality of the SHAKE bundle. -/
instance (p : Params) : DecidableEq (Concrete.shakePrimitives p).SkPrf :=
  inferInstanceAs (DecidableEq (Bytes p.n))

/-- Address-key equality of the SHAKE bundle, whose key is the full 32-byte address. -/
instance (p : Params) : DecidableEq (Concrete.shakePrimitives p).AdrsKey :=
  inferInstanceAs (DecidableEq (Bytes 32))

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

end SLHDSA.SeedCouplingBoundTest
