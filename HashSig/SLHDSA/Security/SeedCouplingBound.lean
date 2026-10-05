/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.SeedCouplingQueries
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# The hidden-seed bound for the run of SLH-DSA

At a fixed public seed `pkSeed`, the run of SLH-DSA in the random-oracle model is the real
hidden-seed game of the secret-free experiment, averaged over uniform secret seeds
(`HashSig.SLHDSA.Security.SeedCoupling`). This module applies the averaged hidden-seed bound of
`VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed` to it: an event of the run is at most the
same event of the *ideal* game, in which the secret values and randomizers are entries of a table
sampled independently of every public answer, plus `1 / |Y|` times the expected number of
derivable public queries (`IsDerivablePublicQuery core pkSeed`) of the ideal run, and so, under
key separation, plus `qh / |Y|` for a forger with hash budget `qh`.

* `prEvent_mem_range_secretEncoding_enc_le`: under uniform secret seeds, a public point encodes a
  derivation with probability at most `1 / |Y|`, when `|Y| ≤ |SK.prf|`. A tweakable-hash point
  `thash _ _ [y]` pins `SK.seed` to `e.symm y`; a `PRF_msg` point pins `SK.prf`; no other point
  encodes a derivation.
* `prEvent_romSchemeRun_pure_le_add_mul_expectedSimulatedQueryCount`: an event of the run and its
  final cache is at most the event, read on the rebuilt transcript and the merged cache, in the
  ideal game under uniform secret seeds, plus `1 / |Y|` times the expected number of derivable
  public queries of the transcript experiment in the ideal game. The count is of every derivable
  public query of the experiment, honest ones included; under key separation only the forger
  makes them (`isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary`). It needs neither
  key separation nor a query budget: the count is of the secret-free ideal run, so further losses
  charged against the queries of that run share it.
* `prEvent_romSchemeRun_pure_le_add`: under key separation and the hash budget `qh`, the same
  bound with the loss `qh / |Y|`.

## Scope

* The statements are per public seed: the scheme is `romScheme core e optRand (pure pkSeed)`.
* Nothing here is quantum.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.Security

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## A public point encodes a derivation with probability at most `1 / |Y|` -/

/-- **A public point encodes a derivation under uniform secret seeds with probability at most
`1 / |Y|`.** At a tweakable-hash point `thash _ _ [y]` the secret seed is `e.symm y`, which has
probability `1 / |SK.seed| = 1 / |Y|`; at a `PRF_msg` point the message-`PRF` key is fixed, which
has probability `1 / |SK.prf| ≤ 1 / |Y|`; no other point encodes a derivation. -/
theorem prEvent_mem_range_secretEncoding_enc_le [SampleableType core.SkSeed]
    [SampleableType core.SkPrf] (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed)
    (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf) (t : (hashSpec core).Domain) :
    Pr{let s ← $ᵗ (core.SkSeed × core.SkPrf)}[
      t ∈ Set.range ((secretEncoding core e pkSeed).enc s)] ≤ (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
  rcases t with (⟨pk, k, xs⟩ | t) | ⟨sp, o, msg⟩
  · refine SampleableType.prEvent_uniformSample_prod_le_of_forall_snd _ fun sp ↦ ?_
    calc _ ≤ Pr{let x ← $ᵗ core.SkSeed}[[e x] = xs] := prEvent_mono _ _ _ fun x ↦ by
          rintro ⟨k' | ⟨o, msg⟩, h⟩
          · simp only [secretEncoding_enc_inl, Sum.inl.injEq, PublicHashQuery.thash.injEq] at h
            exact h.2.2
          · cases h
      _ ≤ (Nat.card core.SkSeed : ℝ≥0∞)⁻¹ := SampleableType.prEvent_uniformSample_apply_eq_le
          (fun x x' h ↦ e.injective (List.singleton_injective h)) xs
      _ = _ := by rw [Nat.card_congr e]
  · rw [(SampleableType.prEvent_uniformSample_eq_zero_iff _).2 ?_]
    · exact zero_le
    rintro s ⟨k | ⟨o, msg⟩, h⟩ <;> cases h
  · refine SampleableType.prEvent_uniformSample_prod_le_of_forall_fst _ fun x ↦ ?_
    calc _ ≤ Pr{let y ← $ᵗ core.SkPrf}[y = sp] := prEvent_mono _ _ _ fun y ↦ by
          rintro ⟨k | ⟨o', msg'⟩, h⟩
          · cases h
          · simp only [secretEncoding_enc_inr, Sum.inr.injEq, PrfMsgQuery.mk.injEq] at h
            exact h.1
      _ = (Nat.card core.SkPrf : ℝ≥0∞)⁻¹ :=
          SampleableType.prEvent_uniformSample_eq_singleton_natCard sp
      _ ≤ _ := ENNReal.inv_le_inv.2 (by exact_mod_cast hcard)

/-! ## The bound for the run -/

variable [SampleableType core.Y] [DecidableEq core.Y] [SampleableType core.SkSeed]
  [SampleableType core.SkPrf] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- **The run of SLH-DSA at a public seed against the ideal game, charged in expectation.** For
`|Y| ≤ |SK.prf|`, an event of the run and its final cache is at most the event, read on the
transcript rebuilt with the secret seeds `s` and on the merged cache, when `s` is drawn uniformly
and the secret-free experiment runs in the ideal game, plus `1 / |Y|` times the expected number
of derivable public queries of that ideal run. The count is of every derivable public query of
the experiment, honest ones included; under key separation only the forger makes them
(`isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary`). In the ideal game every secret
value and randomizer is an entry of a table sampled independently of the public answers. -/
theorem prEvent_romSchemeRun_pure_le_add_mul_expectedSimulatedQueryCount
    (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf) (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))
    (Q : RomOutcome vp core × (hashSpec core).QueryCache → Prop) :
    Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[Q z] ≤
      Pr{let s ← $ᵗ (core.SkSeed × core.SkPrf)
         let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core) core.Y)
           (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run (∅, ∅)}[
        Q (DeriveOutcome.fill core s z.1, (secretEncoding core e pkSeed).merge s z.2)] +
        (Nat.card core.Y : ℝ≥0∞)⁻¹ *
          expectedSimulatedQueryCount
            (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core) core.Y)
            (IsDerivablePublicQuery core pkSeed)
            (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed)) (∅, ∅) :=
  (prEvent_romSchemeRun_pure_eq core e optRand pkSeed adv Q).trans_le
    ((secretEncoding core e pkSeed).prEvent_realImpl_le_add_mul_expectedSimulatedQueryCount
      (prEvent_mem_range_secretEncoding_enc_le e pkSeed hcard)
      (isDerivablePublicQuery_enc core e pkSeed) _ _)

/-- **The run of SLH-DSA at a public seed against the ideal game.** Under key separation, for a
forger with hash budget `qh` and `|Y| ≤ |SK.prf|`, an event of the run and its final cache is at
most the event, read on the transcript rebuilt with the secret seeds `s` and on the merged cache,
when `s` is drawn uniformly and the secret-free experiment runs in the ideal game, plus
`qh / |Y|`. In the ideal game every secret value and randomizer is an entry of a table sampled
independently of the public answers. -/
theorem prEvent_romSchemeRun_pure_le_add (hsep : core.KeySeparated)
    (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf) (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs)
    (Q : RomOutcome vp core × (hashSpec core).QueryCache → Prop) :
    Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[Q z] ≤
      Pr{let s ← $ᵗ (core.SkSeed × core.SkPrf)
         let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core) core.Y)
           (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run (∅, ∅)}[
        Q (DeriveOutcome.fill core s z.1, (secretEncoding core e pkSeed).merge s z.2)] +
        qh * (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
  refine (prEvent_romSchemeRun_pure_le_add_mul_expectedSimulatedQueryCount hcard e optRand
    pkSeed adv Q).trans (add_le_add le_rfl ?_)
  exact mul_expectedSimulatedQueryCount_le_of_isQueryBoundP _ _
    (isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary hsep pkSeed hadv) _ _

end SLHDSA.Security
