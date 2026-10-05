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
sampled independently of every public answer, plus `qh / |Y|` for a forger with hash budget `qh`.

* `prEvent_mem_range_secretEncoding_enc_le`: under uniform secret seeds, a public point encodes a
  derivation with probability at most `1 / |Y|`, when `|Y| ≤ |SK.prf|`. A tweakable-hash point
  `thash _ _ [y]` pins `SK.seed` to `e.symm y`; a `PRF_msg` point pins `SK.prf`; no other point
  encodes a derivation.
* `prEvent_romSchemeRun_pure_le_add`: under key separation and the hash budget `qh`, an event of
  the run and its final cache is at most the event, read on the rebuilt transcript and the merged
  cache, in the ideal game under uniform secret seeds, plus `qh / |Y|`.
* `prEvent_romSchemeRun_pure_eq_coupledImpl_extendState`: an event of the run is the same event of
  the coupled real game extended by any passive auxiliary state, read on the rebuilt transcript
  and the merged split state.
* `prEvent_coupledImpl_extendState_deriveAdversary_le_add`: an event of the extended coupled
  game's output, split state and auxiliary state is at most the same event of the ideal game
  extended by the same auxiliary state, plus `qh / |Y|`.

The last two together bound events that read bookkeeping carried alongside the run, such as a log
of the queries and of the derivation table at each query, which the run itself does not expose.

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
        qh * (Nat.card core.Y : ℝ≥0∞)⁻¹ :=
  (prEvent_romSchemeRun_pure_eq core e optRand pkSeed adv Q).trans_le
    ((secretEncoding core e pkSeed).prEvent_realImpl_le_add_mul
      (prEvent_mem_range_secretEncoding_enc_le e pkSeed hcard)
      (isDerivablePublicQuery_enc core e pkSeed)
      (isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary hsep pkSeed hadv) _)

/-! ## Events that read an auxiliary state -/

/-- **The run of SLH-DSA at a public seed is the extended coupled game, projected.** For any
passive auxiliary state with update `aux s`, which may read the secret seeds, the query, its
answer, the split state before and after the step and its own previous value, the run draws the
secret seeds `s` uniformly, runs the secret-free experiment in the coupled real game at `s`
extended by `aux s`, and rebuilds the transcript with `s` and the cache by merging the final
split state. -/
theorem romSchemeRun_pure_eq_coupledImpl_extendState (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))) {Q : Type} (r₀ : Q)
    (aux : core.SkSeed × core.SkPrf → (t : (deriveSpec core).Domain) →
      SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y →
      (deriveSpec core).Range t →
      SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y → Q → Q) :
    romSchemeRun core e optRand (pure pkSeed) adv = do
      let s ← $ᵗ (core.SkSeed × core.SkPrf)
      let z ← (simulateQ (((secretEncoding core e pkSeed).coupledImpl s).extendState
        fun t st u st' r ↦ aux s t st.1 u st'.1 r)
          (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run
            (((∅, ∅), false), r₀)
      return (DeriveOutcome.fill core s z.1, (secretEncoding core e pkSeed).merge s z.2.1.1) := by
  rw [romSchemeRun_pure_eq]
  refine bind_congr fun s ↦ ?_
  have h := (secretEncoding core e pkSeed).map_run_simulateQ_coupledImpl_extendState s
    (fun t st u st' r ↦ aux s t st.1 u st'.1 r)
    (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed)) ((∅, ∅), false) r₀
  rw [SecretEncoding.merge_empty] at h
  rw [← h, bind_map_left]
  rfl

/-- An event of the run of SLH-DSA at a public seed has the probability of the event, read on the
rebuilt transcript and the merged split state, in the coupled real game extended by any passive
auxiliary state, under uniform secret seeds. -/
theorem prEvent_romSchemeRun_pure_eq_coupledImpl_extendState (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))) {Q : Type} (r₀ : Q)
    (aux : core.SkSeed × core.SkPrf → (t : (deriveSpec core).Domain) →
      SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y →
      (deriveSpec core).Range t →
      SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y → Q → Q)
    (P : RomOutcome vp core × (hashSpec core).QueryCache → Prop) :
    Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[P z] =
      Pr{let s ← $ᵗ (core.SkSeed × core.SkPrf)
         let z ← (simulateQ (((secretEncoding core e pkSeed).coupledImpl s).extendState
           fun t st u st' r ↦ aux s t st.1 u st'.1 r)
             (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run
               (((∅, ∅), false), r₀)}[
        P (DeriveOutcome.fill core s z.1, (secretEncoding core e pkSeed).merge s z.2.1.1)] := by
  rw [romSchemeRun_pure_eq_coupledImpl_extendState e optRand pkSeed adv r₀ aux]
  simp only [bind_assoc, pure_bind]

/-- **The extended coupled game of SLH-DSA at a public seed against the extended ideal game.**
Under key separation, for a forger with hash budget `qh` and `|Y| ≤ |SK.prf|`, and for any
passive auxiliary state with update `aux s`, which may read the secret seeds, the query, its
answer, the split state before and after the step (including the derivation table) and its own
previous value: an event of the secret seeds and of the extended coupled game's output, split
state and auxiliary state is at most the same event of the ideal game extended by `aux s`, under
uniform secret seeds, plus `qh / |Y|`. -/
theorem prEvent_coupledImpl_extendState_deriveAdversary_le_add (hsep : core.KeySeparated)
    (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf) (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) {Q : Type} (r₀ : Q)
    (aux : core.SkSeed × core.SkPrf → (t : (deriveSpec core).Domain) →
      SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y →
      (deriveSpec core).Range t →
      SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y → Q → Q)
    (P : core.SkSeed × core.SkPrf → DeriveOutcome core ×
      SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y × Q → Prop) :
    Pr{let s ← $ᵗ (core.SkSeed × core.SkPrf)
       let z ← (simulateQ (((secretEncoding core e pkSeed).coupledImpl s).extendState
         fun t st u st' r ↦ aux s t st.1 u st'.1 r)
           (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run
             (((∅, ∅), false), r₀)}[P s (z.1, z.2.1.1, z.2.2)] ≤
      Pr{let s ← $ᵗ (core.SkSeed × core.SkPrf)
         let z ← (simulateQ
           ((SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core) core.Y).extendState
             (aux s))
           (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run
             ((∅, ∅), r₀)}[P s z] +
        qh * (Nat.card core.Y : ℝ≥0∞)⁻¹ :=
  (secretEncoding core e pkSeed).prEvent_coupledImpl_extendState_le_add_mul r₀ aux
    (prEvent_mem_range_secretEncoding_enc_le e pkSeed hcard)
    (isDerivablePublicQuery_enc core e pkSeed)
    (isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary hsep pkSeed hadv) P

end SLHDSA.Security
