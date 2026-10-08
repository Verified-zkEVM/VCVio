/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.Transport
public import HashSig.SLHDSA.Security.LabBudget
public import HashSig.SLHDSA.Security.LabEquiv.Experiment

/-!
# The joint target-collision and hidden-value bound

For SLH-DSA in the three-oracle random-oracle model (`romScheme`) at a fixed public seed
`pkSeed`, under the key discipline (`CorePrimitives.KeyDiscipline`) and `|Y| ≤ |SK.prf|`, a forger
with hash budget `qh` makes the run (`romSchemeRun`) fire a same-key target collision
(`RunTargetCollision`) or a hidden-value hit (`RunHiddenHit`) with probability at most
`2 (qh + V) / |Y|`, where `V = GeneralScheme.verifyInternalQueryBound` bounds the verifier's
queries (`prEvent_romSchemeRun_runTargetCollision_or_runHiddenHit_le`). The forger guessing a
secret seed is inside this bound: it is charged by the same potential, not added.

The forging advantage is then bounded in two forms, both per public seed:

* `unforgeableAdvantage_romScheme_pure_le_add_idealDraw`: at most `2 (qh + V) / |Y|` plus the
  probability of interleaved-target coverage (`RunItsrCovered`) in the ideal hidden-seed game
  `idealDraw` (`HashSig.SLHDSA.Security.SeedCouplingBound`), read on the rebuilt transcript and
  the merged cache. The first game hop is applied to the whole bad event before the union is
  split, so a seed guess is charged once, inside the joint term, and the coverage term is a
  probability of a game in which every secret value and randomizer is a table entry sampled
  independently of the public answers. Coverage reads only the `H_msg` answers, which merging
  leaves as they are in the ideal run's public cache, so the coverage term is the probability of
  coverage in the secret-free ideal run alone, read at any fixed seeds
  (`prEvent_idealDraw_runItsrCovered_eq`).
* `unforgeableAdvantage_romScheme_pure_le_add`: at most `2 (qh + V) / |Y|` plus the probability of
  `RunItsrCovered` in the run itself. For deterministic signing at the FIPS 205 parameter sets,
  this run-level coverage term cannot be bounded at the size of the coverage term of
  `securityBound`: a forger that guesses `SK.prf` through its `PRF_msg` queries predicts every
  randomizer and grinds `H_msg` until the digests it gets signed cover its target, so coverage in
  the run is at least about as likely as that guess (≈ `qh / |SK.prf|`), which the joint term
  already charges. The coverage term of the ideal-game form is free of that guess: there every
  randomizer is sampled independently of the public answers.

## The chain of games

* The run is the real hidden-seed game under uniform secret seeds
  (`prEvent_romSchemeRun_pure_eq`), which is at most the ideal game read on the rebuilt cache, or
  a public point encoding a derivation (`SecretEncoding.prEvent_bind_realImpl_le_or`). Together
  these are the first hop, `prEvent_romSchemeRun_pure_le_prEvent_idealDraw_or`, stated on
  `idealDraw`.
* The ideal game is at most the eager relabelled game of the canonical graph `slhGraph core
  pkSeed`, or a conflict (`CanonicalGraph.prEvent_idealImpl_le_eagerImpl_liftComp`).
* In the eager game the lifted secret-free experiment is the lab experiment
  (`prEvent_eagerImpl_liftComp_eq_labExperiment`).
* The eager game is at most the deferred game after the end fill, or a conflict
  (`CanonicalGraph.prEvent_eagerImpl_le_deferredImpl_empty`), and the secret seeds are drawn after
  the fill (`CanonicalGraph.deferredFillDraw`).

The last three hops are `prEvent_idealDraw_le_prEvent_deferredFillDraw`; with the first hop they
give `prEvent_romSchemeRun_le_prEvent_deferredFillDraw`, which bounds an event of the run by any
event of the deferred run that the pointwise transport reaches.

For the target collision and the hidden-value hit, the transport reaches a conflict, a target
collision at a node key, or a seed hazard of the final public cache
(`conflict_or_tcHazard_or_exists_isSome_of_mem_support_deferredFillDraw`), and the joint potential
bounds these by `2 (qh + V) / |Y|`
(`CanonicalGraph.NodeKeys.prEvent_deferredFillDraw_le_of_budget`), under the pathwise budget of the
lab experiment
(`two_mul_encard_keyEntries_div_add_seedCharge_le_of_mem_support`) and the seed charge
(`prEvent_exists_isSome_apply_secretEncoding_enc_le`). This is the ideal-game joint bound
`prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_exists_isSome_le`, from which both the
bound for the run and the ideal-game form of the advantage bound follow.

## Scope

* The bounds are per public seed: the scheme is `romScheme core e optRand (pure pkSeed)`.
* Interleaved-target coverage is not bounded here; it remains a probability, in the ideal
  hidden-seed game in `unforgeableAdvantage_romScheme_pure_le_add_idealDraw` and in the run in
  `unforgeableAdvantage_romScheme_pure_le_add`.
* The losses of the faithfulness step relating the three-oracle model to the byte-level scheme
  over a single SHAKE256 are not included.
* Nothing here is quantum.
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal

namespace SLHDSA.Security

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}
  [SampleableType core.Y] [DecidableEq core.Y] [SampleableType core.SkSeed]
  [SampleableType core.SkPrf] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- **The ideal hidden-seed game is bounded on the deferred lab experiment.** Under the key
discipline, an event `F` of the seeds and the outcome of `idealDraw` at public seed `pkSeed` has
probability at most that of `F` or a conflict in the deferred run of the lab experiment, its end
fill and a draw of secret seeds, with `F` read at the drawn seeds, the deferred outcome and the
split state of the filled state. -/
theorem prEvent_idealDraw_le_prEvent_deferredFillDraw (hd : core.KeyDiscipline vp)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))
    (F : core.SkSeed × core.SkPrf →
      DeriveOutcome core × SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y →
        Prop) :
    Pr{let w ← idealDraw e optRand pkSeed adv}[F w.1 w.2] ≤
      Pr{let w ← (slhGraph core pkSeed).deferredFillDraw ($ᵗ (core.SkSeed × core.SkPrf))
                (labExperiment core adv pkSeed)}[
        F w.2.2 (w.1.1, (slhGraph core pkSeed).toSplitCache w.2.1) ∨
          (slhGraph core pkSeed).Conflict w.2.1] := by
  set G := slhGraph core pkSeed
  set ms := ($ᵗ (core.SkSeed × core.SkPrf) : ProbComp _)
  set oa := unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed)
  set lab := labExperiment core adv pkSeed
  have hs : ∀ s, Pr{let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec core)
        (DeriveQuery core) core.Y) oa).run (∅, ∅)}[F s z] ≤
      Pr{let z ← (simulateQ G.deferredImpl lab).run ((∅, ∅), [])
         let st ← RelabelState.endFill z.2}[F s (z.1, G.toSplitCache st) ∨ G.Conflict st] := by
    intro s
    calc _ ≤ Pr{let z ← (simulateQ G.eagerImpl (liftComp oa (labSpec core))).run (∅, ∅)}[
            F s (z.1, G.toSplitCache z.2) ∨ G.Conflict z.2] :=
          G.prEvent_idealImpl_le_eagerImpl_liftComp oa (F s)
      _ = Pr{let z ← (simulateQ G.eagerImpl lab).run (∅, ∅)}[
            F s (z.1, G.toSplitCache z.2) ∨ G.Conflict z.2] :=
          prEvent_eagerImpl_liftComp_eq_labExperiment core hd pkSeed adv (∅, ∅) _
      _ ≤ Pr{let z ← (simulateQ G.deferredImpl lab).run ((∅, ∅), [])
                let st ← RelabelState.endFill z.2}[
            (F s (z.1, G.toSplitCache st) ∨ G.Conflict st) ∨ G.Conflict st] :=
          G.prEvent_eagerImpl_le_deferredImpl_empty lab _
      _ = _ := by simp only [or_assoc, or_self]
  let _ : MeasurableSpace (core.SkSeed × core.SkPrf) := ⊤
  have hswap : Pr{let w ← G.deferredFillDraw ms lab}[F w.2.2 (w.1.1, G.toSplitCache w.2.1) ∨
      G.Conflict w.2.1] = Pr{let s ← ms; let zst ← ((simulateQ G.deferredImpl lab).run
        ((∅, ∅), []) >>= fun z ↦ (z, ·) <$> RelabelState.endFill z.2)}[
        F s (zst.1.1, G.toSplitCache zst.2) ∨ G.Conflict zst.2] := by
    rw [← OracleComp.prEvent_bind_bind_swap]
    simp only [CanonicalGraph.deferredFillDraw, bind_assoc, bind_map_left, pure_bind]
  rw [prEvent_idealDraw_eq, hswap, prEvent_bind_bind_eq_lintegral_of_discrete,
    prEvent_bind_bind_eq_lintegral_of_discrete]
  refine lintegral_mono fun s ↦ (hs s).trans (le_of_eq ?_)
  simp only [bind_assoc, bind_map_left]

/-- **An event of the run is bounded on the deferred lab experiment.** Under the key discipline,
an event `Q` of the run of SLH-DSA in the random-oracle model at public seed `pkSeed` has
probability at most that of an event `H` of the deferred run of the lab experiment, its end fill
and a draw of secret seeds `s`, when `H` holds at every point of that support at which `Q` holds of
the transcript rebuilt with `s` on the cache that the filled state stands for at `s`, the split
state of the filled state holds a point encoding a derivation under `s`, or the filled state is a
conflict. -/
theorem prEvent_romSchemeRun_le_prEvent_deferredFillDraw (hd : core.KeyDiscipline vp)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))
    (Q : RomOutcome vp core × (hashSpec core).QueryCache → Prop)
    (H : (DeriveOutcome core × LabState core × List (DeriveQuery core ⊕ NodeKey core)) ×
      LabState core × (core.SkSeed × core.SkPrf) → Prop)
    (hH : ∀ w ∈ support ((slhGraph core pkSeed).deferredFillDraw ($ᵗ (core.SkSeed × core.SkPrf))
        (labExperiment core adv pkSeed)),
      ((Q (DeriveOutcome.fill core w.2.2 w.1.1, (secretEncoding core e pkSeed).merge w.2.2
          ((slhGraph core pkSeed).toSplitCache w.2.1)) ∨
        ∃ x, (((slhGraph core pkSeed).toSplitCache w.2.1).1
          ((secretEncoding core e pkSeed).enc w.2.2 x)).isSome) ∨
        (slhGraph core pkSeed).Conflict w.2.1) → H w) :
    Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[Q z] ≤
      Pr{let w ← (slhGraph core pkSeed).deferredFillDraw ($ᵗ (core.SkSeed × core.SkPrf))
                (labExperiment core adv pkSeed)}[H w] :=
  (prEvent_romSchemeRun_pure_le_prEvent_idealDraw_or e optRand pkSeed adv Q).trans
    ((prEvent_idealDraw_le_prEvent_deferredFillDraw hd e optRand pkSeed adv fun s z ↦
      Q (DeriveOutcome.fill core s z.1, (secretEncoding core e pkSeed).merge s z.2) ∨
        ∃ x, (z.2.1 ((secretEncoding core e pkSeed).enc s x)).isSome).trans
      (prEvent_mono_of_support _ _ _ hH))

/-- **The joint bound in the ideal hidden-seed game, per public seed.** Under the key discipline
and `|Y| ≤ |SK.prf|`, for a forger with hash budget `qh`, `idealDraw` at public seed `pkSeed`
fires, on the transcript rebuilt with the drawn seeds and the cache merged under them, a same-key
target collision or a hidden-value hit, or holds in its final public cache a point encoding a
derivation under the drawn seeds, with probability at most `2 (qh + V) / |Y|`, with `V` the
verifier's query bound. -/
theorem prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_exists_isSome_le
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))}
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    Pr{let w ← idealDraw e optRand pkSeed adv}[
      (RunTargetCollision core e (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2) ∨
        RunHiddenHit core e (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)) ∨
      ∃ x, (w.2.2.1 ((secretEncoding core e pkSeed).enc w.1 x)).isSome] ≤
    2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) / Nat.card core.Y :=
  (prEvent_idealDraw_le_prEvent_deferredFillDraw hd e optRand pkSeed adv fun s z ↦
    (RunTargetCollision core e (DeriveOutcome.fill core s z.1,
        (secretEncoding core e pkSeed).merge s z.2) ∨
      RunHiddenHit core e (DeriveOutcome.fill core s z.1,
        (secretEncoding core e pkSeed).merge s z.2)) ∨
    ∃ x, (z.2.1 ((secretEncoding core e pkSeed).enc s x)).isSome).trans <|
  (prEvent_mono_of_support _ _
    (fun w ↦ (slhGraph core pkSeed).Conflict w.2.1 ∨ (slhNodeKeys core pkSeed).TCHazard w.2.1 ∨
      ∃ x, (w.2.1.1 ((secretEncoding core e pkSeed).enc w.2.2 x)).isSome)
    fun _ hw h ↦ conflict_or_tcHazard_or_exists_isSome_of_mem_support_deferredFillDraw hd hw
      h).trans <|
  (slhNodeKeys core pkSeed).prEvent_deferredFillDraw_le_of_budget _
    (fun s C ↦ ∃ x, (C ((secretEncoding core e pkSeed).enc s x)).isSome) (seedCharge core pkSeed)
    (prEvent_exists_isSome_apply_secretEncoding_enc_le e pkSeed hcard) _ _
    (ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (by
      simp only [ne_eq, Nat.cast_eq_zero, Nat.card_ne_zero]
      exact ⟨inferInstance, inferInstance⟩))
    (fun _ hz ↦ two_mul_encard_keyEntries_div_add_seedCharge_le_of_mem_support
      hd.keySeparated hadv hz)

/-- **The joint target-collision and hidden-value bound, per public seed.** Under the key
discipline and `|Y| ≤ |SK.prf|`, for a forger with hash budget `qh`, the run of SLH-DSA in the
random-oracle model at public seed `pkSeed` fires a same-key target collision or a hidden-value hit
with probability at most `2 (qh + V) / |Y|`, with `V` the verifier's query bound. The forger
guessing a secret seed is charged inside this bound. Interleaved-target coverage and the
faithfulness step are not included. -/
theorem prEvent_romSchemeRun_runTargetCollision_or_runHiddenHit_le (hd : core.KeyDiscipline vp)
    (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf) (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[
      RunTargetCollision core e z ∨ RunHiddenHit core e z] ≤
    2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) / Nat.card core.Y :=
  (prEvent_romSchemeRun_pure_le_prEvent_idealDraw_or e optRand pkSeed adv _).trans
    (prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_exists_isSome_le hd hcard e optRand
      pkSeed hadv)

/-- **The forging advantage per public seed, up to coverage in the ideal hidden-seed game.**
Under the byte laws, the key discipline and `|Y| ≤ |SK.prf|`, the forging advantage against
SLH-DSA in the random-oracle model at public seed `pkSeed`, of a forger with hash budget `qh`, is at
most `2 (qh + V) / |Y|`, with `V` the verifier's query bound, plus the probability that
`idealDraw` at `pkSeed` fires interleaved-target coverage with a fresh forged message
(`RunItsrCovered`) on the transcript rebuilt with the drawn seeds and the cache merged under them.
The forger guessing a secret seed is charged once, inside the first term. The statement is per
public seed; the coverage term remains a probability in the ideal hidden-seed game and is not
bounded here; the faithfulness step relating the three-oracle model to the byte-level scheme is not
included. -/
theorem unforgeableAdvantage_romScheme_pure_le_add_idealDraw (laws : core.ByteLaws)
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))}
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec core)) adv ≤
      2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) / Nat.card core.Y +
      Pr{let w ← idealDraw e optRand pkSeed adv}[
        RunItsrCovered core (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)] := by
  set E := secretEncoding core e pkSeed
  refine (unforgeableAdvantage_romScheme_le_prEvent_or core laws e optRand (pure pkSeed) adv).trans
    ((prEvent_romSchemeRun_pure_le_prEvent_idealDraw_or e optRand pkSeed adv _).trans ?_)
  refine (prEvent_mono _ _ (fun w ↦ (((RunTargetCollision core e
      (DeriveOutcome.fill core w.1 w.2.1, E.merge w.1 w.2.2) ∨
      RunHiddenHit core e (DeriveOutcome.fill core w.1 w.2.1, E.merge w.1 w.2.2)) ∨
      ∃ x, (w.2.2.1 (E.enc w.1 x)).isSome) ∨
      RunItsrCovered core (DeriveOutcome.fill core w.1 w.2.1, E.merge w.1 w.2.2)))
    fun _ h ↦ by
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)).trans ((prEvent_or_le _ _ _).trans ?_)
  gcongr
  exact prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_exists_isSome_le hd hcard e optRand
    pkSeed hadv

/-- **The coverage term of the ideal hidden-seed game does not depend on the drawn seeds.**
Interleaved-target coverage with a fresh forged message, read in `idealDraw` on the transcript
rebuilt with the drawn seeds and the cache merged under them, has the probability that the
secret-free experiment run alone in the ideal game fires it, read on the transcript rebuilt with
any fixed seeds `s₀` and on the run's final public cache. Coverage reads only `H_msg` answers, and
no `H_msg` point encodes a derivation, so merging leaves them as they are in the public cache. -/
theorem prEvent_idealDraw_runItsrCovered_eq (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))
    (s₀ : core.SkSeed × core.SkPrf) :
    Pr{let w ← idealDraw e optRand pkSeed adv}[
        RunItsrCovered core (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)] =
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core) core.Y)
          (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run (∅, ∅)}[
        RunItsrCovered core (DeriveOutcome.fill core s₀ z.1, z.2.1)] := by
  have hm : ∀ (s : core.SkSeed × core.SkPrf)
      (C : SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y)
      (r : core.Y) (ps : core.PkSeed) (pr : core.Y) (m : List Byte),
      ((secretEncoding core e pkSeed).merge s C).fst (.hmsg r ps pr m) =
        C.1.fst (.hmsg r ps pr m) := fun s C _ _ _ _ ↦ by
    simp only [QueryCache.fst_apply]
    refine (secretEncoding core e pkSeed).merge_apply_of_not_exists s C ?_
    rintro ⟨x | ⟨o, msg⟩, hx⟩ <;> cases hx
  have ho : ∀ (o o' : RomOutcome vp core) (C : (hashSpec core).QueryCache), o.pk = o'.pk →
      o.log = o'.log → o.msg = o'.msg → o.sig = o'.sig →
      (RunItsrCovered core (o, C) ↔ RunItsrCovered core (o', C)) := by
    rintro ⟨pk, sk, log, msg, sig, v⟩ ⟨pk', sk', log', msg', sig', v'⟩ C hpk hlog hmsg hsig
    cases hpk; cases hlog; cases hmsg; cases hsig
    exact Iff.rfl
  have hev : ∀ w : (core.SkSeed × core.SkPrf) × (DeriveOutcome core ×
      SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y),
      RunItsrCovered core (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2) ↔
        RunItsrCovered core (DeriveOutcome.fill core s₀ w.2.1, w.2.2.1) := fun w ↦ by
    rw [ho _ (DeriveOutcome.fill core s₀ w.2.1) _
      (by simp only [DeriveOutcome.fill, UnforgeableTranscript.mapSk_pk])
      (by simp only [DeriveOutcome.fill, UnforgeableTranscript.mapSk_log])
      (by simp only [DeriveOutcome.fill, UnforgeableTranscript.mapSk_msg])
      (by simp only [DeriveOutcome.fill, UnforgeableTranscript.mapSk_sig])]
    simp only [RunItsrCovered, ItsrCovered, ForgerDigest, LoggedDigest, RunFresh, hm]
  rw [prEvent_congr _ _ _ hev, prEvent_idealDraw_eq e optRand pkSeed adv
    fun _ z ↦ RunItsrCovered core (DeriveOutcome.fill core s₀ z.1, z.2.1)]
  let _ : MeasurableSpace (core.SkSeed × core.SkPrf) := ⊤
  rw [prEvent_bind_bind_eq_lintegral_of_discrete, lintegral_const]
  simp

/-- **The forging advantage per public seed, up to coverage in the run.** Under the byte laws, the
key discipline and `|Y| ≤ |SK.prf|`, the forging advantage against SLH-DSA in the random-oracle
model at public seed `pkSeed`, of a forger with hash budget `qh`, is at most `2 (qh + V) / |Y|`,
with `V` the verifier's query bound, plus the probability that the run fires interleaved-target
coverage with a fresh forged message (`RunItsrCovered`). The statement is per public seed; the
coverage term remains a probability of the run and is not bounded here; the faithfulness step
relating the three-oracle model to the byte-level scheme is not included. For deterministic
signing at the FIPS 205 parameter sets, this run-level coverage term cannot be bounded at the size
of the coverage term of `securityBound`: a forger that guesses `SK.prf` through its `PRF_msg`
queries predicts every randomizer and grinds `H_msg` until the digests it gets signed cover its
target, so coverage in the run is at least about as likely as that guess (≈ `qh / |SK.prf|`),
which the first term already charges. The coverage term of
`unforgeableAdvantage_romScheme_pure_le_add_idealDraw` is free of that guess: there every
randomizer is sampled independently of the public answers. -/
theorem unforgeableAdvantage_romScheme_pure_le_add (laws : core.ByteLaws)
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))}
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec core)) adv ≤
      2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) / Nat.card core.Y +
      Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[RunItsrCovered core z] := by
  calc _ ≤ _ := unforgeableAdvantage_romScheme_le_or_add core laws e optRand (pure pkSeed) adv
    _ ≤ _ := by
      gcongr
      exact prEvent_romSchemeRun_runTargetCollision_or_runHiddenHit_le hd hcard e optRand pkSeed
        hadv

end SLHDSA.Security
