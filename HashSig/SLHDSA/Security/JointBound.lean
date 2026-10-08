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
  `idealDraw`, read on the rebuilt transcript and the merged cache. The first game hop is applied
  to the whole bad event before the union is split, so a seed guess is charged once, inside the
  joint term, and the coverage term is a probability of a game in which every secret value and
  randomizer is a table entry sampled independently of the public answers.
* `unforgeableAdvantage_romScheme_pure_le_add`: at most `2 (qh + V) / |Y|` plus the probability of
  `RunItsrCovered` in the run itself. For deterministic signing this coverage probability is not
  of the size of a coverage bound: a forger that finds `SK.prf` through its `PRF_msg` queries
  predicts every randomizer and so chooses which `H_msg` digests get signed, which makes coverage
  in the run about as likely as that seed guess. The coverage term to bound separately is the one
  in the ideal hidden-seed game.

## The chain of games

* The run is the real hidden-seed game under uniform secret seeds
  (`prEvent_romSchemeRun_pure_eq`), which is at most the ideal game read on the rebuilt cache, or
  a public point encoding a derivation (`SecretEncoding.prEvent_bind_realImpl_le_or`). Together
  these are the first hop, `prEvent_romSchemeRun_pure_le_or`, stated on `idealDraw`.
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

/-- The ideal hidden-seed game of SLH-DSA at public seed `pkSeed`: the secret seeds drawn
uniformly, paired with the outcome and the final split cache of the secret-free experiment run in
the ideal game (`SecretEncoding.idealImpl`) from the empty caches. The seeds are drawn
independently of that run, in which every secret value and randomizer is a table entry sampled
independently of the public answers. -/
@[expose] noncomputable def idealDraw (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))) :
    ProbComp ((core.SkSeed × core.SkPrf) × (DeriveOutcome core ×
      SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y)) := do
  let s ← $ᵗ (core.SkSeed × core.SkPrf)
  let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core) core.Y)
    (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run (∅, ∅)
  return (s, z)

/-- **The run against the ideal hidden-seed game.** An event `Q` of the run of SLH-DSA in the
random-oracle model at public seed `pkSeed` and its final cache has probability at most that, in
`idealDraw`, `Q` holds of the transcript rebuilt with the drawn seeds `s` and of the cache merged
under `s`, or the final public cache holds a point encoding a derivation under `s`. -/
theorem prEvent_romSchemeRun_pure_le_or (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))
    (Q : RomOutcome vp core × (hashSpec core).QueryCache → Prop) :
    Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[Q z] ≤
      Pr{let w ← idealDraw e optRand pkSeed adv}[
        Q (DeriveOutcome.fill core w.1 w.2.1, (secretEncoding core e pkSeed).merge w.1 w.2.2) ∨
          ∃ x, (w.2.2.1 ((secretEncoding core e pkSeed).enc w.1 x)).isSome] := by
  rw [prEvent_romSchemeRun_pure_eq core e optRand pkSeed adv Q]
  refine ((secretEncoding core e pkSeed).prEvent_bind_realImpl_le_or _
    fun s z ↦ Q (DeriveOutcome.fill core s z.1, z.2)).trans (le_of_eq ?_)
  simp only [idealDraw, bind_assoc, pure_bind]

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
  have hdraw : Pr{let w ← idealDraw e optRand pkSeed adv}[F w.1 w.2] =
      Pr{let s ← ms; let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec core)
        (DeriveQuery core) core.Y) oa).run (∅, ∅)}[F s z] := by
    simp only [idealDraw, bind_assoc, pure_bind]
    rfl
  rw [hdraw, hswap, prEvent_bind_bind_eq_lintegral_of_discrete,
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
  (prEvent_romSchemeRun_pure_le_or e optRand pkSeed adv Q).trans
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
      (h.imp_left id)).trans <|
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
  (prEvent_romSchemeRun_pure_le_or e optRand pkSeed adv _).trans
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
    ((prEvent_romSchemeRun_pure_le_or e optRand pkSeed adv _).trans ?_)
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

/-- **The forging advantage per public seed, up to coverage in the run.** Under the byte laws, the
key discipline and `|Y| ≤ |SK.prf|`, the forging advantage against SLH-DSA in the random-oracle
model at public seed `pkSeed`, of a forger with hash budget `qh`, is at most `2 (qh + V) / |Y|`,
with `V` the verifier's query bound, plus the probability that the run fires interleaved-target
coverage with a fresh forged message (`RunItsrCovered`). The statement is per public seed; the
coverage term remains a probability of the run and is not bounded here; the faithfulness step
relating the three-oracle model to the byte-level scheme is not included. For deterministic
signing the coverage probability of the run includes the forger guessing `SK.prf`, which
`unforgeableAdvantage_romScheme_pure_le_add_idealDraw` charges inside the first term instead. -/
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
