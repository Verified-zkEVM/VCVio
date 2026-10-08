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
secret seed is inside this bound: it is charged by the same potential, not added. With the grouped
union bound (`unforgeableAdvantage_romScheme_le_or_add`), the forging advantage is at most this
bound plus the probability of interleaved-target coverage (`RunItsrCovered`)
(`unforgeableAdvantage_romScheme_pure_le_add`).

The proof is a chain of games, packaged for an arbitrary event of the run as
`prEvent_romSchemeRun_le_prEvent_deferredFillDraw`:

* the run is the real hidden-seed game under uniform secret seeds
  (`prEvent_romSchemeRun_pure_eq`), which is at most the ideal game read on the rebuilt cache, or
  a public point encoding a derivation (`SecretEncoding.prEvent_bind_realImpl_le_or`);
* the ideal game is at most the eager relabelled game of the canonical graph `slhGraph core
  pkSeed`, or a conflict (`CanonicalGraph.prEvent_idealImpl_le_eagerImpl_liftComp`);
* in the eager game the lifted secret-free experiment is the lab experiment
  (`prEvent_eagerImpl_liftComp_eq_labExperiment`);
* the eager game is at most the deferred game after the end fill, or a conflict
  (`CanonicalGraph.prEvent_eagerImpl_le_deferredImpl_empty`), and the secret seeds are drawn after
  the fill (`CanonicalGraph.deferredFillDraw`); there, a pointwise transport of the events
  bounds them by any event of the deferred run that the transport reaches.

For the target collision and the hidden-value hit, the transport reaches a conflict, a target
collision at a node key, or a seed hazard of the final public cache
(`conflict_or_tcHazard_or_exists_isSome_of_mem_support_deferredFillDraw`), and the joint potential
bounds these by `2 (qh + V) / |Y|`
(`CanonicalGraph.NodeKeys.prEvent_deferredFillDraw_le_of_budget`), under the pathwise budget of the
lab experiment
(`two_mul_encard_keyEntries_div_add_seedCharge_le_of_mem_support`) and the seed charge
(`prEvent_exists_isSome_apply_secretEncoding_enc_le`).

## Scope

* The bounds are per public seed: the scheme is `romScheme core e optRand (pure pkSeed)`.
* Interleaved-target coverage (`RunItsrCovered`) is not bounded here; it remains a probability in
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
                (labExperiment core adv pkSeed)}[H w] := by
  set G := slhGraph core pkSeed
  set E := secretEncoding core e pkSeed
  set ms := ($ᵗ (core.SkSeed × core.SkPrf) : ProbComp _)
  set oa := unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed)
  set lab := labExperiment core adv pkSeed
  set F : core.SkSeed × core.SkPrf →
      DeriveOutcome core × SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y →
        Prop :=
    fun s z ↦ Q (DeriveOutcome.fill core s z.1, E.merge s z.2) ∨
      ∃ x, (z.2.1 (E.enc s x)).isSome
  have h1 : Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[Q z] ≤
      Pr{let s ← ms; let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec core)
        (DeriveQuery core) core.Y) oa).run (∅, ∅)}[F s z] := by
    rw [prEvent_romSchemeRun_pure_eq core e optRand pkSeed adv Q]
    exact E.prEvent_bind_realImpl_le_or oa fun s z ↦ Q (DeriveOutcome.fill core s z.1, z.2)
  have h2 : ∀ s, Pr{let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec core)
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
  have h3 : Pr{let s ← ms; let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec core)
        (DeriveQuery core) core.Y) oa).run (∅, ∅)}[F s z] ≤
      Pr{let w ← G.deferredFillDraw ms lab}[F w.2.2 (w.1.1, G.toSplitCache w.2.1) ∨
        G.Conflict w.2.1] := by
    let _ : MeasurableSpace (core.SkSeed × core.SkPrf) := ⊤
    have hswap : Pr{let w ← G.deferredFillDraw ms lab}[F w.2.2 (w.1.1, G.toSplitCache w.2.1) ∨
        G.Conflict w.2.1] = Pr{let s ← ms; let zst ← ((simulateQ G.deferredImpl lab).run
          ((∅, ∅), []) >>= fun z ↦ (z, ·) <$> RelabelState.endFill z.2)}[
          F s (zst.1.1, G.toSplitCache zst.2) ∨ G.Conflict zst.2] := by
      rw [← OracleComp.prEvent_bind_bind_swap]
      simp only [CanonicalGraph.deferredFillDraw, bind_assoc, bind_map_left, pure_bind]
    rw [hswap, prEvent_bind_bind_eq_lintegral_of_discrete,
      prEvent_bind_bind_eq_lintegral_of_discrete]
    refine lintegral_mono fun s ↦ (h2 s).trans (le_of_eq ?_)
    simp only [bind_assoc, bind_map_left]
  exact h1.trans (h3.trans (prEvent_mono_of_support _ _ _ hH))

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
  (prEvent_romSchemeRun_le_prEvent_deferredFillDraw hd e optRand pkSeed adv _
    (fun w ↦ (slhGraph core pkSeed).Conflict w.2.1 ∨ (slhNodeKeys core pkSeed).TCHazard w.2.1 ∨
      ∃ x, (w.2.1.1 ((secretEncoding core e pkSeed).enc w.2.2 x)).isSome)
    fun _ hw h ↦
      conflict_or_tcHazard_or_exists_isSome_of_mem_support_deferredFillDraw hd hw h).trans
  ((slhNodeKeys core pkSeed).prEvent_deferredFillDraw_le_of_budget _
    (fun s C ↦ ∃ x, (C ((secretEncoding core e pkSeed).enc s x)).isSome) (seedCharge core pkSeed)
    (prEvent_exists_isSome_apply_secretEncoding_enc_le e pkSeed hcard) _ _
    (ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (by
      simp only [ne_eq, Nat.cast_eq_zero, Nat.card_ne_zero]
      exact ⟨inferInstance, inferInstance⟩))
    (fun _ hz ↦ two_mul_encard_keyEntries_div_add_seedCharge_le_of_mem_support
      hd.keySeparated hadv hz))

/-- **The forging advantage per public seed, up to interleaved-target coverage.** Under the byte
laws, the key discipline and `|Y| ≤ |SK.prf|`, the forging advantage against SLH-DSA in the
random-oracle model at public seed `pkSeed`, of a forger with hash budget `qh`, is at most
`2 (qh + V) / |Y|`, with `V` the verifier's query bound, plus the probability that the run fires
interleaved-target coverage with a fresh forged message (`RunItsrCovered`). The statement is per
public seed; the coverage term remains a probability and is not bounded here; the faithfulness
step relating the three-oracle model to the byte-level scheme is not included. -/
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
