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

The proof is a chain of games:

* the run is the real hidden-seed game under uniform secret seeds
  (`prEvent_romSchemeRun_pure_eq`), which is at most the ideal game read on the rebuilt cache, or
  a public point encoding a derivation (`SecretEncoding.prEvent_bind_realImpl_le_or`);
* the ideal game is at most the eager relabelled game of the canonical graph `slhGraph core
  pkSeed`, or a conflict (`CanonicalGraph.prEvent_idealImpl_le_eagerImpl_liftComp`);
* in the eager game the lifted secret-free experiment is the lab experiment
  (`prEvent_eagerImpl_liftComp_eq_labExperiment`);
* the eager game is at most the deferred game after the end fill, or a conflict
  (`CanonicalGraph.prEvent_eagerImpl_le_deferredImpl_empty`), and the secret seeds are drawn after
  the fill;
* there, the events are a conflict, a target collision at a node key, or a seed hazard of the
  final public cache
  (`conflict_or_tcHazard_or_exists_isSome_of_mem_support_deferredFillDraw`);
* the joint potential bounds these by `2 (qh + V) / |Y|`
  (`CanonicalGraph.NodeKeys.prEvent_deferredFillDraw_le_of_budget`), under the pathwise budget of
  the lab experiment (`two_mul_encard_keyEntries_div_add_seedCharge_le_of_mem_support`) and the
  seed charge (`prEvent_exists_isSome_apply_secretEncoding_enc_le`).

## Scope

* The bound is per public seed: the scheme is `romScheme core e optRand (pure pkSeed)`.
* It bounds the target-collision and hidden-value events only. Interleaved-target coverage
  (`RunItsrCovered`), the third event of `unforgeableAdvantage_romScheme_le_add`, is not bounded
  here, and neither are the losses of the faithfulness step relating the three-oracle model to the
  byte-level scheme over a single SHAKE256.
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
    2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) / Nat.card core.Y := by
  set G := slhGraph core pkSeed
  set E := secretEncoding core e pkSeed
  set ms := ($ᵗ (core.SkSeed × core.SkPrf) : ProbComp _)
  set oa := unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed)
  set lab := labExperiment core adv pkSeed
  set Q : RomOutcome vp core × (hashSpec core).QueryCache → Prop :=
    fun z ↦ RunTargetCollision core e z ∨ RunHiddenHit core e z
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
  have h4 : Pr{let w ← G.deferredFillDraw ms lab}[F w.2.2 (w.1.1, G.toSplitCache w.2.1) ∨
        G.Conflict w.2.1] ≤
      Pr{let w ← G.deferredFillDraw ms lab}[G.Conflict w.2.1 ∨
        (slhNodeKeys core pkSeed).TCHazard w.2.1 ∨ ∃ x, (w.2.1.1 (E.enc w.2.2 x)).isSome] :=
    prEvent_mono_of_support _ _ _ fun w hw h ↦
      conflict_or_tcHazard_or_exists_isSome_of_mem_support_deferredFillDraw hd hw h
  have h5 := (slhNodeKeys core pkSeed).prEvent_deferredFillDraw_le_of_budget ms
    (fun s C ↦ ∃ x, (C (E.enc s x)).isSome) (seedCharge core pkSeed)
    (prEvent_exists_isSome_apply_secretEncoding_enc_le e pkSeed hcard) lab
    (2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) / Nat.card core.Y)
    (ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (by
      simp only [ne_eq, Nat.cast_eq_zero, Nat.card_ne_zero]
      exact ⟨inferInstance, inferInstance⟩))
    (fun z hz ↦ two_mul_encard_keyEntries_div_add_seedCharge_le_of_mem_support
      hd.keySeparated hadv hz)
  exact h1.trans (h3.trans (h4.trans h5))

end SLHDSA.Security
