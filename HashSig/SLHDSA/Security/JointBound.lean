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

The strong forging advantage is then bounded in two forms, both per public seed:

* `strongUnforgeableAdvantage_romScheme_pure_le_add_idealDraw`: at most `2 (qh + V) / |Y|` plus the
  probability of interleaved-target coverage (`RunItsrCovered`) in the ideal hidden-seed game
  `idealDraw` (`HashSig.SLHDSA.Security.SeedCouplingBound`), read on the rebuilt transcript and
  the merged cache. The first game hop is applied to the whole bad event before the union is
  split, so a seed guess is charged once, inside the joint term, and the coverage term is a
  probability of a game in which every secret value and randomizer is a table entry sampled
  independently of the public answers. Coverage reads only the `H_msg` answers, which merging
  leaves as they are in the ideal run's public cache, so the coverage term is the probability of
  coverage in the secret-free ideal run alone, read at any fixed seeds
  (`prEvent_idealDraw_runItsrCovered_eq`).
* `strongUnforgeableAdvantage_romScheme_pure_le_add`: at most `2 (qh + V) / |Y|` plus the
  probability of `RunItsrCovered` in the run itself. For deterministic signing at the FIPS 205
  parameter sets, this run-level coverage term cannot be bounded at the size of the coverage term of
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

The joint bound and the advantage bound in the ideal-game form both take a further event.
`prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_le_of_charged` joins an event of the ideal
game that transports to a hazard of a further charge (`DeferredCharge`): a hazard of relabelled
states charged inside the joint potential (`CanonicalGraph.IsCharged`), and a hazard of the drawn
seeds and the filled state charged alongside the seed charge, under one widened pathwise budget.
Charges combine (`DeferredCharge.add`); a hazard of the drawn seeds and the final public cache alone
is one (`DeferredCharge.ofSeed`), and so is a charged hazard of relabelled states alone
(`DeferredCharge.ofCharged`). The first case is
`prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_le_of_budget`.
`prEvent_romSchemeRun_strongWins_or_le_add_idealDraw` bounds a forgery or a further event `P` of the
run by such an ideal-game bound plus the coverage term.

## Scope

* The bounds are per public seed: the scheme is `romScheme core e optRand (pure pkSeed)`.
* Interleaved-target coverage is not bounded here; it remains a probability, in the ideal
  hidden-seed game in `strongUnforgeableAdvantage_romScheme_pure_le_add_idealDraw` and in the run in
  `strongUnforgeableAdvantage_romScheme_pure_le_add`. `HashSig.SLHDSA.Security.CoverageBound` bounds
  the ideal-game term (`prEvent_idealDraw_runItsrCovered_le`).
* The losses of the faithfulness step relating the three-oracle model to the byte-level scheme
  over a single SHAKE256 are not included; that scheme is bounded in
  `HashSig.SLHDSA.Security.ByteBound`.
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
    rw [← OracleComp.prEvent_bind_map_swap]
    simp only [CanonicalGraph.deferredFillDraw, prEvent_norm]
  rw [prEvent_idealDraw_eq, hswap, prEvent_bind_bind_eq_lintegral_of_discrete,
    prEvent_bind_bind_eq_lintegral_of_discrete]
  refine lintegral_mono fun s ↦ (hs s).trans (le_of_eq ?_)
  simp only [prEvent_norm]

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

omit [DecidableEq core.Y] [SampleableType core.SkSeed] [SampleableType core.SkPrf]
  [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf] in
/-- A finite quantity over `|Y|` is finite: the node type is finite and nonempty. -/
theorem div_natCard_ne_top {x : ℝ≥0∞} (hx : x ≠ ⊤) : x / Nat.card core.Y ≠ ⊤ :=
  ENNReal.div_ne_top hx (Nat.cast_ne_zero.2 Nat.card_pos.ne')

variable (core) in
/-- **A further hazard charged inside the joint potential** of the deferred lab run at public seed
`pkSeed`: a hazard `P` of relabelled states charged to a potential `Φ`
(`CanonicalGraph.IsCharged`), failing at the empty state, with `Φ` at most `U` of the public
cache; and a hazard `H` of the secret seeds and the filled state, firing under uniform seeds with
probability at most `c` of the public cache. -/
structure DeferredCharge (pkSeed : core.PkSeed) where
  /-- The hazard of relabelled states. -/
  P : LabState core → Prop
  /-- Its potential. -/
  Φ : LabState core → ℝ≥0∞
  /-- The hazard is charged to the potential in the deferred game of `slhGraph core pkSeed`. -/
  isCharged : (slhGraph core pkSeed).IsCharged P Φ
  /-- The hazard fails at the empty state. -/
  not_empty : ¬P (∅, ∅)
  /-- A bound of the potential by the public cache. -/
  U : (hashSpec core).QueryCache → ℝ≥0∞
  /-- The potential of every state is at most `U` of its public cache. -/
  le_U : ∀ st, Φ st ≤ U st.1
  /-- The hazard of the secret seeds and the filled state. -/
  H : core.SkSeed × core.SkPrf → LabState core → Prop
  /-- Its charge. -/
  c : (hashSpec core).QueryCache → ℝ≥0∞
  /-- Under uniform secret seeds the seed hazard fires at every state with probability at most
  `c` of its public cache. -/
  prEvent_le : ∀ st, Pr{let s ← $ᵗ (core.SkSeed × core.SkPrf)}[H s st] ≤ c st.1

namespace DeferredCharge

variable {pkSeed : core.PkSeed}

/-- A hazard of the secret seeds and the public cache, charged `c`, as a further charge with no
hazard of relabelled states. -/
@[expose] def ofSeed (H : core.SkSeed × core.SkPrf → (hashSpec core).QueryCache → Prop)
    (c : (hashSpec core).QueryCache → ℝ≥0∞)
    (hH : ∀ C, Pr{let s ← $ᵗ (core.SkSeed × core.SkPrf)}[H s C] ≤ c C) :
    DeferredCharge core pkSeed where
  P _ := False
  Φ := 0
  isCharged := CanonicalGraph.isCharged_false _
  not_empty := id
  U := 0
  le_U _ := le_rfl
  H s st := H s st.1
  c := c
  prEvent_le st := hH st.1

/-- A hazard of relabelled states charged to a potential bounded by `U` of the public cache, as a
further charge with no hazard of the seeds. -/
@[expose] def ofCharged (P : LabState core → Prop) (Φ : LabState core → ℝ≥0∞)
    (hP : (slhGraph core pkSeed).IsCharged P Φ) (hP₀ : ¬P (∅, ∅))
    (U : (hashSpec core).QueryCache → ℝ≥0∞) (hU : ∀ st, Φ st ≤ U st.1) :
    DeferredCharge core pkSeed where
  P := P
  Φ := Φ
  isCharged := hP
  not_empty := hP₀
  U := U
  le_U := hU
  H _ _ := False
  c := 0
  prEvent_le _ := by simp

/-- Two further charges: the disjunctions of their hazards, charged to the sums. -/
@[expose] def add (χ₁ χ₂ : DeferredCharge core pkSeed) : DeferredCharge core pkSeed where
  P st := χ₁.P st ∨ χ₂.P st
  Φ := χ₁.Φ + χ₂.Φ
  isCharged := χ₁.isCharged.or_add χ₂.isCharged
  not_empty := not_or.2 ⟨χ₁.not_empty, χ₂.not_empty⟩
  U := χ₁.U + χ₂.U
  le_U st := add_le_add (χ₁.le_U st) (χ₂.le_U st)
  H s st := χ₁.H s st ∨ χ₂.H s st
  c := χ₁.c + χ₂.c
  prEvent_le st := (prEvent_or_le _ _ _).trans (add_le_add (χ₁.prEvent_le st) (χ₂.prEvent_le st))

end DeferredCharge

/-- **The joint bound in the ideal hidden-seed game, with a further charge.** Under the key
discipline and `|Y| ≤ |SK.prf|`, let an event `F` of the seeds and the outcome of `idealDraw`,
read at each point of the deferred lab run with its end fill and drawn seeds, imply there a
conflict, a target collision at a node key, or a hazard of a further charge `χ`, and let twice the
public entries at node keys over `|Y|`, plus the bound `U` of the potential of `χ`, the seed
charge and the charge `c` of `χ`, be at most `B` on every deferred run of the lab experiment.
Then `idealDraw` at public seed `pkSeed` fires, on the transcript rebuilt with the drawn seeds and
the cache merged under them, a same-key target collision, a hidden-value hit or `F`, or holds in
its final public cache a point encoding a derivation under the drawn seeds, with probability at
most `B`. -/
theorem prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_le_of_charged
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))
    (F : core.SkSeed × core.SkPrf →
      DeriveOutcome core × SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y →
        Prop) (χ : DeferredCharge core pkSeed)
    (hF : ∀ w ∈ support ((slhGraph core pkSeed).deferredFillDraw ($ᵗ (core.SkSeed × core.SkPrf))
        (labExperiment core adv pkSeed)),
      F w.2.2 (w.1.1, (slhGraph core pkSeed).toSplitCache w.2.1) →
        (slhGraph core pkSeed).Conflict w.2.1 ∨ (slhNodeKeys core pkSeed).TCHazard w.2.1 ∨
          χ.P w.2.1 ∨ χ.H w.2.2 w.2.1)
    (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hbud : ∀ z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
        (labExperiment core adv pkSeed)).run ((∅, ∅), [])),
      2 * (((slhNodeKeys core pkSeed).keyEntries z.2.1.1).encard : ℝ≥0∞) / Nat.card core.Y +
        χ.U z.2.1.1 + (seedCharge core pkSeed z.2.1.1 + χ.c z.2.1.1) ≤ B) :
    Pr{let w ← idealDraw e optRand pkSeed adv}[
      ((RunTargetCollision core e (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2) ∨
        RunHiddenHit core e (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)) ∨ F w.1 w.2) ∨
      ∃ x, (w.2.2.1 ((secretEncoding core e pkSeed).enc w.1 x)).isSome] ≤ B := by
  set E := secretEncoding core e pkSeed
  set G := slhGraph core pkSeed
  set nk := slhNodeKeys core pkSeed
  refine (prEvent_idealDraw_le_prEvent_deferredFillDraw hd e optRand pkSeed adv fun s z ↦
    ((RunTargetCollision core e (DeriveOutcome.fill core s z.1, E.merge s z.2) ∨
      RunHiddenHit core e (DeriveOutcome.fill core s z.1, E.merge s z.2)) ∨ F s z) ∨
    ∃ x, (z.2.1 (E.enc s x)).isSome).trans <|
  (prEvent_mono_of_support _ _ (fun w ↦ ((G.Conflict w.2.1 ∨ nk.TCHazard w.2.1) ∨ χ.P w.2.1) ∨
      ((∃ x, (w.2.1.1 (E.enc w.2.2 x)).isSome) ∨ χ.H w.2.2 w.2.1)) fun w hw h ↦ ?_).trans <|
  (nk.isCharged.or_add χ.isCharged).prEvent_deferredFillDraw_le_of_budget
    (not_or.2 ⟨not_or.2 ⟨G.not_conflict_empty, CanonicalGraph.NodeKeys.not_tcHazard_empty⟩,
      χ.not_empty⟩)
    (fun C ↦ 2 * ((nk.keyEntries C).encard : ℝ≥0∞) / Nat.card core.Y + χ.U C)
    (fun st ↦ add_le_add (nk.potential_le_two_mul st) (χ.le_U st)) _
    (fun s st ↦ (∃ x, (st.1 (E.enc s x)).isSome) ∨ χ.H s st)
    (fun C ↦ seedCharge core pkSeed C + χ.c C)
    (fun st ↦ (prEvent_or_le _ _ _).trans
      (add_le_add (prEvent_exists_isSome_apply_secretEncoding_enc_le e pkSeed hcard st.1)
        (χ.prEvent_le st))) _ B hB hbud
  have hT : G.Conflict w.2.1 ∨ nk.TCHazard w.2.1 ∨ (∃ x, (w.2.1.1 (E.enc w.2.2 x)).isSome) →
      ((G.Conflict w.2.1 ∨ nk.TCHazard w.2.1) ∨ χ.P w.2.1) ∨
        ((∃ x, (w.2.1.1 (E.enc w.2.2 x)).isSome) ∨ χ.H w.2.2 w.2.1) := by
    rintro (h | h | h)
    exacts [.inl (.inl (.inl h)), .inl (.inl (.inr h)), .inr (.inl h)]
  rcases h with ((htchh | hF') | hseed) | hc
  · exact hT (conflict_or_tcHazard_or_exists_isSome_of_mem_support_deferredFillDraw hd hw
      (.inl (.inl htchh)))
  · rcases hF w hw hF' with h | h | h | h
    exacts [.inl (.inl (.inl h)), .inl (.inl (.inr h)), .inl (.inr h), .inr (.inr h)]
  · exact hT (conflict_or_tcHazard_or_exists_isSome_of_mem_support_deferredFillDraw hd hw
      (.inl (.inr hseed)))
  · exact .inl (.inl (.inl hc))

/-- **The joint bound in the ideal hidden-seed game, with a further hazard.** Under the key
discipline and `|Y| ≤ |SK.prf|`, let an event `F` of the seeds and the outcome of `idealDraw`, read
at each point of the deferred lab run with its end fill and drawn seeds, imply there a conflict, a
target collision at a node key, or a hazard `H` of the drawn seeds and the final public cache, let
`H` fire
under uniform seeds with probability at most `c C` at each public cache `C`, and let twice the
public entries at node keys over `|Y|`, plus the seed charge and `c`, be at most `B` on every
deferred run of the lab experiment. Then `idealDraw` at public seed `pkSeed` fires, on the
transcript rebuilt with the drawn seeds and the cache merged under them, a same-key target
collision, a hidden-value hit or `F`, or holds in its final public cache a point encoding a
derivation under the drawn seeds, with probability at most `B`. -/
theorem prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_le_of_budget
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))
    (F : core.SkSeed × core.SkPrf →
      DeriveOutcome core × SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y →
        Prop)
    (H : core.SkSeed × core.SkPrf → (hashSpec core).QueryCache → Prop)
    (c : (hashSpec core).QueryCache → ℝ≥0∞)
    (hF : ∀ w ∈ support ((slhGraph core pkSeed).deferredFillDraw ($ᵗ (core.SkSeed × core.SkPrf))
        (labExperiment core adv pkSeed)),
      F w.2.2 (w.1.1, (slhGraph core pkSeed).toSplitCache w.2.1) →
        (slhGraph core pkSeed).Conflict w.2.1 ∨ (slhNodeKeys core pkSeed).TCHazard w.2.1 ∨
          H w.2.2 w.2.1.1)
    (hH : ∀ C, Pr{let s ← $ᵗ (core.SkSeed × core.SkPrf)}[H s C] ≤ c C) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hbud : ∀ z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
        (labExperiment core adv pkSeed)).run ((∅, ∅), [])),
      2 * (((slhNodeKeys core pkSeed).keyEntries z.2.1.1).encard : ℝ≥0∞) / Nat.card core.Y +
        (seedCharge core pkSeed z.2.1.1 + c z.2.1.1) ≤ B) :
    Pr{let w ← idealDraw e optRand pkSeed adv}[
      ((RunTargetCollision core e (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2) ∨
        RunHiddenHit core e (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)) ∨ F w.1 w.2) ∨
      ∃ x, (w.2.2.1 ((secretEncoding core e pkSeed).enc w.1 x)).isSome] ≤ B :=
  prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_le_of_charged hd hcard e optRand pkSeed
    adv F (.ofSeed H c hH) (fun w hw h ↦ (hF w hw h).imp_right (Or.imp_right Or.inr)) B hB
    fun z hz ↦ by simpa only [DeferredCharge.ofSeed, Pi.zero_apply, add_zero] using hbud z hz

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
  le_trans (prEvent_mono _ _ _ fun _ h ↦ h.imp_left Or.inl) <|
    prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_le_of_budget hd hcard e optRand pkSeed
      adv (fun _ _ ↦ False) (fun _ _ ↦ False) 0 (fun _ _ ↦ False.elim) (fun _ ↦ by simp) _
      (div_natCard_ne_top (ENNReal.mul_ne_top (by simp) (by simp)))
      fun _ hz ↦ by
        simpa only [Pi.zero_apply, add_zero] using
          two_mul_encard_keyEntries_div_add_seedCharge_le_of_mem_support hd.keySeparated hadv hz

/-- **The joint target-collision and hidden-value bound, per public seed.** Under the key
discipline and `|Y| ≤ |SK.prf|`, for a forger with hash budget `qh`, the run of SLH-DSA in the
random-oracle model at public seed `pkSeed` fires a same-key target collision or a hidden-value hit
with probability at most `2 (qh + V) / |Y|`, with `V` the verifier's query bound. The forger
guessing a secret seed is charged inside this bound. Interleaved-target coverage and the
faithfulness step (bounded in `HashSig.SLHDSA.Security.ByteBound`) are not included. -/
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

/-- **A forgery or a further event, up to coverage in the ideal hidden-seed game.** Under the byte
laws, if `idealDraw` at public seed `pkSeed` fires, on the transcript rebuilt with the drawn seeds
and the cache merged under them, a same-key target collision, a hidden-value hit or `P`, or holds a
point encoding a derivation in its final public cache, with probability at most `B`, then the run of
SLH-DSA in the random-oracle model at `pkSeed` wins strongly or fires `P` with probability at most
`B` plus the probability that `idealDraw` fires interleaved-target coverage at a fresh `H_msg` point
(`RunItsrCovered`) there. The first game hop is applied to the whole event before the union is
split, so a seed guess is charged once, inside `B`. -/
theorem prEvent_romSchemeRun_strongWins_or_le_add_idealDraw (laws : core.ByteLaws)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))
    (P : RomOutcome vp core × (hashSpec core).QueryCache → Prop) {B : ℝ≥0∞}
    (hB : Pr{let w ← idealDraw e optRand pkSeed adv}[((RunTargetCollision core e
        (DeriveOutcome.fill core w.1 w.2.1, (secretEncoding core e pkSeed).merge w.1 w.2.2) ∨
        RunHiddenHit core e (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)) ∨
        P (DeriveOutcome.fill core w.1 w.2.1, (secretEncoding core e pkSeed).merge w.1 w.2.2)) ∨
      ∃ x, (w.2.2.1 ((secretEncoding core e pkSeed).enc w.1 x)).isSome] ≤ B) :
    Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[z.1.strongWins = true ∨ P z] ≤
      B + Pr{let w ← idealDraw e optRand pkSeed adv}[
        RunItsrCovered core (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)] := by
  refine (prEvent_mono_of_support _ _
    (fun z ↦ ((RunTargetCollision core e z ∨ RunHiddenHit core e z) ∨ P z) ∨ RunItsrCovered core z)
    fun z hz h ↦ ?_).trans
    ((prEvent_romSchemeRun_pure_le_prEvent_idealDraw_or e optRand pkSeed adv _).trans ?_)
  · rcases h with hw | h
    · rcases bad_event_of_strongWins_romSchemeRun laws e optRand _ adv hz hw with h | h | h
      exacts [Or.inl (Or.inl (Or.inl h)), Or.inl (Or.inl (Or.inr h)), Or.inr h]
    · exact Or.inl (Or.inr h)
  exact (prEvent_mono _ _ _ fun _ h ↦ or_right_comm.1 h).trans
    ((prEvent_or_le _ _ _).trans (add_le_add hB le_rfl))

/-- **The strong forging advantage per public seed, up to coverage in the ideal hidden-seed game.**
Under the byte laws, the key discipline and `|Y| ≤ |SK.prf|`, the strong forging advantage against
SLH-DSA in the random-oracle model at public seed `pkSeed`, of a forger with hash budget `qh`, is at
most `2 (qh + V) / |Y|`, with `V` the verifier's query bound, plus the probability that `idealDraw`
at `pkSeed` fires interleaved-target coverage at a fresh `H_msg` point (`RunItsrCovered`) on the
transcript rebuilt with the drawn seeds and the cache merged under them. The forger guessing a
secret seed is charged once, inside the first term. The statement is per public seed; the coverage
term remains a probability in the ideal hidden-seed game and is not bounded here; the faithfulness
step relating the three-oracle model to the byte-level scheme is not included (it is bounded in
`HashSig.SLHDSA.Security.ByteBound`). -/
theorem strongUnforgeableAdvantage_romScheme_pure_le_add_idealDraw (laws : core.ByteLaws)
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed)
    {adv : StrongUnforgeableAdversary (romScheme core e optRand (pure pkSeed))}
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec core)) adv ≤
      2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) / Nat.card core.Y +
      Pr{let w ← idealDraw e optRand pkSeed adv.toUnforgeableAdversary}[
        RunItsrCovered core (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)] := by
  rw [strongUnforgeableAdvantage_romScheme_eq]
  refine (prEvent_mono _ _ _ fun _ ↦ Or.inl).trans
    (prEvent_romSchemeRun_strongWins_or_le_add_idealDraw laws e optRand pkSeed _ (fun _ ↦ False)
      ((prEvent_mono _ _ _ fun _ h ↦ h.imp_left fun h ↦ h.resolve_right id).trans
        (prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_exists_isSome_le hd hcard e
          optRand pkSeed hadv)))

/-- **The coverage term of the ideal hidden-seed game does not depend on the drawn seeds.**
Interleaved-target coverage at a fresh `H_msg` point, read in `idealDraw` on the transcript
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
    simp only [RunItsrCovered, ItsrCovered, ForgerDigest, LoggedDigest, RunPointFresh, hm]
  rw [prEvent_congr _ _ _ hev, prEvent_idealDraw_eq e optRand pkSeed adv
    fun _ z ↦ RunItsrCovered core (DeriveOutcome.fill core s₀ z.1, z.2.1)]
  let _ : MeasurableSpace (core.SkSeed × core.SkPrf) := ⊤
  rw [prEvent_bind_bind_eq_lintegral_of_discrete, lintegral_const,
    OracleComp.evalDist_apply_univ_eq_one, mul_one]

/-- **The strong forging advantage per public seed, up to coverage in the run.** Under the byte
laws, the key discipline and `|Y| ≤ |SK.prf|`, the strong forging advantage against SLH-DSA in the
random-oracle model at public seed `pkSeed`, of a forger with hash budget `qh`, is at most `2 (qh +
V) / |Y|`, with `V` the verifier's query bound, plus the probability that the run fires
interleaved-target coverage at a fresh `H_msg` point (`RunItsrCovered`). The statement is per public
seed; the coverage term remains a probability of the run and is not bounded here; the faithfulness
step relating the three-oracle model to the byte-level scheme is not included (it is bounded in
`HashSig.SLHDSA.Security.ByteBound`). For deterministic signing at the FIPS 205 parameter sets, this
run-level coverage term cannot be bounded at the size of the coverage term of `securityBound`: a
forger that guesses `SK.prf` through its `PRF_msg` queries predicts every randomizer and grinds
`H_msg` until the digests it gets signed cover its target, so coverage in the run is at least about
as likely as that guess (≈ `qh / |SK.prf|`), which the first term already charges. The coverage term
of `strongUnforgeableAdvantage_romScheme_pure_le_add_idealDraw` is free of that guess: there every
randomizer is sampled independently of the public answers. -/
theorem strongUnforgeableAdvantage_romScheme_pure_le_add (laws : core.ByteLaws)
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed)
    {adv : StrongUnforgeableAdversary (romScheme core e optRand (pure pkSeed))}
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec core)) adv ≤
      2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) / Nat.card core.Y +
      Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv.toUnforgeableAdversary}[
        RunItsrCovered core z] := by
  calc _ ≤ _ := strongUnforgeableAdvantage_romScheme_le_or_add core laws e optRand (pure pkSeed) adv
    _ ≤ _ := by
      gcongr
      exact prEvent_romSchemeRun_runTargetCollision_or_runHiddenHit_le hd hcard e optRand pkSeed
        hadv

end SLHDSA.Security
