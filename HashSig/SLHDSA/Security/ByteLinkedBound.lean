/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteLinkedView
public import HashSig.SLHDSA.Security.CoverageBound
public import HashSig.SLHDSA.Security.HedgedKeyBound

/-!
# The events of the verifying run, bounded with a further charge

At `n = 32`, for a fixed public seed and every `opt_rand` distribution,
`HashSig.SLHDSA.Security.ByteLinkedView` bounds the strong advantage against SLH-DSA over one
SHAKE256 oracle by the probability of an event of the three-oracle run of `romScheme` against the
verifying adversary `verifyingAdv`: a target collision or a mixed hidden-value hit
(`RunHiddenHitMixed`), a clash of the message-`PRF` key at `opt_rand = PK.seed` (`RunPrfKeyClash`),
a virtual hit (`VirtualHit`), an honest input at a linked point (`LinkedHonestInput`), or
interleaved-target coverage. This module bounds that event in one game hop and one potential, in
both signing modes, with the virtual hit and the honest input at a linked point charged by a further
charge that the caller supplies. It is a classical random-oracle statement; nothing here is quantum.

## The bound

For an adversary with hash budget `qh` and signing budget `qs`, the verifying adversary has
budget `(qh + V, qs)`, `V` the verifier's query bound (`romQueryBound_verifyingAdv`). Take a
further event `X` of the run, a further charge `χ : DeferredCharge` (a hazard of relabelled states
charged to a potential bounded by `χ.U`, and a hazard of the secret seeds and the filled state
charged `χ.c`), and a cost `κ`, such that

* `X` is charged to `χ` (`DeferredCharge.Charges`): at every point of the deferred lab run against
  the verifying adversary, its end fill and a draw of secret seeds, `X` of the run point it stands
  for (`deferredRunPoint`), off the seed hazard, is a conflict, a target collision at a node key,
  or a hazard of `χ`;
* `χ` is within the budget (`DeferredCharge.WithinBudget`): on every deferred run, twice the public
  entries at node keys over `|Y|`, plus `χ.U`, the seed charge, the charge of the message-`PRF` key
  and `χ.c`, is at most the joint budget of the message-`PRF` key at budget `(qh + V, qs)` plus
  `κ`.

Then the run against the verifying adversary fires a target collision, a mixed hidden-value hit,
the key clash, `X` or coverage with probability at most

* `securityBound vp.params |Y| 2 1 (qh + V) qs + (qs + 1) / |Y| + κ`
  (`prEvent_romSchemeRun_verifyingAdv_le_add`), and
* `securityBound vp.params |Y| 2 1 (qh + V) qs + 1 / |Y| + qs · ε · (qh + V + qs + 1) / |Y| + κ`
  when `optRand pk = PK.seed` with probability at most `ε` at every public key
  (`prEvent_romSchemeRun_verifyingAdv_le_add_hedged`),

and with `X` the virtual hit or the honest input at a linked point, so does the strong advantage
(`shakeStrongAdvantage_pure_le_securityBound_add`,
`shakeStrongAdvantage_pure_le_securityBound_add_hedged`). With no further event or charge, the first
is `securityBound vp.params |Y| 2 1 (qh + V) qs + (qs + 1) / |Y|`
(`prEvent_romSchemeRun_verifyingAdv_le`).

The first game hop is applied once, to the whole event, and the joint potential is spent once:
the mixed hidden-value hit is a conflict or a seed hazard of the deferred run
(`conflict_or_exists_isSome_of_hiddenHitMixed_withPost` at the linked redirect), the key clash is
charged as in `HashSig.SLHDSA.Security.PrfKeyBound` and `HashSig.SLHDSA.Security.HedgedKeyBound`,
and coverage is the ideal-game coverage term of `HashSig.SLHDSA.Security.CoverageBound`
(`prEvent_idealDraw_runItsrCovered_le`).

## The further charge

The further charge extends the joint potential. Its hazard of relabelled states is charged inside
that potential (`CanonicalGraph.IsCharged.or_add`) and its hazard of the seeds beside the seed
charge, under one pathwise budget that is joint with the charges of conflicts, target collisions,
the seed and the message-`PRF` key. So a hazard whose entries lie in the slack of the joint budget
of `HashSig.SLHDSA.Security.PrfKeyBound`, such as an `H_msg` entry at a projected key or two cells
drawn equal, costs only what the widened budget exceeds that one by, `κ`, and neither the seed hop
nor a conflict is paid a second time. The transport of `X` may
assume that no point of the public cache encodes a derivation under the drawn seeds; that hazard
is charged once, by the seed charge.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.Security

open Concrete

variable {vp : ValidatedParams} {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
  {pkSeed : (shakeCore vp).PkSeed}

/-! ## The mixed hidden-value hit on the deferred run -/

/-- The run point that a point of the deferred lab run at public seed `pkSeed`, its end fill and a
draw of secret seeds stands for: the transcript rebuilt with the drawn seeds, on the cache that the
filled state stands for at them. -/
noncomputable abbrev deferredRunPoint (pkSeed : (shakeCore vp).PkSeed)
    (w : (DeriveOutcome (shakeCore vp) × LabState (shakeCore vp) ×
      List (DeriveQuery (shakeCore vp) ⊕ NodeKey (shakeCore vp))) ×
      LabState (shakeCore vp) × ((shakeCore vp).SkSeed × (shakeCore vp).SkPrf)) :
    RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache :=
  (DeriveOutcome.fill (shakeCore vp) w.2.2 w.1.1,
    (secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).merge w.2.2
      ((slhGraph (shakeCore vp) pkSeed).toSplitCache w.2.1))

namespace DeferredCharge

/-- **An event of the run charged to a further charge** `χ`, for the adversary `A`: at every point
of the deferred lab run against `A`, its end fill and a draw of secret seeds, the event `X` of the
run point it stands for, when no point of the public cache encodes a derivation under the drawn
seeds, is a conflict of the filled state, a target collision at one of its node keys, or a hazard
of `χ`. -/
@[expose] def Charges (χ : DeferredCharge (shakeCore vp) pkSeed)
    (A : UnforgeableAdversary (romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)))
    (X : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache → Prop) : Prop :=
  ∀ w ∈ support ((slhGraph (shakeCore vp) pkSeed).deferredFillDraw
      ($ᵗ ((shakeCore vp).SkSeed × (shakeCore vp).SkPrf))
      (labExperiment (shakeCore vp) A pkSeed)),
    X (deferredRunPoint pkSeed w) →
    (¬∃ x, (w.2.1.1 ((secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).enc w.2.2 x)).isSome) →
      (slhGraph (shakeCore vp) pkSeed).Conflict w.2.1 ∨
        (slhNodeKeys (shakeCore vp) pkSeed).TCHazard w.2.1 ∨ χ.P w.2.1 ∨ χ.H w.2.2 w.2.1

/-- **A further charge within a budget**, for the adversary `A`: on every run of the lab
experiment against `A` in the deferred game, twice the public entries at node keys over `|Y|`,
plus the bound `χ.U` of the potential of `χ`, the seed charge, a charge `c₀` and the charge `χ.c`,
is at most `B`. -/
@[expose] def WithinBudget (χ : DeferredCharge (shakeCore vp) pkSeed)
    (A : UnforgeableAdversary (romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)))
    (c₀ : (hashSpec (shakeCore vp)).QueryCache → ℝ≥0∞) (B : ℝ≥0∞) : Prop :=
  ∀ z ∈ support ((simulateQ (slhGraph (shakeCore vp) pkSeed).deferredImpl
      (labExperiment (shakeCore vp) A pkSeed)).run ((∅, ∅), [])),
    2 * (((slhNodeKeys (shakeCore vp) pkSeed).keyEntries z.2.1.1).encard : ℝ≥0∞) /
        Nat.card (shakeCore vp).Y + χ.U z.2.1.1 +
      (seedCharge (shakeCore vp) pkSeed z.2.1.1 + (c₀ z.2.1.1 + χ.c z.2.1.1)) ≤ B

end DeferredCharge

/-! ## The ideal game -/

/-- **The verifying adversary in the ideal hidden-seed game, with a further charge.** Under the
key discipline, let an event `F` of the seeds and the outcome of `idealDraw`, and an event `X` of
the run off the seed hazard, each imply at every point of the deferred lab run against the
verifying adversary, its end fill and drawn seeds, a conflict, a target collision at a node key or
a hazard of the further charge `χ`, and let the joint budget with `χ` be at most `B` on every
deferred run. Then `idealDraw` at public seed `pkSeed` against the verifying adversary fires, on
the transcript rebuilt with the drawn seeds and the cache merged under them, a same-key target
collision, a mixed hidden-value hit, `F` or `X`, or holds in its final public cache a point
encoding a derivation under the drawn seeds, with probability at most `B`. -/
theorem prEvent_idealDraw_verifyingAdv_le_of_charged (hd : (shakeCore vp).KeyDiscipline vp)
    (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed)))
    (F : (shakeCore vp).SkSeed × (shakeCore vp).SkPrf → DeriveOutcome (shakeCore vp) ×
      SecretEncoding.SplitCache (hashSpec (shakeCore vp)) (DeriveQuery (shakeCore vp))
        (shakeCore vp).Y → Prop)
    (X : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache → Prop)
    (χ : DeferredCharge (shakeCore vp) pkSeed)
    (hF : ∀ w ∈ support ((slhGraph (shakeCore vp) pkSeed).deferredFillDraw
        ($ᵗ ((shakeCore vp).SkSeed × (shakeCore vp).SkPrf))
        (labExperiment (shakeCore vp) (verifyingAdv vp hn hnm adv) pkSeed)),
      F w.2.2 (w.1.1, (slhGraph (shakeCore vp) pkSeed).toSplitCache w.2.1) →
        (slhGraph (shakeCore vp) pkSeed).Conflict w.2.1 ∨
          (slhNodeKeys (shakeCore vp) pkSeed).TCHazard w.2.1 ∨ χ.P w.2.1 ∨ χ.H w.2.2 w.2.1)
    (hX : χ.Charges (verifyingAdv vp hn hnm adv) X)
    (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hbud : χ.WithinBudget (verifyingAdv vp hn hnm adv) 0 B) :
    Pr{let w ← idealDraw (core := shakeCore vp) (Equiv.refl _) optRand pkSeed
        (verifyingAdv vp hn hnm adv)}[
      ((RunTargetCollision (shakeCore vp) (Equiv.refl _)
          (DeriveOutcome.fill (shakeCore vp) w.1 w.2.1,
            (secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).merge w.1 w.2.2) ∨
        RunHiddenHitMixed vp (DeriveOutcome.fill (shakeCore vp) w.1 w.2.1,
            (secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).merge w.1 w.2.2)) ∨
        (F w.1 w.2 ∨ X (DeriveOutcome.fill (shakeCore vp) w.1 w.2.1,
            (secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).merge w.1 w.2.2))) ∨
      ∃ x, (w.2.2.1 ((secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).enc w.1 x)).isSome] ≤
      B := by
  set E := secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed
  set Seed := fun (s : (shakeCore vp).SkSeed × (shakeCore vp).SkPrf)
      (C : (hashSpec (shakeCore vp)).QueryCache) ↦ ∃ x, (C (E.enc s x)).isSome
  refine (prEvent_mono _ _ _ fun w h ↦ ?_).trans
    (prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_le_of_charged hd le_rfl
      (Equiv.refl _) optRand pkSeed (verifyingAdv vp hn hnm adv) (fun s z ↦
        (RunHiddenHitMixed vp (DeriveOutcome.fill (shakeCore vp) s z.1, E.merge s z.2) ∧
          ¬Seed s z.2.1) ∨ F s z ∨
        (X (DeriveOutcome.fill (shakeCore vp) s z.1, E.merge s z.2) ∧ ¬Seed s z.2.1))
      χ (fun w hw h ↦ ?_) B hB fun z hz ↦ by simpa only [Pi.zero_apply, zero_add] using hbud z hz)
  · by_cases hs : Seed w.1 w.2.2.1
    · exact .inr hs
    rcases h with ((htc | hhm) | hf | hx) | hs'
    exacts [.inl (.inl (.inl htc)), .inl (.inr (.inl ⟨hhm, hs⟩)), .inl (.inr (.inr (.inl hf))),
      .inl (.inr (.inr (.inr ⟨hx, hs⟩))), .inr hs']
  · have hns : ∀ {P : Prop}, (P ∧ ¬Seed w.2.2
        ((slhGraph (shakeCore vp) pkSeed).toSplitCache w.2.1).1) → P ∧ ¬Seed w.2.2 w.2.1.1 :=
      fun ⟨hp, hs⟩ ↦ ⟨hp, fun h ↦ hs
        ((exists_isSome_toSplitCache_fst_secretEncoding_enc_iff hd.keySeparated).2 h)⟩
    rcases h with hhm | hf | hx
    · exact .inl ((conflict_or_exists_isSome_of_hiddenHitMixed_withPost hd
        (linkedRouteAdv vp hn hnm adv) (fun _ _ ht ↦ linkedRedirect_of_not_isLinked ht)
        (fun _ _ _ _ _ ↦ rfl) hw (hns hhm).1).resolve_right (hns hhm).2)
    · exact hF w hw hf
    · exact hX w hw (hns hx).1 (hns hx).2

/-! ## The run -/

/-- The events of the verifying run with a further charge `χ`, the key clash read in the ideal
game as an event `F`, charged by a seed hazard `H₀` at `c₀`, or an event `E` of probability at
most `e`: at most `B + (e + (qh + V + 1) · weightedTargetCoverBound h a k qs (qh + V) (qs / |Y|))`
when `χ` with `c₀` is within `B`. -/
private theorem prEvent_romSchemeRun_verifyingAdv_le_of_clash
    (hd : (shakeCore vp).KeyDiscipline vp) (h32 : vp.params.n = 32)
    (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs)
    (X : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache → Prop)
    (χ : DeferredCharge (shakeCore vp) pkSeed)
    (H₀ : (shakeCore vp).SkSeed × (shakeCore vp).SkPrf → (hashSpec (shakeCore vp)).QueryCache →
      Prop) (c₀ : (hashSpec (shakeCore vp)).QueryCache → ℝ≥0∞)
    (hH₀ : ∀ C, Pr{let s ← $ᵗ ((shakeCore vp).SkSeed × (shakeCore vp).SkPrf)}[H₀ s C] ≤ c₀ C)
    (F : (shakeCore vp).SkSeed × (shakeCore vp).SkPrf → DeriveOutcome (shakeCore vp) ×
      SecretEncoding.SplitCache (hashSpec (shakeCore vp)) (DeriveQuery (shakeCore vp))
        (shakeCore vp).Y → Prop)
    (hF : ∀ s o (st : LabState (shakeCore vp)),
      F s (o, (slhGraph (shakeCore vp) pkSeed).toSplitCache st) → H₀ s st.1)
    (E : ((shakeCore vp).SkSeed × (shakeCore vp).SkPrf) × DeriveOutcome (shakeCore vp) ×
      SecretEncoding.SplitCache (hashSpec (shakeCore vp)) (DeriveQuery (shakeCore vp))
        (shakeCore vp).Y → Prop) {e : ℝ≥0∞}
    (hE : Pr{let w ← idealDraw (core := shakeCore vp) (Equiv.refl _) optRand pkSeed
                (verifyingAdv vp h32.le hnm adv)}[E w] ≤ e)
    (hclash : ∀ w, RunPrfKeyClash id pkSeed pkSeed (DeriveOutcome.fill (shakeCore vp) w.1 w.2.1,
        (secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).merge w.1 w.2.2) → F w.1 w.2 ∨ E w)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (hX : χ.Charges (verifyingAdv vp h32.le hnm adv) X)
    (hbud : χ.WithinBudget (verifyingAdv vp h32.le hnm adv) c₀ B) :
    Pr{let z ← romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
        (verifyingAdv vp h32.le hnm adv)}[
      ((RunTargetCollision (shakeCore vp) (Equiv.refl _) z ∨ RunHiddenHitMixed vp z) ∨
        (RunPrfKeyClash id pkSeed pkSeed z ∨ X z)) ∨ RunItsrCovered (shakeCore vp) z] ≤
    B + (e + ((qh + GeneralScheme.verifyInternalQueryBound vp.params : ℕ) + 1) *
      KeyedHash.Covering.weightedTargetCoverBound vp.params.h vp.params.a vp.params.k qs
        (qh + GeneralScheme.verifyInternalQueryBound vp.params)
        ((qs : ℝ≥0∞) / Nat.card (shakeCore vp).Y)) := by
  set χ' := (DeferredCharge.ofSeed (pkSeed := pkSeed) H₀ c₀ hH₀).add χ
  refine (prEvent_romSchemeRun_pure_le_prEvent_idealDraw_or _ optRand pkSeed _ _).trans <|
    (prEvent_mono _ _ _ fun w h ↦ ?_).trans <|
    (prEvent_or_le _ _ _).trans <| add_le_add
      (prEvent_idealDraw_verifyingAdv_le_of_charged hd h32.le hnm adv F X χ'
        (fun w _ h ↦ .inr (.inr (.inr (.inl (hF _ _ _ h)))))
        (fun w hw h hs ↦ (hX w hw h hs).imp_right (Or.imp_right fun h ↦ h.elim (.inl ∘ .inr)
          (.inr ∘ .inr))) B hB
        fun z hz ↦ (le_of_eq (by simp only [χ', DeferredCharge.add, DeferredCharge.ofSeed,
          Pi.add_apply, Pi.zero_apply, zero_add])).trans (hbud z hz))
      ((prEvent_or_le _ _ _).trans (add_le_add hE (prEvent_idealDraw_runItsrCovered_le _ optRand
        pkSeed (romQueryBound_verifyingAdv h32.le hnm hadv))))
  rcases h with (((htc | hhm) | hk | hx) | hit) | hs
  · exact .inl (.inl (.inl (.inl htc)))
  · exact .inl (.inl (.inl (.inr hhm)))
  · rcases hclash w hk with h | h
    exacts [.inl (.inl (.inr (.inl h))), .inr (.inl h)]
  · exact .inl (.inl (.inr (.inr hx)))
  · exact .inr (.inr hit)
  · exact .inl (.inr hs)

/-- **The events of the verifying run, with a further charge.** Under the key discipline, at
`n = 32`, for an adversary with hash budget `qh` and signing budget `qs`, a further event `X` of
the run charged to a further charge `χ`, and a cost `κ` covering `χ` on top of the joint budget of
the message-`PRF` key: the run at public seed `pkSeed` against the verifying adversary fires a
same-key target collision, a mixed hidden-value hit, a clash of the message-`PRF` key at
`opt_rand = PK.seed`, `X` or interleaved-target coverage with probability at most
`securityBound vp.params |Y| 2 1 (qh + V) qs + (qs + 1) / |Y| + κ`. -/
theorem prEvent_romSchemeRun_verifyingAdv_le_add (hd : (shakeCore vp).KeyDiscipline vp)
    (h32 : vp.params.n = 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs)
    (X : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache → Prop)
    (χ : DeferredCharge (shakeCore vp) pkSeed) (κ : ℝ≥0∞) (hκ : κ ≠ ⊤)
    (hX : χ.Charges (verifyingAdv vp h32.le hnm adv) X)
    (hbud : χ.WithinBudget (verifyingAdv vp h32.le hnm adv)
      (fun C ↦ hmsgCharge (shakeCore vp) C + (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
      ((2 * ((qh : ℝ≥0∞) + 2 * GeneralScheme.verifyInternalQueryBound vp.params) + qs + 1) /
        Nat.card (shakeCore vp).Y + κ)) :
    Pr{let z ← romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
        (verifyingAdv vp h32.le hnm adv)}[
      ((RunTargetCollision (shakeCore vp) (Equiv.refl _) z ∨ RunHiddenHitMixed vp z) ∨
        (RunPrfKeyClash id pkSeed pkSeed z ∨ X z)) ∨ RunItsrCovered (shakeCore vp) z] ≤
    securityBound vp.params (Nat.card (shakeCore vp).Y) 2 1
        (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
      ((qs : ℝ≥0∞) + 1) / Nat.card (shakeCore vp).Y + κ := by
  refine (prEvent_romSchemeRun_verifyingAdv_le_of_clash hd h32 hnm adv hadv X χ
    (fun s C ↦ HmsgAtPrfKey id s.2 C ∨ s.2 = pkSeed)
    (fun C ↦ hmsgCharge (shakeCore vp) C + (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
    (fun C ↦ (prEvent_or_le _ _ _).trans <| add_le_add
      (prEvent_hmsgAtPrfKey_le Function.injective_id le_rfl C)
      (SampleableType.prEvent_uniformSample_prod_le_of_forall_fst _ fun _ ↦
        (SampleableType.prEvent_uniformSample_eq_singleton_natCard _).le))
    (fun s z ↦ RunPrfKeyHit id pkSeed (DeriveOutcome.fill (shakeCore vp) s z.1,
      (secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).merge s z.2))
    (fun s o st h ↦ hmsgAtPrfKey_or_eq_of_runPrfKeyHit _ pkSeed id pkSeed s o st h)
    (fun _ ↦ False) (e := 0) (by simp) (fun _ h ↦ .inl (by
      rcases h with ⟨h, -⟩ | h
      exacts [.inl h, .inr h])) _
    (ENNReal.add_ne_top.2 ⟨div_natCard_ne_top (by simp [ENNReal.mul_eq_top]), hκ⟩) hX
    hbud).trans_eq ?_
  simp only [securityBound, ENNReal.div_eq_inv_mul, zero_add]
  push_cast
  ring

/-- **The events of the verifying run, with a further charge, hedged form.** As
`prEvent_romSchemeRun_verifyingAdv_le_add`, with `optRand pk` equal to `PK.seed` with probability
at most `ε` at every public key and a cost `κ` covering `χ` on top of the joint budget of the
fixed key: the bound is
`securityBound vp.params |Y| 2 1 (qh + V) qs + 1 / |Y| + qs · ε · (qh + V + qs + 1) / |Y| + κ`.
The fixed key is charged inside the joint potential, and the `H_msg` point at the key with a
randomizer derivation at `PK.seed` by the product bound. -/
theorem prEvent_romSchemeRun_verifyingAdv_le_add_hedged (hd : (shakeCore vp).KeyDiscipline vp)
    (h32 : vp.params.n = 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = pkSeed] ≤ ε)
    (X : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache → Prop)
    (χ : DeferredCharge (shakeCore vp) pkSeed) (κ : ℝ≥0∞) (hκ : κ ≠ ⊤)
    (hX : χ.Charges (verifyingAdv vp h32.le hnm adv) X)
    (hbud : χ.WithinBudget (verifyingAdv vp h32.le hnm adv)
      (fun _ ↦ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
      ((2 * ((qh : ℝ≥0∞) + 2 * GeneralScheme.verifyInternalQueryBound vp.params) + 1) /
        Nat.card (shakeCore vp).Y + κ)) :
    Pr{let z ← romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
        (verifyingAdv vp h32.le hnm adv)}[
      ((RunTargetCollision (shakeCore vp) (Equiv.refl _) z ∨ RunHiddenHitMixed vp z) ∨
        (RunPrfKeyClash id pkSeed pkSeed z ∨ X z)) ∨ RunItsrCovered (shakeCore vp) z] ≤
    securityBound vp.params (Nat.card (shakeCore vp).Y) 2 1
        (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
      1 / Nat.card (shakeCore vp).Y +
      qs * ε * (((qh + GeneralScheme.verifyInternalQueryBound vp.params : ℕ) : ℝ≥0∞) + qs + 1) /
        Nat.card (shakeCore vp).Y + κ := by
  refine (prEvent_romSchemeRun_verifyingAdv_le_of_clash hd h32 hnm adv hadv X χ
    (fun s _ ↦ s.2 = pkSeed) (fun _ ↦ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
    (fun _ ↦ SampleableType.prEvent_uniformSample_prod_le_of_forall_fst _ fun _ ↦
      (SampleableType.prEvent_uniformSample_eq_singleton_natCard _).le)
    (fun s _ ↦ s.2 = pkSeed) (fun _ _ _ h ↦ h)
    (fun w ↦ HmsgAtPrfKey id w.1.2 w.2.2.1 ∧ RandDerivedAt pkSeed w.2.2.2)
    (prEvent_idealDraw_hmsgAtPrfKey_and_randDerivedAt_le le_rfl _ optRand pkSeed
      Function.injective_id hε (romQueryBound_verifyingAdv h32.le hnm hadv))
    (fun w h ↦ (hmsgAtPrfKey_and_randDerivedAt_or_eq_of_runPrfKeyClash _ pkSeed id pkSeed pkSeed
      w.1 w.2.1 w.2.2 h).symm) _
    (ENNReal.add_ne_top.2 ⟨div_natCard_ne_top (by simp [ENNReal.mul_eq_top]), hκ⟩) hX
    hbud).trans_eq ?_
  simp only [securityBound, ENNReal.div_eq_inv_mul]
  push_cast
  ring

/-- **The events of the verifying run, with no further charge.** Under the key discipline, at
`n = 32`, for an adversary with hash budget `qh` and signing budget `qs`, the run at public seed
`pkSeed` against the verifying adversary fires a same-key target collision, a mixed hidden-value
hit, a clash of the message-`PRF` key at `opt_rand = PK.seed` or interleaved-target coverage with
probability at most `securityBound vp.params |Y| 2 1 (qh + V) qs + (qs + 1) / |Y|`. -/
theorem prEvent_romSchemeRun_verifyingAdv_le (hd : (shakeCore vp).KeyDiscipline vp)
    (h32 : vp.params.n = 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let z ← romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
        (verifyingAdv vp h32.le hnm adv)}[
      ((RunTargetCollision (shakeCore vp) (Equiv.refl _) z ∨ RunHiddenHitMixed vp z) ∨
        RunPrfKeyClash id pkSeed pkSeed z) ∨ RunItsrCovered (shakeCore vp) z] ≤
    securityBound vp.params (Nat.card (shakeCore vp).Y) 2 1
        (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
      ((qs : ℝ≥0∞) + 1) / Nat.card (shakeCore vp).Y := by
  refine (prEvent_mono _ _ _ fun z h ↦ h.imp_left (Or.imp_right .inl)).trans
    ((prEvent_romSchemeRun_verifyingAdv_le_add hd h32 hnm adv hadv (fun _ ↦ False)
      (.ofSeed (fun _ _ ↦ False) 0 fun _ ↦ by simp) 0 ENNReal.zero_ne_top
      (fun _ _ h ↦ h.elim) fun z hz ↦ ?_).trans_eq (add_zero _))
  have h := two_mul_encard_keyEntries_div_add_seedCharge_add_hmsgCharge_le_of_mem_support
    hd.keySeparated (romQueryBound_verifyingAdv h32.le hnm hadv) hz
  simp only [DeferredCharge.ofSeed, Pi.zero_apply, add_zero] at h ⊢
  refine h.trans_eq ?_
  push_cast
  ring_nf

/-! ## The advantage -/

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32`, per public seed, with a further charge.** At
`n = 32` and `n ≤ m`, under the canonical address bounds, for every public seed `pkSeed`, every
`opt_rand` distribution and an adversary with hash budget `qh` and signing budget `qs`, let the
virtual hit or the honest input at a linked point, off the seed hazard, imply at every point of
the deferred lab run against the verifying adversary, its end fill and drawn seeds, a conflict, a
target collision at a node key or a hazard of a further charge `χ`, and let `κ` cover `χ` on top
of the joint budget of the message-`PRF` key. Then the strong advantage of the adversary against
`shakeRomScheme` at `pkSeed` is at most
`securityBound vp.params |Y| 2 1 (qh + V) qs + (qs + 1) / |Y| + κ`. -/
theorem shakeStrongAdvantage_pure_le_securityBound_add (hb : CanonicalAddressBounds vp.params)
    (h32 : vp.params.n = 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) (χ : DeferredCharge (shakeCore vp) pkSeed) (κ : ℝ≥0∞)
    (hκ : κ ≠ ⊤)
    (hX : χ.Charges (verifyingAdv vp h32.le hnm adv.toUnforgeableAdversary)
      fun z ↦ VirtualHit vp z ∨ LinkedHonestInput vp z)
    (hbud : χ.WithinBudget (verifyingAdv vp h32.le hnm adv.toUnforgeableAdversary)
      (fun C ↦ hmsgCharge (shakeCore vp) C + (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
      ((2 * ((qh : ℝ≥0∞) + 2 * GeneralScheme.verifyInternalQueryBound vp.params) + qs + 1) /
        Nat.card (shakeCore vp).Y + κ)) :
    shakeStrongAdvantage vp adv ≤
      securityBound vp.params (Nat.card (shakeCore vp).Y) 2 1
          (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
        ((qs : ℝ≥0∞) + 1) / Nat.card (shakeCore vp).Y + κ :=
  (shakeStrongAdvantage_pure_le_viewEvents h32 hnm pkSeed adv).trans
    (prEvent_romSchemeRun_verifyingAdv_le_add (keyDiscipline_shakePrimitives vp hb) h32 hnm
      adv.toUnforgeableAdversary hadv _ χ κ hκ hX hbud)

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32`, per public seed, with a further charge, hedged
form.** As `shakeStrongAdvantage_pure_le_securityBound_add`, with `optRand pk` equal to `PK.seed`
with probability at most `ε` at every public key and `κ` covering `χ` on top of the joint budget of
the fixed key: the strong advantage is at most
`securityBound vp.params |Y| 2 1 (qh + V) qs + 1 / |Y| + qs · ε · (qh + V + qs + 1) / |Y| + κ`. -/
theorem shakeStrongAdvantage_pure_le_securityBound_add_hedged
    (hb : CanonicalAddressBounds vp.params) (h32 : vp.params.n = 32)
    (hnm : vp.params.n ≤ vp.params.m)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = pkSeed] ≤ ε)
    (χ : DeferredCharge (shakeCore vp) pkSeed) (κ : ℝ≥0∞) (hκ : κ ≠ ⊤)
    (hX : χ.Charges (verifyingAdv vp h32.le hnm adv.toUnforgeableAdversary)
      fun z ↦ VirtualHit vp z ∨ LinkedHonestInput vp z)
    (hbud : χ.WithinBudget (verifyingAdv vp h32.le hnm adv.toUnforgeableAdversary)
      (fun _ ↦ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
      ((2 * ((qh : ℝ≥0∞) + 2 * GeneralScheme.verifyInternalQueryBound vp.params) + 1) /
        Nat.card (shakeCore vp).Y + κ)) :
    shakeStrongAdvantage vp adv ≤
      securityBound vp.params (Nat.card (shakeCore vp).Y) 2 1
          (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
        1 / Nat.card (shakeCore vp).Y +
        qs * ε * (((qh + GeneralScheme.verifyInternalQueryBound vp.params : ℕ) : ℝ≥0∞) + qs +
          1) / Nat.card (shakeCore vp).Y + κ :=
  (shakeStrongAdvantage_pure_le_viewEvents h32 hnm pkSeed adv).trans
    (prEvent_romSchemeRun_verifyingAdv_le_add_hedged (keyDiscipline_shakePrimitives vp hb) h32 hnm
      adv.toUnforgeableAdversary hadv hε _ χ κ hκ hX hbud)

end SLHDSA.Security
