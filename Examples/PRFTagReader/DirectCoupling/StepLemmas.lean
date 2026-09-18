/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import Examples.PRFTagReader.DirectCoupling
public import Examples.PRFTagReader.MultipleToHybrid.EagerSetup

/-!
# PRF Tag/Reader Protocol — Direct-Coupling Handler Step Lemmas

Per-query step shapes of the instrumented Fine handler and the single-table handler at
slot-positive states, together with the Fine handler's `cacheBad`-irrelevance bridge.

The step lemmas unfold one tag query of each side of the direct M/S coupling at the
slot-positive case (`s.sessionsUsed tag ≠ 0`): the M-side `multipleBadTableHandlerFine` on the
`slotZeroSubTable` of an extended table reads slot `0`, while the S-side `singleTableHandler`
reads the realized slot `⟨s.sessionsUsed tag, hslot⟩`, which is non-zero there
(`slotPositive_slotK_ne_zero`).

## Main results

* `slotPositive_MFine_tag_step` — the M-Fine tag-step shape at slot-positive states.
* `slotPositive_S_tag_step` — the S tag-step shape at slot-positive states.
* `evalSPMF_simulateQ_multipleBadTableHandlerFine_cacheBad_irrelevant` — Fine-run distributions
  after a `cacheBad` projection do not depend on the initial state's `cacheBad` field.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section DirectCouplingStepLemmas

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

namespace UnlinkReduction

/-! ### Slot-positive handler step characterizations

The next two lemmas explicitly unfold the M-Fine and S handler tag-step shapes at the
slot-positive case. They form the structural foundation of the slot-positive tag case:

* `slotPositive_MFine_tag_step` — the `Sum.inl tag` branch of `multipleBadTableHandlerFine` on
  the sub-table `slotZeroSubTable (tableExtending c gS)`, under `hslot ∧ ¬hzero`, samples a nonce
  and emits the transcript `⟨n, gS((tag, 0), n)⟩` (M reads cell `(tag, 0)` of `gS` because the
  sub-table embedding fixes slot 0), threading `multipleBadAdvance` through the bad state. Note
  the M-Fine tag branch does NOT depend on `gFine`.
* `slotPositive_S_tag_step` — the same shape on the single-session side: samples a nonce and emits
  `⟨n, gS((tag, slotK), n)⟩` where `slotK = ⟨s.sessionsUsed tag, hslot⟩`. Under `¬hzero`,
  `slotK ≠ 0`, so M and S read genuinely different cells.

Both step lemmas are direct corollaries of `multipleTableHandler_tag_run_of_lt` and
`singleTableHandler_tag_run_of_lt`, specialized to the slot-positive case where the
zero-slot rewrite `Fin.ext hzero` of the slot-zero tag case no longer applies. -/

omit [Nonempty TagId] [SampleableType Digest] in
/-- **M-Fine tag step at slot-positive.** Under `hslot : s.sessionsUsed tag < sessionsPerTag`,
the `multipleBadTableHandlerFine` `Sum.inl tag` branch on the sub-table
`slotZeroSubTable (tableExtending c gS)` samples a fresh nonce and emits the M-transcript
`⟨n, tableExtending c gS ((tag, 0), n)⟩` (M reads SLOT 0 of `gS` regardless of how many sessions
this tag has used), threading `multipleBadAdvance tag sB` through the bad state. The handler does
NOT depend on `gFine` on the tag branch. -/
lemma slotPositive_MFine_tag_step
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (gS gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (tag : TagId) (s : UnlinkState TagId) (sB : UnlinkBadState TagId Nonce Digest)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)
      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
        (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
    = ($ᵗ Nonce) >>= fun n =>
        pure (some (⟨n, OracleComp.tableExtending c gS
            ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest),
          { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) },
          multipleBadAdvance tag sB
            (some (⟨n, OracleComp.tableExtending c gS
              ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest))) := by
  change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)
      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
        (OracleComp.tableExtending c gS)) (Sum.inl tag)) s
      >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1))
      = _
  rw [multipleTableHandler_tag_run_of_lt _ tag s hslot]
  exact bind_assoc ..

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **S tag step at slot-positive.** Under `hslot : s.sessionsUsed tag < sessionsPerTag`,
the `singleTableHandler` `Sum.inl tag` branch on `tableExtending c gS` samples a fresh nonce and
emits the S-transcript `⟨n, tableExtending c gS ((tag, slotK), n)⟩` where
`slotK = ⟨s.sessionsUsed tag, hslot⟩`. Under `¬ s.sessionsUsed tag = 0`, this slot is non-zero, so
M and S read different cells of `gS`. -/
lemma slotPositive_S_tag_step
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (gS : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (tag : TagId) (s : UnlinkState TagId)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS) (Sum.inl tag) s
    = ($ᵗ Nonce) >>= fun n =>
        pure (some (⟨n, OracleComp.tableExtending c gS
            ((tag, ⟨s.sessionsUsed tag, hslot⟩), n)⟩ : TagTranscript Nonce Digest),
          { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }) :=
  singleTableHandler_tag_run_of_lt (OracleComp.tableExtending c gS) tag s hslot

/-- **Slot-positive slotK is non-zero.** At the slot-positive case
`¬ s.sessionsUsed tag = 0`, the realized session index `⟨s.sessionsUsed tag, hslot⟩` is
non-zero in `Fin sessionsPerTag`. -/
lemma slotPositive_slotK_ne_zero {TagId' : Type} {sessionsPerTag' : ℕ}
    [NeZero sessionsPerTag'] {tag : TagId'} {s : UnlinkState TagId'}
    (hslot : s.sessionsUsed tag < sessionsPerTag')
    (hzero : ¬ s.sessionsUsed tag = 0) :
    (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag') ≠ 0 := by
  intro h
  apply hzero
  have : (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag').val = (0 : Fin sessionsPerTag').val :=
    congrArg Fin.val h
  simpa using this

/-! ### Fine `cacheBad`-irrelevance bridge -/

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Fine handler is `cacheBad`-irrelevant.** Two initial bad states agreeing off `cacheBad`
produce identical Fine-run distributions after the projection `with cacheBad := cb`. Composes the
pointwise Fine→original bridge (`…_forget_cacheBad_pointwise_eq`) with the original-handler
irrelevance (`…_multipleBadTableHandler_cacheBad_irrelevant`). Used in the reader case to discard
the per-step `multipleBadReaderAdvance` perturbation of the initial state before applying the IH. -/
lemma evalSPMF_simulateQ_multipleBadTableHandlerFine_cacheBad_irrelevant
    {α : Type} (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId) (sB sB' : UnlinkBadState TagId Nonce Digest) (cb : Bool)
    (hSU : sB.sessionsUsed = sB'.sessionsUsed)
    (hR : sB.responses = sB'.responses) (hB : sB.bad = sB'.bad) :
    𝒮[(fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g gFine) oa).run (s, sB)]
      = 𝒮[(fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g gFine) oa).run (s, sB')] := by
  rw [evalSPMF_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_pointwise_eq
        g gFine oa (s, sB),
      evalSPMF_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_pointwise_eq
        g gFine oa (s, sB')]
  exact evalSPMF_simulateQ_multipleBadTableHandler_cacheBad_irrelevant g oa s sB sB' cb hSU hR hB

end UnlinkReduction

end DirectCouplingStepLemmas

end PRFTagReader
