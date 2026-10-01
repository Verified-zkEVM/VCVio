/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import Examples.PRFTagReader.DirectCoupling
public import Examples.PRFTagReader.DirectCoupling.StepLemmas
public import Examples.PRFTagReader.MultipleToHybrid.EagerSetup
public import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# PRF Tag/Reader Protocol — Direct Coupling, Slot-Zero Tag Step

The slot-zero tag (`Sum.inl tag` with `s.sessionsUsed tag = 0`) induction step of the direct
M_ideal/S_ideal coupling aux `multipleBadEager_le_singleEager_DC_aux`. At a slot-zero state both
worlds read the same reference cell `((tag, 0), n)` of the shared `gS`, so the `Sum.inl tag` branch
of `multipleBadTableHandlerFine` is byte-identical to the coarse handler and does not consume the
fine table `gFine`.

The head step coincides with the single-table tag step
(`multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero`); the inner
`gFine ← $ᵗ` binder is commuted past the step at the measure level and the induction hypothesis
applies on the post-step state, at the extended cache on a cache miss or the unchanged cache on a
cache hit.

## Main results

* `dcAux_tag_slotZero` — the slot-zero tag induction step of the direct-coupling aux, taking the
  induction hypothesis as an explicit premise.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section DirectCouplingCompose

variable {TagId Nonce Digest : Type} {sessionsPerTag : ℕ}
  [DecidableEq TagId] [Fintype TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag]

namespace UnlinkReduction

/-- The slot-zero tag (`Sum.inl tag`, `s.sessionsUsed tag = 0`) induction step of the direct
M_ideal/S_ideal coupling aux. The induction hypothesis is supplied as the explicit premise `ih`;
the conclusion is the aux bound specialized to the adversary `query (Sum.inl tag) >>= k` at a
slot-zero state. -/
lemma dcAux_tag_slotZero [Fintype Nonce] [Fintype Digest] (out : Bool)
    (qRInit qR qT : ℕ)
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (R : Finset Nonce)
    (hqRle : qR + R.card ≤ qRInit)
    (hcInv : ∀ tag : TagId, ∀ sid : Fin sessionsPerTag, sid ≠ 0 →
        ∀ n : Nonce, c ((tag, sid), n) = none)
    (hRespInv : ∀ tag : TagId, ∀ n : Nonce, n ∉ R →
        c ((tag, (0 : Fin sessionsPerTag)), n) ≠ none →
        sB.responses (tag, n) ≠ none)
    (tag : TagId)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (ih : ∀ (u : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag))
        (qR qT : ℕ) (s : UnlinkState TagId)
        (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
        (sB : UnlinkBadState TagId Nonce Digest) (R : Finset Nonce),
        OracleComp.IsQueryBoundP (k u) (·.isRight) qR →
        OracleComp.IsQueryBoundP (k u) (·.isLeft) qT →
        qR + R.card ≤ qRInit →
        (∀ tag : TagId, ∀ sid : Fin sessionsPerTag, sid ≠ 0 →
          ∀ n : Nonce, c ((tag, sid), n) = none) →
        (∀ tag : TagId, ∀ n : Nonce, n ∉ R →
          c ((tag, (0 : Fin sessionsPerTag)), n) ≠ none →
          sB.responses (tag, n) ≠ none) →
        Pr{let b ← (do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
              (simulateQ (multipleBadTableHandlerFine
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine) (k u)).run (s, sB))}[b = out] ≤
          Pr{let b ← (do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
              (k u)).run' s)}[b = out] +
          Pr{let z ← (do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine) (k u)).run (s, sB))}[z.2.bad] +
          ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
          ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
          ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞))
    (hqR : OracleComp.IsQueryBoundP (liftM (OracleSpec.query (Sum.inl tag)) >>= k)
      (·.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP (liftM (OracleSpec.query (Sum.inl tag)) >>= k)
      (·.isLeft) qT)
    (hslot : s.sessionsUsed tag < sessionsPerTag)
    (hzero : s.sessionsUsed tag = 0) :
    Pr{let b ← (do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine)
            (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run (s, sB))}[b = out] ≤
      Pr{let b ← (do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
          (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run' s)}[b = out] +
      Pr{let z ← (do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandlerFine
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine)
            (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run (s, sB))}[z.2.bad] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  -- Slot-zero tag case (k = 0 fresh): the `Sum.inl tag` branch of `multipleBadTableHandlerFine`
  -- `multipleBadTableHandlerFine` is byte-identical to the coarse handler — it does not
  -- consume `gFine`. So the head step is the same as the coarse version; we mirror the
  -- coarse closure (Phase A handler unfolds, Phase B `$ᵗ gS`/`$ᵗ Nonce` commutation,
  -- Phase C empty-`D` `wp_le_add_add_of_disagree`, Phase D per-`n` cache split),
  -- but with `gFine ← $ᵗ` threaded as an extra binder. We commute `gFine ← $ᵗ` past the
  -- step at the measure level via `OracleComp.evalDist_bind_bind_swap`, then apply IH on the
  -- new state at the extended cache (Case B) or the unchanged cache (Case A).
  have hqRk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isRight) qR := by
    have := hqR
    rw [OracleComp.isQueryBoundP_query_bind_iff] at this
    simpa using this.2
  have hqTsplit := hqT
  rw [OracleComp.isQueryBoundP_query_bind_iff] at hqTsplit
  have hqTpos : 0 < qT := hqTsplit.1.resolve_left (fun h => absurd rfl h)
  obtain ⟨qT', rfl⟩ : ∃ qT', qT = qT' + 1 := ⟨qT - 1, by omega⟩
  have hqTk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isLeft) qT' := fun u => by
    simpa using hqTsplit.2 u
  -- Post-step state (shared between M and S under hzero).
  set advM : UnlinkState TagId :=
    { s with sessionsUsed :=
        Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } with hadvM
  -- M-Fine step under hzero: same as coarse — the `Sum.inl tag` branch of the Fine handler
  -- does not depend on `gFine`. By
  -- `multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero`,
  -- M-handler step = S-handler step, then
  -- unfold via `singleTableHandler_tag_run_of_lt` and use `sidH = 0` (from hzero).
  have hMstep_with_bad : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      ∀ gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest,
      multipleBadTableHandlerFine (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
      = ($ᵗ Nonce) >>= fun n =>
          pure (some (⟨n, OracleComp.tableExtending c gS
              ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest),
            advM,
            multipleBadAdvance tag sB
              (some (⟨n, OracleComp.tableExtending c gS
                ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest))) := by
    intro gS gFine
    change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c gS)) (Sum.inl tag)) s
        >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1))
        = _
    rw [multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero
        (OracleComp.tableExtending c gS) tag s hzero,
      singleTableHandler_tag_run_of_lt (OracleComp.tableExtending c gS) tag s hslot]
    have hsid : (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) =
        (0 : Fin sessionsPerTag) := Fin.ext hzero
    rw [hsid, ← hadvM]
    exact bind_assoc ..
  -- S-side step, no bad wrap.
  have hSstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      singleTableHandler (OracleComp.tableExtending c gS)
        (Sum.inl tag) s
      = ($ᵗ Nonce) >>= fun n =>
          pure (some (⟨n, OracleComp.tableExtending c gS
              ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest),
            advM) := by
    intro gS
    rw [singleTableHandler_tag_run_of_lt (OracleComp.tableExtending c gS) tag s hslot]
    have hsid : (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) =
        (0 : Fin sessionsPerTag) := Fin.ext hzero
    rw [hsid, ← hadvM]
  -- LHS: rewrite `gS ← $ᵗ; gFine ← $ᵗ; step >>= ...` into
  -- `gS ← $ᵗ; gFine ← $ᵗ; n ← $ᵗ Nonce; ...`.
  have hM_eq {α : Type}
      (observe : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) → α) :
      (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          observe <$>
            (simulateQ (multipleBadTableHandlerFine
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c gS)) gFine)
              (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run (s, sB))
      = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let n ← $ᵗ Nonce
            observe <$>
              (simulateQ (multipleBadTableHandlerFine
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine)
                (k (some (⟨n, OracleComp.tableExtending c gS
                    ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest)))).run
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, OracleComp.tableExtending c gS
                    ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest)))) := by
    simp only [multipleBadTableFine_run_query_bind', map_bind]
    refine bind_congr fun gS => ?_
    refine bind_congr fun gFine => ?_
    rw [hMstep_with_bad gS gFine]
    exact bind_assoc ..
  have hLHS_eq := hM_eq (fun z => z.1)
  have hRHS_eq :
      (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
            (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run' s)
      = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let n ← $ᵗ Nonce
            (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
              (k (some (⟨n, OracleComp.tableExtending c gS
                  ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                  TagTranscript Nonce Digest)))).run' advM) := by
    simp only [singleTable_run'_query_bind']
    refine bind_congr fun gS => ?_
    rw [hSstep gS]
    exact bind_assoc ..
  have hBAD_eq := hM_eq (fun z => (z.1, z.2.2))
  have hLHS_ev := congrArg (fun mx => Pr{let b ← mx}[b = out]) hLHS_eq
  have hRHS_ev := congrArg (fun mx => Pr{let b ← mx}[b = out]) hRHS_eq
  have hBAD_ev := congrArg (fun mx => Pr{let z ← mx}[z.2.bad = true]) hBAD_eq
  simp only [expect_norm] at hLHS_ev hRHS_ev hBAD_ev ⊢
  rw [hLHS_ev, hRHS_ev, hBAD_ev]
  -- Phase B. Commute outer `$ᵗ gS`, `$ᵗ gFine` past inner `$ᵗ Nonce` at the measure level
  -- so the shared nonce draw is outermost. We push `n` out one binder at a time.
  have hLHS_comm :
      𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let n ← $ᵗ Nonce
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                z.1) <$>
              (simulateQ (multipleBadTableHandlerFine
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine)
                (k (some (⟨n, OracleComp.tableExtending c gS
                    ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest)))).run
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, OracleComp.tableExtending c gS
                    ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest))))]
      = 𝒟[(do let n ← $ᵗ Nonce
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  z.1) <$>
                (simulateQ (multipleBadTableHandlerFine
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c gS)) gFine)
                  (k (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                      TagTranscript Nonce Digest)))).run
                  (advM, multipleBadAdvance tag sB
                    (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                      TagTranscript Nonce Digest))))] := by
    let : MeasurableSpace Digest := ⊤
    let : MeasurableSpace Nonce := ⊤
    exact evalDist_bind_bind_bind_rotate _ _ _ _ .of_discrete
  have hRHS_comm :
      𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let n ← $ᵗ Nonce
            (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
              (k (some (⟨n, OracleComp.tableExtending c gS
                  ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                  TagTranscript Nonce Digest)))).run' advM)]
      = 𝒟[(do let n ← $ᵗ Nonce
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
                (k (some (⟨n, OracleComp.tableExtending c gS
                    ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest)))).run' advM)] :=
    OracleComp.evalDist_bind_bind_swap
      ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
  have hBAD_comm :
      letI : MeasurableSpace (Bool × UnlinkBadState TagId Nonce Digest) := ⊤
      𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let n ← $ᵗ Nonce
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine)
                (k (some (⟨n, OracleComp.tableExtending c gS
                    ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest)))).run
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, OracleComp.tableExtending c gS
                    ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest))))]
      = 𝒟[(do let n ← $ᵗ Nonce
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadTableHandlerFine
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c gS)) gFine)
                  (k (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                      TagTranscript Nonce Digest)))).run
                  (advM, multipleBadAdvance tag sB
                    (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                      TagTranscript Nonce Digest))))] := by
    let : MeasurableSpace Digest := ⊤
    let : MeasurableSpace Nonce := ⊤
    let : MeasurableSpace (Bool × UnlinkBadState TagId Nonce Digest) := ⊤
    exact evalDist_bind_bind_bind_rotate _ _ _ _ .of_discrete
  have hLHS_cm := (EvalDistEq.of_evalDist_eq hLHS_comm).prEvent_eq fun b => b = out
  have hRHS_cm := (EvalDistEq.of_evalDist_eq hRHS_comm).prEvent_eq fun b => b = out
  have hBAD_cm := (EvalDistEq.of_evalDist_eq hBAD_comm).prEvent_eq fun z => z.2.bad = true
  simp only [expect_norm] at hLHS_cm hRHS_cm hBAD_cm
  rw [hLHS_cm, hRHS_cm, hBAD_cm]
  -- Phase C. Split `qRInit * (qT' + 1) / |Nonce|` into `qRInit / |Nonce| + qRInit * qT' / |Nonce|`
  -- and reassociate. Apply the disagree lemma with empty `D` on the inner `$ᵗ Nonce` (since under
  -- hzero, M and S do the same step — there is no per-step disagreement to charge, and no tag-side
  -- slack is incurred).
  have hSplit : ((qRInit * (qT' + 1) : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞)
      = ((qRInit : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
        ((qRInit * qT' : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
    rw [show qRInit * (qT' + 1) = qRInit + qRInit * qT' from by ring,
      Nat.cast_add, ENNReal.add_div]
  rw [hSplit]
  rw [show ∀ a b c d e f : ℝ≥0∞,
        a + b + c + (d + e) + f = a + b + d + (c + e + f) from
        fun a b c d e f => by ring]
  refine wp_le_add_add_of_disagree (D := fun _ : Nonce => False) ?_ (fun _ =>
    wp_le_of_forall_le _ fun _ => wp_le_of_forall_le _ fun _ => prEvent_le_one _) ?_
  · simp
  intro n _ _hnD
  -- Phase D. Per-`n` bound. Case-split on `c ((tag, 0), n)`.
  rcases hc : c ((tag, (0 : Fin sessionsPerTag)), n) with _ | u₀
  · -- Case B: cache miss. Marginalize cell via `evalDist_bind_bind_update`, then
    -- apply IH at extended cache `c.cacheQuery ((tag, 0), n) u`.
    have hmarg : ∀ {β : Type} [MeasurableSpace β]
        (Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp β),
        𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest); Mψ gS)] =
        𝒟[(do let u ← $ᵗ Digest
              let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              Mψ (Function.update gS' ((tag, (0 : Fin sessionsPerTag)), n) u))] := by
      intro β _ Mψ
      let : MeasurableSpace Digest := ⊤
      exact (evalDist_bind_bind_update ($ᵗ Digest)
        ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
        SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample
        ((tag, (0 : Fin sessionsPerTag)), n) Mψ).symm
    have hmargW : ∀ Φ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ℝ≥0∞,
        wp⟦($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest) : ProbComp _)⟧ Φ =
          wp⟦($ᵗ Digest : ProbComp Digest)⟧ fun u =>
            wp⟦($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest) : ProbComp _)⟧ fun gS' =>
              Φ (Function.update gS' ((tag, (0 : Fin sessionsPerTag)), n) u) := fun Φ => by
      let : MeasurableSpace ((TagId × Fin sessionsPerTag) × Nonce → Digest) := ⊤
      simpa only [bind_pure, expect_norm] using
        EvalDistEq.wp_eq (EvalDistEq.of_evalDist_eq (hmarg pure)) Φ
    have hext_eq : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
        (u : Digest),
        OracleComp.tableExtending c
            (Function.update gS' ((tag, (0 : Fin sessionsPerTag)), n) u) =
          OracleComp.tableExtending (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
            gS' := fun gS' u => by
      have h1 := OracleComp.tableExtending_update_of_none c gS' hc u
      have h2 := OracleComp.tableExtending_cacheQuery c gS'
        ((tag, (0 : Fin sessionsPerTag)), n) u
      exact h1.symm.trans h2.symm
    have hcell_u : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
        (u : Digest),
        OracleComp.tableExtending
            (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS'
            ((tag, (0 : Fin sessionsPerTag)), n) = u := fun gS' u => by
      rw [OracleComp.tableExtending_cacheQuery]
      simp [Function.update_self]
    have hLHS_marg :
        Pr{let b ← ((do
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  z.1) <$>
                (simulateQ (multipleBadTableHandlerFine
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c gS)) gFine)
                  (k (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                      TagTranscript Nonce Digest)))).run
                  (advM, multipleBadAdvance tag sB
                    (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                      TagTranscript Nonce Digest)))))}[b = out]
      = Pr{let b ← ((do
              let u ← $ᵗ Digest
              let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  z.1) <$>
                (simulateQ (multipleBadTableHandlerFine
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending
                      (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS'))
                    gFine)
                  (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                  (advM, multipleBadAdvance tag sB
                    (some (⟨n, u⟩ : TagTranscript Nonce Digest)))))}[b = out] := by
      simp only [expect_norm]
      rw [hmargW]
      refine MeasureProgramLogic.wp_congr _ fun u => MeasureProgramLogic.wp_congr _ fun gS' =>
        MeasureProgramLogic.wp_congr _ fun gFine => ?_
      rw [hext_eq gS' u, hcell_u gS' u]
    have hRHS_marg :
        Pr{let b ← ((do
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
                (k (some (⟨n, OracleComp.tableExtending c gS
                    ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                    TagTranscript Nonce Digest)))).run' advM))}[b = out]
      = Pr{let b ← ((do
              let u ← $ᵗ Digest
              let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (singleTableHandler (OracleComp.tableExtending
                  (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS'))
                (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' advM))}[b = out] := by
      simp only [expect_norm]
      rw [hmargW]
      refine MeasureProgramLogic.wp_congr _ fun u => MeasureProgramLogic.wp_congr _ fun gS' => ?_
      rw [hext_eq gS' u, hcell_u gS' u]
    have hBAD_marg :
        Pr{let z ← ((do
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadTableHandlerFine
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c gS)) gFine)
                  (k (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                      TagTranscript Nonce Digest)))).run
                  (advM, multipleBadAdvance tag sB
                    (some (⟨n, OracleComp.tableExtending c gS
                      ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                      TagTranscript Nonce Digest)))))}[z.2.bad = true]
      = Pr{let z ← ((do
              let u ← $ᵗ Digest
              let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadTableHandlerFine
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending
                      (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS'))
                    gFine)
                  (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                  (advM, multipleBadAdvance tag sB
                    (some (⟨n, u⟩ : TagTranscript Nonce Digest)))))}[z.2.bad = true] := by
      simp only [expect_norm]
      rw [hmargW]
      refine MeasureProgramLogic.wp_congr _ fun u => MeasureProgramLogic.wp_congr _ fun gS' =>
        MeasureProgramLogic.wp_congr _ fun gFine => ?_
      rw [hext_eq gS' u, hcell_u gS' u]
    simp only [expect_norm] at hLHS_marg hRHS_marg hBAD_marg
    rw [hLHS_marg, hRHS_marg, hBAD_marg]
    rw [show ∀ a b c : ℝ≥0∞, a + b + c = a + b + 0 + c from
          fun a b c => by ring]
    refine wp_le_add_add_of_disagree (mx := ($ᵗ Digest : ProbComp Digest))
      (D := fun _ : Digest => False) (by simp) (fun _ => wp_le_of_forall_le _ fun _ =>
        wp_le_of_forall_le _ fun _ => prEvent_le_one _) ?_
    intro u _ _
    have hcInv' : ∀ tag' : TagId, ∀ sid' : Fin sessionsPerTag, sid' ≠ 0 →
        ∀ n' : Nonce,
          (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
            ((tag', sid'), n') = none := by
      intro tag' sid' hsid' n'
      have hne : ((tag', sid'), n') ≠ ((tag, (0 : Fin sessionsPerTag)), n) := by
        intro h
        exact hsid' (congrArg (fun p => p.1.2) h)
      simp [OracleSpec.QueryCache.cacheQuery_of_ne, hne, hcInv tag' sid' hsid' n']
    have hRespInv' : ∀ tag' : TagId, ∀ n' : Nonce, n' ∉ R →
        (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
          ((tag', (0 : Fin sessionsPerTag)), n') ≠ none →
        (multipleBadAdvance tag sB
          (some (⟨n, u⟩ : TagTranscript Nonce Digest))).responses (tag', n') ≠ none := by
      intro tag' n' hn'R hne
      by_cases htagn : (tag', n') = (tag, n)
      · -- Same cell; the advance updates `responses` at this cell.
        have : (multipleBadAdvance tag sB
            (some (⟨n, u⟩ : TagTranscript Nonce Digest))).responses (tag', n') =
            (sB.responses.cacheQuery (tag, n)
              (u :: Option.getD (sB.responses (tag, n)) [])) (tag', n') := rfl
        rw [this, htagn, OracleSpec.QueryCache.cacheQuery_self]
        exact Option.some_ne_none _
      · -- Different cell; cache unchanged at this entry, responses unchanged.
        have hne_cell : ((tag', (0 : Fin sessionsPerTag)), n') ≠
            ((tag, (0 : Fin sessionsPerTag)), n) := by
          intro h
          exact htagn (Prod.ext (congrArg (fun p => p.1.1) h)
            (congrArg (fun p => p.2) h))
        have hc_unchanged : (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
            ((tag', (0 : Fin sessionsPerTag)), n') =
            c ((tag', (0 : Fin sessionsPerTag)), n') := by
          simp [OracleSpec.QueryCache.cacheQuery_of_ne, hne_cell]
        rw [hc_unchanged] at hne
        have hsb_unchanged : (multipleBadAdvance tag sB
            (some (⟨n, u⟩ : TagTranscript Nonce Digest))).responses (tag', n') =
            sB.responses (tag', n') := by
          change (sB.responses.cacheQuery (tag, n)
            (u :: Option.getD (sB.responses (tag, n)) [])) (tag', n') =
            sB.responses (tag', n')
          simp [OracleSpec.QueryCache.cacheQuery_of_ne, htagn]
        rw [hsb_unchanged]
        exact hRespInv tag' n' hn'R hne
    have hihB := ih (some (⟨n, u⟩ : TagTranscript Nonce Digest)) qR qT'
      advM (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
      (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest))) R
      (hqRk _) (hqTk _) hqRle hcInv' hRespInv'
    rw [← add_assoc, ← add_assoc]
    simpa only [expect_norm] using hihB
  · -- Case A: cache hit `u₀`. Cell read is `u₀` regardless of `gS`. Apply IH at unchanged
    -- cache `c`.
    have hcell : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
        OracleComp.tableExtending c gS ((tag, (0 : Fin sessionsPerTag)), n) = u₀ :=
      fun gS => by
        change (c ((tag, (0 : Fin sessionsPerTag)), n)).getD
            (gS ((tag, (0 : Fin sessionsPerTag)), n)) = u₀
        rw [hc]; rfl
    simp_rw [hcell]
    have hRespInv'' : ∀ tag' : TagId, ∀ n' : Nonce, n' ∉ R →
        c ((tag', (0 : Fin sessionsPerTag)), n') ≠ none →
        (multipleBadAdvance tag sB
          (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))).responses (tag', n') ≠ none := by
      intro tag' n' hn'R hne
      by_cases htagn : (tag', n') = (tag, n)
      · have heq : (multipleBadAdvance tag sB
            (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))).responses (tag', n') =
            (sB.responses.cacheQuery (tag, n)
              (u₀ :: Option.getD (sB.responses (tag, n)) [])) (tag', n') := rfl
        rw [heq, htagn, OracleSpec.QueryCache.cacheQuery_self]
        exact Option.some_ne_none _
      · have hsb_unchanged : (multipleBadAdvance tag sB
            (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))).responses (tag', n') =
            sB.responses (tag', n') := by
          change (sB.responses.cacheQuery (tag, n)
            (u₀ :: Option.getD (sB.responses (tag, n)) [])) (tag', n') =
            sB.responses (tag', n')
          simp [OracleSpec.QueryCache.cacheQuery_of_ne, htagn]
        rw [hsb_unchanged]
        exact hRespInv tag' n' hn'R hne
    have hihA := ih (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)) qR qT'
      advM c
      (multipleBadAdvance tag sB (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))) R
      (hqRk _) (hqTk _) hqRle hcInv hRespInv''
    rw [← add_assoc, ← add_assoc]
    simpa only [expect_norm] using hihA

end UnlinkReduction

end DirectCouplingCompose

end PRFTagReader
