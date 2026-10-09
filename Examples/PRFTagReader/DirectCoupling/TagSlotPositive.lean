/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import Examples.PRFTagReader.DirectCoupling
public import Examples.PRFTagReader.DirectCoupling.StepLemmas
public import Examples.PRFTagReader.DirectCoupling.Swap
public import Examples.PRFTagReader.MultipleToHybrid.EagerSetup
public import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# PRF Tag/Reader Protocol — Direct Coupling, Slot-Positive Tag Step

The slot-positive tag (`Sum.inl tag` with `1 ≤ s.sessionsUsed tag < sessionsPerTag`) induction
step of the direct M_ideal/S_ideal coupling aux `multipleBadEager_le_singleEager_DC_aux`. At a
slot-positive state the M side reads the slot-0 cell of `gS` (via `slotZeroSubTable`) while the S
side reads the realized slot-`K` cell, with `K = ⟨s.sessionsUsed tag, hslot⟩` non-zero.

Each side marginalizes its own cell via the single-cell helper
`evalDist_uniformSample_bind_update_map`, giving the induction hypothesis a fresh slot-0 draw on
the M side; the resulting slot-0 → slot-`K` cache extension is then bridged on the S side by the
permutation lemma `evalDist_singleTableHandler_cache_swap_eq`. Cell-pair independence gives
per-nonce equality off the multiple-bad flag, so the tag step charges no tag-side slack: the
per-step nonce-aliasing unit `qRInit / |Nonce|` carved out of the `qRInit·qT / |Nonce|` slack
absorbs the reader-touched-set mass `R.card / |Nonce|`, and no
`|TagId| · sessionsPerTag / |Digest|` charge is incurred.

## Main results

* `dcAux_tag_slotPositive` — the slot-positive tag induction step of the direct-coupling aux,
  taking the induction hypothesis as an explicit premise.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace PRFTagReader

section DirectCouplingCompose

variable {TagId Nonce Digest : Type} {sessionsPerTag : ℕ}
  [DecidableEq TagId] [Fintype TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag]

namespace UnlinkReduction

/-- The slot-positive tag (`Sum.inl tag`, `1 ≤ s.sessionsUsed tag < sessionsPerTag`) induction
step of the direct M_ideal/S_ideal coupling aux. The induction hypothesis is supplied as the
explicit premise `ih`; the conclusion is the aux bound specialized to the adversary
`query (Sum.inl tag) >>= k` at a slot-positive state. -/
lemma dcAux_tag_slotPositive [Fintype Nonce] [Fintype Digest] (out : Bool)
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
    (hzero : ¬ s.sessionsUsed tag = 0) :
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
  -- Slot-positive tag case (1 ≤ k < sp). M reads slot-0 cell, S reads slot-K cell (K ≠ 0).
  -- (K ≠ 0).
  -- **Cell-pair independence strategy.** Each side marginalizes its own cell via a
  -- single-cell helper (`evalDist_uniformSample_bind_update_map`), giving the IH a fresh
  -- slot-0 draw on the M side; the resulting slot-0 → slot-K cache extension is then
  -- bridged on the S side by the permutation lemma `evalDist_singleTableHandler_cache_swap_eq`.
  -- No per-step `cacheBadReader` charge is needed at this site: cell-pair independence gives
  -- per-`n` equality off the bad flag, so the tag step incurs no `|TagId| · sp / |Digest|` charge
  -- (the headline carries no tag-side slack).
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
  -- Post-step state (shared between M and S — both increment `sessionsUsed tag`).
  set advM : UnlinkState TagId :=
    { s with sessionsUsed :=
        Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } with hadvM
  -- Realized slot-K (non-zero by `hzero`).
  set slotK : Fin sessionsPerTag := ⟨s.sessionsUsed tag, hslot⟩ with hslotK
  have hslotK_ne : slotK ≠ 0 := slotPositive_slotK_ne_zero (sessionsPerTag' := sessionsPerTag)
    hslot hzero
  -- M-Fine and S step shapes via `slotPositive_MFine_tag_step` /
  -- `slotPositive_S_tag_step`. Note: M reads slot-0 cell of
  -- `gS` (via `slotZeroSubTable`) regardless of `hzero`; S reads slot-K cell where
  -- `slotK = ⟨s.sessionsUsed tag, hslot⟩` is non-zero by `hslotK_ne`.
  have hMstep : ∀ gS gFine,
      multipleBadTableHandlerFine (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
      = ($ᵗ Nonce) >>= fun n =>
          pure (some (⟨n, OracleComp.tableExtending c gS
              ((tag, (0 : Fin sessionsPerTag)), n)⟩ : TagTranscript Nonce Digest),
            advM,
            multipleBadAdvance tag sB
              (some (⟨n, OracleComp.tableExtending c gS
                ((tag, (0 : Fin sessionsPerTag)), n)⟩ :
                  TagTranscript Nonce Digest))) :=
    fun gS gFine => slotPositive_MFine_tag_step (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag) c gS gFine tag s sB hslot
  have hSstep : ∀ gS,
      singleTableHandler (OracleComp.tableExtending c gS)
        (Sum.inl tag) s
      = ($ᵗ Nonce) >>= fun n =>
          pure (some (⟨n, OracleComp.tableExtending c gS
              ((tag, slotK), n)⟩ : TagTranscript Nonce Digest), advM) := fun gS => by
    have := slotPositive_S_tag_step (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) c gS tag s hslot
    convert this using 1
  -- Unfold head queries on both sides.
  simp only [multipleBadTableFine_run_query_bind', singleTable_run'_query_bind', map_bind]
  -- Phase B-1: rewrite each of LHS, RHS, BAD so the head step exposes the inner `n ← $ᵗ`.
  have hM_eq {α : Type}
      (observe : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) → α) :
      (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let p ← multipleBadTableHandlerFine (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
          observe <$>
            (simulateQ (multipleBadTableHandlerFine
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c gS)) gFine) (k p.1)).run p.2)
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
    refine bind_congr fun gS => ?_
    refine bind_congr fun gFine => ?_
    rw [hMstep gS gFine]
    exact bind_assoc ..
  have hLHS_eq := hM_eq (fun z => z.1)
  have hRHS_eq :
      (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let p ← singleTableHandler (OracleComp.tableExtending c gS) (Sum.inl tag) s
          (simulateQ (singleTableHandler (OracleComp.tableExtending c gS)) (k p.1)).run' p.2)
      = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let n ← $ᵗ Nonce
            (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
              (k (some (⟨n, OracleComp.tableExtending c gS
                  ((tag, slotK), n)⟩ : TagTranscript Nonce Digest)))).run' advM) := by
    refine bind_congr fun gS => ?_
    rw [hSstep gS]
    exact bind_assoc ..
  have hBAD_eq := hM_eq (fun z => (z.1, z.2.2))
  rw [hLHS_eq, hRHS_eq, hBAD_eq]
  -- Phase B-2: commute outer `$ᵗ gS`, `$ᵗ gFine` past inner `$ᵗ Nonce` at the measure
  -- level so `n` is outermost. Identical structure to slot-zero (M-side LHS/BAD have the
  -- same shape — both read slot-0). RHS is shorter (no `gFine` binder).
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
                  ((tag, slotK), n)⟩ : TagTranscript Nonce Digest)))).run' advM)]
      = 𝒟[(do let n ← $ᵗ Nonce
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
                (k (some (⟨n, OracleComp.tableExtending c gS
                    ((tag, slotK), n)⟩ : TagTranscript Nonce Digest)))).run' advM)] :=
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
  rw [prEvent_congr_of_evalDist_eq _ _ hLHS_comm, prEvent_congr_of_evalDist_eq _ _ hRHS_comm,
    prEvent_congr_of_evalDist_eq _ _ hBAD_comm]
  -- Phase C: split `qRInit * (qT' + 1) / |Nonce|` into `qRInit / |Nonce| + qRInit * qT' / |Nonce|`
  -- and reassociate so the per-`n` obligation carries the reader-cell, nonce-remainder, and
  -- reader-slot slacks. No tag-side slack is charged here: cell-pair independence provides per-`n`
  -- equality off the bad flag.
  classical
  have hSplit : ((qRInit * (qT' + 1) : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞)
      = ((qRInit : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
        ((qRInit * qT' : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
    rw [show qRInit * (qT' + 1) = qRInit + qRInit * qT' from by ring,
      Nat.cast_add, ENNReal.add_div]
  rw [hSplit]
  rw [show ∀ a b c d e f : ℝ≥0∞,
        a + b + c + (d + e) + f = a + b + d + (c + e + f) from
        fun a b c d e f => by ring]
  refine prEvent_bind_le_add_bad_disagree (D := fun n : Nonce => n ∈ R) ?_ ?_
  · -- The reader-touched set `R` has uniform-sample probability `R.card / |Nonce|`, which
    -- is at most the `qRInit / |Nonce|` headroom carved out of slack₂.
    rw [SampleableType.prEvent_uniformSample]
    have hcard : (Finset.univ.filter (· ∈ R)).card ≤ qRInit := by
      calc (Finset.univ.filter (· ∈ R)).card
          = R.card := by
            rw [Finset.filter_univ_mem]
        _ ≤ qRInit := le_trans (Nat.le_add_left _ _) hqRle
    gcongr
  intro n _ hnD
  -- `hnD : ¬ (n ∈ R)`, i.e. `n ∉ R`: off the reader-touched set, the v2 invariant applies.
  replace hnD : n ∉ R := hnD
  -- Phase D: per-`n` bound. Case-split on `c ((tag, 0), n)`:
  -- * Case M-hit: M reads cached value `u₀`; `hRespInv` triggers `multipleBadAdvance`
  --   to fire `bad := true`. By bad monotonicity, the LHS is at most the bad term in the RHS.
  -- * Case M-miss: marginalize M's slot-0 cell + S's slot-K cell, apply IH at u_0,
  --   then `evalDist_singleTableHandler_cache_swap_eq` (swap-bridge) closes the cache-extension
  --   asymmetry; rename u_0 ↔ u_K via the two-cell marginalization.
  rcases hc0 : c ((tag, (0 : Fin sessionsPerTag)), n) with _ | u₀
  · -- Case M-miss: c slot-0 = none. Marginalize slot-0 → IH → swap-bridge → re-marginalize.
    -- Step 1: marginalize gS over slot-0 cell (same pattern as slot-zero Case B).
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
    have hext_eq : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
        (u : Digest),
        OracleComp.tableExtending c
            (Function.update gS' ((tag, (0 : Fin sessionsPerTag)), n) u) =
          OracleComp.tableExtending (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
            gS' := fun gS' u => by
      have h1 := OracleComp.tableExtending_update_of_none c gS' hc0 u
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
    -- Step 2: marginalize LHS-output event over slot-0 (same as slot-zero Case B).
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
      refine prEvent_congr_of_evalDist_eq _ _ ((@hmarg _ ⊤ _).trans ?_) _
      congr 1
      refine bind_congr fun u => ?_
      refine bind_congr fun gS' => ?_
      refine bind_congr fun gFine => ?_
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
      refine prEvent_congr_of_evalDist_eq _ _ ((@hmarg _ ⊤ _).trans ?_) _
      congr 1
      refine bind_congr fun u => ?_
      refine bind_congr fun gS' => ?_
      refine bind_congr fun gFine => ?_
      rw [hext_eq gS' u, hcell_u gS' u]
    -- Step 3: marginalize RHS S-event over slot-K cell (uncached by hcInv).
    have hmarg_K : ∀ {β : Type} [MeasurableSpace β]
        (Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp β),
        𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest); Mψ gS)] =
        𝒟[(do let u ← $ᵗ Digest
              let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              Mψ (Function.update gS' ((tag, slotK), n) u))] := by
      intro β _ Mψ
      let : MeasurableSpace Digest := ⊤
      exact (evalDist_bind_bind_update ($ᵗ Digest)
        ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
        SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample
        ((tag, slotK), n) Mψ).symm
    have hext_K_eq : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
        (u : Digest),
        OracleComp.tableExtending c
            (Function.update gS' ((tag, slotK), n) u) =
          OracleComp.tableExtending (c.cacheQuery ((tag, slotK), n) u) gS' :=
      fun gS' u => by
        have h1 := OracleComp.tableExtending_update_of_none c gS'
          (hcInv tag slotK hslotK_ne n) u
        have h2 := OracleComp.tableExtending_cacheQuery c gS' ((tag, slotK), n) u
        exact h1.symm.trans h2.symm
    have hcell_K_u : ∀ (gS' : (TagId × Fin sessionsPerTag) × Nonce → Digest)
        (u : Digest),
        OracleComp.tableExtending (c.cacheQuery ((tag, slotK), n) u) gS'
            ((tag, slotK), n) = u := fun gS' u => by
      rw [OracleComp.tableExtending_cacheQuery]
      simp [Function.update_self]
    have hRHS_marg :
        Pr{let b ← ((do
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
                (k (some (⟨n, OracleComp.tableExtending c gS
                    ((tag, slotK), n)⟩ : TagTranscript Nonce Digest)))).run' advM))}[b = out]
      = Pr{let b ← ((do
              let u ← $ᵗ Digest
              let gS' ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (singleTableHandler
                (OracleComp.tableExtending (c.cacheQuery ((tag, slotK), n) u) gS'))
                (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' advM))}[b = out] := by
      refine prEvent_congr_of_evalDist_eq _ _ ((@hmarg_K _ ⊤ _).trans ?_) _
      congr 1
      refine bind_congr fun u => ?_
      refine bind_congr fun gS' => ?_
      rw [hext_K_eq gS' u, hcell_K_u gS' u]
    -- Step 4: rewrite the marginalizations and apply `prEvent_bind_le_add_bad_disagree`.
    rw [hLHS_marg, hRHS_marg, hBAD_marg]
    rw [show ∀ a b c : ℝ≥0∞, a + b + c = a + b + 0 + c from
          fun a b c => by ring]
    refine prEvent_bind_le_add_bad_disagree (mx := ($ᵗ Digest : ProbComp Digest))
      (D := fun _ : Digest => False) (by simp) ?_
    intro u _ _
    -- Step 5: per-`u`. Build new invariants for IH call at cache `c.cacheQuery slot-0 u`.
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
      · have : (multipleBadAdvance tag sB
            (some (⟨n, u⟩ : TagTranscript Nonce Digest))).responses (tag', n') =
            (sB.responses.cacheQuery (tag, n)
              (u :: Option.getD (sB.responses (tag, n)) [])) (tag', n') := rfl
        rw [this, htagn, OracleSpec.QueryCache.cacheQuery_self]
        exact Option.some_ne_none _
      · have hne_cell : ((tag', (0 : Fin sessionsPerTag)), n') ≠
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
    -- IH at transcript ⟨n, u⟩, cache c+u@slot-0, qT'.
    have hihB := ih (some (⟨n, u⟩ : TagTranscript Nonce Digest)) qR qT'
      advM (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u)
      (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest))) R
      (hqRk _) (hqTk _) hqRle hcInv' hRespInv'
    -- Bridge S-side from c+u@slot-0 to c+u@slot-K via the swap-bridge.
    -- The swap-bridge requires `slotK.val < advM.sessionsUsed tag`, which holds
    -- because advM = (s with sessionsUsed tag ↦ s.sessionsUsed tag + 1)
    -- = slotK.val + 1 > slotK.val.
    have hAdv_advM : slotK.val < advM.sessionsUsed tag := by
      change slotK.val <
        (Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)) tag
      rw [Function.update_self]
      change s.sessionsUsed tag < s.sessionsUsed tag + 1
      omega
    have hbridge := by
      let : MeasurableSpace Digest := ⊤
      exact evalDist_singleTableHandler_cache_swap_eq (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
        SampleableType.evalDist_uniformSample
        advM c tag slotK hslotK_ne n u hcInv hc0 hAdv_advM
        (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
    -- The bridge says distributions over uniform gS are equal between the two caches.
    -- Use this to rewrite the S-side of hihB.
    -- Rewrite hihB's S-side from c+u@slot-0 to c+u@slot-K via hbridge.
    have hS_eq : Pr{let b ← ((do
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (singleTableHandler (OracleComp.tableExtending
                  (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS))
                (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' advM))}[b = out]
        = Pr{let b ← ((do
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (singleTableHandler (OracleComp.tableExtending
                  (c.cacheQuery ((tag, slotK), n) u) gS))
                (k (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' advM))}[b = out] :=
      prEvent_congr_of_evalDist_eq _ _ hbridge _
    rw [hS_eq] at hihB
    rw [← add_assoc, ← add_assoc]
    exact hihB
  · -- Case M-hit: c slot-0 = some u₀.
    -- Step 1: M's transcript becomes constant ⟨n, u₀⟩.
    have hcell : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
        OracleComp.tableExtending c gS ((tag, (0 : Fin sessionsPerTag)), n) = u₀ :=
      fun gS => by
        change (c ((tag, (0 : Fin sessionsPerTag)), n)).getD
            (gS ((tag, (0 : Fin sessionsPerTag)), n)) = u₀
        rw [hc0]; rfl
    simp_rw [hcell]
    -- Step 2: hRespInv → responses (tag, n) ≠ none → multipleBadAdvance flips bad := true.
    have hresp_some : sB.responses (tag, n) ≠ none :=
      hRespInv tag n hnD (by rw [hc0]; exact Option.some_ne_none _)
    have hbad_init : (multipleBadAdvance tag sB
        (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))).bad = true := by
      change (sB.bad || (sB.responses (tag, n)).isSome) = true
      rw [Option.isSome_iff_ne_none.mpr hresp_some]
      simp
    -- Step 3: By preserves_bad, every reachable output has z.2.2.bad = true.
    -- So LHS-output event (z.1 = out) is dominated by BAD event (z.2.2.bad = true).
    have hLHS_le_BAD :
        Pr{let b ← ((do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                z.1) <$>
              (simulateQ (multipleBadTableHandlerFine
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine)
                (k (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))).run
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))))}[b = out]
        ≤ Pr{let z ← ((do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine)
                (k (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))).run
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, u₀⟩ : TagTranscript Nonce Digest)))))}[z.2.bad = true] := by
      -- Both events come from the same underlying run via different `<$>` projections: push the
      -- two table draws through `lintegral_mono`, then the projections through `prEvent_map`, and
      -- compare on the support, where bad monotonicity makes the implication unconditional.
      let : MeasurableSpace ((TagId × Fin sessionsPerTag) × Nonce → Digest) := ⊤
      rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
      refine lintegral_mono fun gS => ?_
      rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
      refine lintegral_mono fun gFine => ?_
      rw [prEvent_map, prEvent_map]
      refine prEvent_mono_of_support _ _ _ fun z hz_mem _ => ?_
      -- z is in support of the simQ run starting at state with bad = true.
      -- By preserves_bad, z.2.2.bad = true.
      exact multipleBadTableHandlerFine_run_preserves_bad
        (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c gS)) gFine _
        (advM, multipleBadAdvance tag sB
          (some (⟨n, u₀⟩ : TagTranscript Nonce Digest))) hbad_init z hz_mem
    -- Step 4: BAD ≤ (S + BAD) + slacks. Chain: `le_add_self` then `le_self_add`.
    refine hLHS_le_BAD.trans ?_
    exact le_add_self.trans le_self_add

end UnlinkReduction

end DirectCouplingCompose

end PRFTagReader
