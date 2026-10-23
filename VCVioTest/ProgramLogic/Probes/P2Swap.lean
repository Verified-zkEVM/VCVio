/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio
public import Examples.PRFTagReader.DirectCoupling.Swap
public meta import VCVio.ProgramLogic.Tactics
import Mathlib.Util.CountHeartbeats

-- A probe: its proofs are measurements, not library code, so Mathlib's style set is off.
set_option linter.mathlibStandardSet false

/-!
# Probe P2: `singleTableHandler` swap invariance through the `simulateQ` state-relation route

Restates `singleTableHandler_simulateQ_swap_invariant` (private, in
`Examples/PRFTagReader/DirectCoupling/Swap.lean`), copies its proof verbatim (`swap_invariant_orig`)
and re-proves it with the relational `simulateQ` rule, leaving one first-order goal per oracle.
-/

set_option linter.hashCommand false

open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open scoped OracleComp.ProgramLogic

namespace VCVioTest.ProgramLogic.Probes.P2

open PRFTagReader PRFTagReader.UnlinkReduction

variable {TagId Nonce Digest : Type} {sessionsPerTag : ℕ}
variable [DecidableEq TagId] [Fintype TagId]
variable [SampleableType Nonce] [DecidableEq Digest] [NeZero sessionsPerTag]

/-! ## Original proof, verbatim -/

#count_heartbeats in
lemma swap_invariant_orig
    (tag : TagId) (slotK : Fin sessionsPerTag) (hslotK : slotK ≠ 0)
    (n : Nonce)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (hAdv : slotK.val < s.sessionsUsed tag)
    (g₁ g₂ : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (heq : ∀ x : (TagId × Fin sessionsPerTag) × Nonce,
        x ≠ ((tag, (0 : Fin sessionsPerTag)), n) → x ≠ ((tag, slotK), n) →
        g₁ x = g₂ x)
    (hswap_0 : g₁ ((tag, (0 : Fin sessionsPerTag)), n) = g₂ ((tag, slotK), n))
    (hswap_K : g₁ ((tag, slotK), n) = g₂ ((tag, (0 : Fin sessionsPerTag)), n)) :
    (simulateQ (singleTableHandler g₁) oa).run' s
    = (simulateQ (singleTableHandler g₂) oa).run' s := by
  classical
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b =>
    -- Both sides reduce to `pure b` via `simulateQ_pure` and `StateT.run'`.
    simp [simulateQ_pure]
  | query_bind t k ih =>
    -- Decompose via `singleTable_run'_query_bind'`, then case-split on `t`.
    rw [singleTable_run'_query_bind', singleTable_run'_query_bind']
    -- Goal: (step_g₁ t s) >>= cont_g₁ = (step_g₂ t s) >>= cont_g₂
    -- Strategy: show step_g₁ = step_g₂ pointwise (case-split on `t`), then apply IH on
    -- continuation. The IH carries the swap-invariance to each post-step state.
    cases t with
    | inl T =>
      -- Tag query: handler reads at cell `((T, sessionsUsed T), fresh_nonce)`.
      -- Case-split on whether T's session budget is available.
      by_cases hslot : s.sessionsUsed T < sessionsPerTag
      · -- Free slot: step samples nonce, reads cell, advances state.
        rw [singleTableHandler_tag_run_of_lt _ T s hslot,
            singleTableHandler_tag_run_of_lt _ T s hslot]
        -- Cell read is `((T, ⟨sessionsUsed T, hslot⟩), nonce)`. Show this is NOT in the swap pair.
        have hcell_ne : ∀ nonce : Nonce,
            ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce)
              ≠ ((tag, (0 : Fin sessionsPerTag)), n) ∧
            ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce)
              ≠ ((tag, slotK), n) := by
          intro nonce
          refine ⟨?_, ?_⟩
          · -- Differs from (tag, 0, n): either T ≠ tag, or sid > 0.
            intro h
            by_cases hT : T = tag
            · -- T = tag: by hAdv, sessionsUsed tag > slotK > 0, so sid > 0 ≠ 0.
              subst hT
              have hsidpos : 0 < s.sessionsUsed T := by
                have : (slotK : ℕ) < s.sessionsUsed T := hAdv
                exact Nat.lt_of_le_of_lt (Nat.zero_le _) this
              have hsid : s.sessionsUsed T = 0 := by
                have := congrArg (fun p => (p.1.2 : Fin sessionsPerTag).val) h
                simpa using this
              omega
            · -- T ≠ tag: first components differ.
              exact hT (congrArg (fun p => p.1.1) h)
          · -- Differs from (tag, slotK, n): either T ≠ tag, or sid ≠ slotK.
            intro h
            by_cases hT : T = tag
            · subst hT
              have : (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag) = slotK := by
                exact (congrArg (fun p => (p.1.2 : Fin sessionsPerTag)) h)
              have hsid : s.sessionsUsed T = slotK.val := by
                exact congrArg Fin.val this
              omega
            · exact hT (congrArg (fun p => p.1.1) h)
        have hcell_eq : ∀ nonce : Nonce,
            g₁ ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce)
            = g₂ ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce) := by
          intro nonce
          exact heq _ (hcell_ne nonce).1 (hcell_ne nonce).2
        -- The bind structure is `(do { let p ← do { ... }; cont p })`. Flatten via bind_assoc
        -- with explicit OracleComp namespace, then bind_congr on the outer `$ᵗ Nonce`.
        change ($ᵗ Nonce >>= fun nonce => pure _) >>= _ =
             ($ᵗ Nonce >>= fun nonce => pure _) >>= _
        rw [bind_assoc, bind_assoc]
        refine bind_congr fun nonce => ?_
        simp only [unlinkOracleSpec_range_inl, pure_bind, hcell_eq nonce]
        refine ih _ _ ?_
        -- Post-step state preserves hAdv: sessionsUsed tag either unchanged (T ≠ tag) or
        -- increased by 1 (T = tag); in either case ≥ s.sessionsUsed tag > slotK.
        by_cases hT : T = tag
        · subst hT
          change (slotK : ℕ) < (Function.update s.sessionsUsed T (s.sessionsUsed T + 1)) T
          simp
          omega
        · change (slotK : ℕ) < (Function.update s.sessionsUsed T (s.sessionsUsed T + 1)) tag
          rw [Function.update_of_ne (Ne.symm hT)]
          exact hAdv
      · -- Slot exhausted: both sides return `pure (none, s)`. IH on `k none` at state `s` closes.
        rw [singleTableHandler_tag_run_of_not_lt _ T s hslot,
            singleTableHandler_tag_run_of_not_lt _ T s hslot]
        change (simulateQ (singleTableHandler g₁) (k _)).run' s
             = (simulateQ (singleTableHandler g₂) (k _)).run' s
        exact ih _ s hAdv
    | inr transcript =>
      -- Reader query: handler returns `pure (ReaderReply.ofBool (unlinkReaderAccepts ...), s)`.
      rw [singleTableHandler_reader_run, singleTableHandler_reader_run]
      -- Goal: `pure (ofBool h₁, s) >>= cont_g₁ = pure (ofBool h₂, s) >>= cont_g₂`
      -- where h_i = unlinkReaderAccepts (fun slot nc => g_i (slot, nc)) singlePattern transcript.
      by_cases hn : transcript.nonce = n
      · -- Sub-case `transcript.nonce = n`: existential reads cells at `n`, including the swap
        -- pair. Multiset-invariance: `∃ (T', sid'), g((T', sid'), n) = V` is the same for g₁ and
        -- g₂ because the SET of values present at nonce `n` is identical (swap of positions
        -- doesn't change the multiset).
        subst hn
        -- Key claim: `unlinkReaderAccepts` is equal between g₁ and g₂ at this nonce, via the
        -- existential iff: each side can witness the existential by relocating to the other
        -- cached cell when needed.
        have hresp_eq : unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nc => g₁ (slot, nc)) (singlePattern sessionsPerTag) transcript
            = unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nc => g₂ (slot, nc)) (singlePattern sessionsPerTag) transcript := by
          -- Alias the outer `tag` to avoid name shadowing with the existential's bound variable.
          set tagOut : TagId := tag with htag_def
          unfold unlinkReaderAccepts tagAccepts
          rw [decide_eq_decide]
          simp only [singlePattern]
          constructor
          · rintro ⟨T', hT'⟩
            obtain ⟨sid', hsid'⟩ := of_decide_eq_true hT'
            by_cases hCase0 : (T', sid') = (tagOut, (0 : Fin sessionsPerTag))
            · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = 0 := Prod.mk.inj hCase0
              exact ⟨tagOut, decide_eq_true ⟨slotK, hswap_0 ▸ hsid'⟩⟩
            · by_cases hCaseK : (T', sid') = (tagOut, slotK)
              · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = slotK := Prod.mk.inj hCaseK
                exact ⟨tagOut, decide_eq_true ⟨0, hswap_K ▸ hsid'⟩⟩
              · refine ⟨T', decide_eq_true ⟨sid', ?_⟩⟩
                have h_g_eq : g₁ ((T', sid'), transcript.nonce) =
                    g₂ ((T', sid'), transcript.nonce) := by
                  refine heq ((T', sid'), transcript.nonce) ?_ ?_
                  · intro h
                    exact hCase0 (congrArg (fun p => p.1) h)
                  · intro h
                    exact hCaseK (congrArg (fun p => p.1) h)
                exact h_g_eq ▸ hsid'
          · rintro ⟨T', hT'⟩
            obtain ⟨sid', hsid'⟩ := of_decide_eq_true hT'
            by_cases hCase0 : (T', sid') = (tagOut, (0 : Fin sessionsPerTag))
            · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = 0 := Prod.mk.inj hCase0
              exact ⟨tagOut, decide_eq_true ⟨slotK, hswap_K ▸ hsid'⟩⟩
            · by_cases hCaseK : (T', sid') = (tagOut, slotK)
              · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = slotK := Prod.mk.inj hCaseK
                exact ⟨tagOut, decide_eq_true ⟨0, hswap_0 ▸ hsid'⟩⟩
              · refine ⟨T', decide_eq_true ⟨sid', ?_⟩⟩
                have h_g_eq : g₁ ((T', sid'), transcript.nonce) =
                    g₂ ((T', sid'), transcript.nonce) := by
                  refine heq ((T', sid'), transcript.nonce) ?_ ?_
                  · intro h
                    exact hCase0 (congrArg (fun p => p.1) h)
                  · intro h
                    exact hCaseK (congrArg (fun p => p.1) h)
                exact h_g_eq.symm ▸ hsid'
        rw [hresp_eq]
        change (simulateQ (singleTableHandler g₁) (k _)).run' s
             = (simulateQ (singleTableHandler g₂) (k _)).run' s
        exact ih _ s hAdv
      · -- Sub-case `transcript.nonce ≠ n`: cells at `transcript.nonce` are not in swap pair,
        -- so `g₁` and `g₂` agree pointwise there. `unlinkReaderAccepts` value equal.
        -- Pointwise cell-value equality at every cell at `transcript.nonce`:
        have hg_eq : ∀ T' : TagId, ∀ sid' : Fin sessionsPerTag,
            g₁ ((T', sid'), transcript.nonce) = g₂ ((T', sid'), transcript.nonce) := by
          intro T' sid'
          refine heq ((T', sid'), transcript.nonce) ?_ ?_ <;>
            intro h <;> exact hn (congrArg (fun p => p.2) h)
        have hresp_eq : unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nc => g₁ (slot, nc)) (singlePattern sessionsPerTag) transcript
            = unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nc => g₂ (slot, nc)) (singlePattern sessionsPerTag) transcript := by
          unfold unlinkReaderAccepts tagAccepts
          simp only [hg_eq]
        rw [hresp_eq]
        -- Pure-bind: `pure (response, s) >>= cont = cont (response, s)`. Apply IH.
        change (simulateQ (singleTableHandler g₁) (k _)).run' s
             = (simulateQ (singleTableHandler g₂) (k _)).run' s
        exact ih _ s hAdv


/-! ## Relational route

The per-oracle facts of the original proof become two first-order helpers; the induction on `oa`,
the `query_bind` decomposition and the continuation plumbing go to the `simulateQ` rule. -/

#count_heartbeats in
omit [DecidableEq TagId] [Fintype TagId] [SampleableType Nonce] in
/-- A tag query from an invariant state reads a cell off the swap pair (original, condensed). -/
lemma tagCell_ne (tag T : TagId) (slotK : Fin sessionsPerTag) (n nonce : Nonce)
    (s : UnlinkState TagId) (hAdv : slotK.val < s.sessionsUsed tag)
    (hslot : s.sessionsUsed T < sessionsPerTag) :
    ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce) ≠
        ((tag, (0 : Fin sessionsPerTag)), n) ∧
      ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce) ≠ ((tag, slotK), n) := by
  constructor <;> intro h <;> simp only [Prod.mk.injEq, Fin.ext_iff] at h <;>
    obtain ⟨⟨rfl, h⟩, -⟩ := h <;> (try simp at h) <;> omega

#count_heartbeats in
omit [SampleableType Nonce] in
/-- A swap of two cells at one nonce leaves the reader's verdict unchanged (original, verbatim). -/
lemma readerAccepts_eq
    (tag : TagId) (slotK : Fin sessionsPerTag) (n : Nonce)
    (g₁ g₂ : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (heq : ∀ x : (TagId × Fin sessionsPerTag) × Nonce,
        x ≠ ((tag, (0 : Fin sessionsPerTag)), n) → x ≠ ((tag, slotK), n) →
        g₁ x = g₂ x)
    (hswap_0 : g₁ ((tag, (0 : Fin sessionsPerTag)), n) = g₂ ((tag, slotK), n))
    (hswap_K : g₁ ((tag, slotK), n) = g₂ ((tag, (0 : Fin sessionsPerTag)), n))
    (transcript : TagTranscript Nonce Digest) :
    unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
        (fun slot nc => g₁ (slot, nc)) (singlePattern sessionsPerTag) transcript
      = unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
        (fun slot nc => g₂ (slot, nc)) (singlePattern sessionsPerTag) transcript := by
  classical
  by_cases hn : transcript.nonce = n
  · subst hn
    -- Alias the outer `tag` to avoid name shadowing with the existential's bound variable.
    set tagOut : TagId := tag with htag_def
    unfold unlinkReaderAccepts tagAccepts
    rw [decide_eq_decide]
    simp only [singlePattern]
    constructor
    · rintro ⟨T', hT'⟩
      obtain ⟨sid', hsid'⟩ := of_decide_eq_true hT'
      by_cases hCase0 : (T', sid') = (tagOut, (0 : Fin sessionsPerTag))
      · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = 0 := Prod.mk.inj hCase0
        exact ⟨tagOut, decide_eq_true ⟨slotK, hswap_0 ▸ hsid'⟩⟩
      · by_cases hCaseK : (T', sid') = (tagOut, slotK)
        · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = slotK := Prod.mk.inj hCaseK
          exact ⟨tagOut, decide_eq_true ⟨0, hswap_K ▸ hsid'⟩⟩
        · refine ⟨T', decide_eq_true ⟨sid', ?_⟩⟩
          have h_g_eq : g₁ ((T', sid'), transcript.nonce) =
              g₂ ((T', sid'), transcript.nonce) := by
            refine heq ((T', sid'), transcript.nonce) ?_ ?_
            · intro h
              exact hCase0 (congrArg (fun p => p.1) h)
            · intro h
              exact hCaseK (congrArg (fun p => p.1) h)
          exact h_g_eq ▸ hsid'
    · rintro ⟨T', hT'⟩
      obtain ⟨sid', hsid'⟩ := of_decide_eq_true hT'
      by_cases hCase0 : (T', sid') = (tagOut, (0 : Fin sessionsPerTag))
      · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = 0 := Prod.mk.inj hCase0
        exact ⟨tagOut, decide_eq_true ⟨slotK, hswap_K ▸ hsid'⟩⟩
      · by_cases hCaseK : (T', sid') = (tagOut, slotK)
        · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = slotK := Prod.mk.inj hCaseK
          exact ⟨tagOut, decide_eq_true ⟨0, hswap_0 ▸ hsid'⟩⟩
        · refine ⟨T', decide_eq_true ⟨sid', ?_⟩⟩
          have h_g_eq : g₁ ((T', sid'), transcript.nonce) =
              g₂ ((T', sid'), transcript.nonce) := by
            refine heq ((T', sid'), transcript.nonce) ?_ ?_
            · intro h
              exact hCase0 (congrArg (fun p => p.1) h)
            · intro h
              exact hCaseK (congrArg (fun p => p.1) h)
          exact h_g_eq.symm ▸ hsid'
  · have hg_eq : ∀ T' : TagId, ∀ sid' : Fin sessionsPerTag,
        g₁ ((T', sid'), transcript.nonce) = g₂ ((T', sid'), transcript.nonce) := by
      intro T' sid'
      refine heq ((T', sid'), transcript.nonce) ?_ ?_ <;>
        intro h <;> exact hn (congrArg (fun p => p.2) h)
    unfold unlinkReaderAccepts tagAccepts
    simp only [hg_eq]

#count_heartbeats in
lemma swap_invariant_rel
    (tag : TagId) (slotK : Fin sessionsPerTag) (_hslotK : slotK ≠ 0)
    (n : Nonce)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (hAdv : slotK.val < s.sessionsUsed tag)
    (g₁ g₂ : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (heq : ∀ x : (TagId × Fin sessionsPerTag) × Nonce,
        x ≠ ((tag, (0 : Fin sessionsPerTag)), n) → x ≠ ((tag, slotK), n) →
        g₁ x = g₂ x)
    (hswap_0 : g₁ ((tag, (0 : Fin sessionsPerTag)), n) = g₂ ((tag, slotK), n))
    (hswap_K : g₁ ((tag, slotK), n) = g₂ ((tag, (0 : Fin sessionsPerTag)), n)) :
    𝒟[(simulateQ (singleTableHandler g₁) oa).run' s] =
      𝒟[(simulateQ (singleTableHandler g₂) oa).run' s] := by
  by_equiv
  rvcstep using (fun s₁ s₂ : UnlinkState TagId => s₁ = s₂ ∧ slotK.val < s₁.sessionsUsed tag)
  · rintro (T | transcript) s₁ _ ⟨rfl, hAdv⟩
    · by_cases hslot : s₁.sessionsUsed T < sessionsPerTag
      · change ⟪singleTableHandler g₁ (Sum.inl T) s₁ ~ singleTableHandler g₂ (Sum.inl T) s₁ | _⟫
        have hcell (nonce : Nonce) := heq _ (tagCell_ne tag T slotK n nonce s₁ hAdv hslot).1
          (tagCell_ne tag T slotK n nonce s₁ hAdv hslot).2
        rw [singleTableHandler_tag_run_of_lt _ T s₁ hslot,
          singleTableHandler_tag_run_of_lt _ T s₁ hslot]
        simp only [hcell]
        rvcstep
        rvcstep using (id : Nonce → Nonce)
        · exact Function.bijective_id
        · refine fun _ => ⟨rfl, rfl, ?_⟩
          change slotK.val < Function.update s₁.sessionsUsed T _ tag
          rw [Function.update_apply]
          split_ifs with h
          · subst h; omega
          · exact hAdv
      · change ⟪singleTableHandler g₁ (Sum.inl T) s₁ ~ singleTableHandler g₂ (Sum.inl T) s₁ | _⟫
        rw [singleTableHandler_tag_run_of_not_lt _ T s₁ hslot,
          singleTableHandler_tag_run_of_not_lt _ T s₁ hslot]
        exact relTriple_pure_pure ⟨rfl, rfl, hAdv⟩
    · change ⟪singleTableHandler g₁ (Sum.inr transcript) s₁ ~
        singleTableHandler g₂ (Sum.inr transcript) s₁ | _⟫
      rw [singleTableHandler_reader_run, singleTableHandler_reader_run,
        readerAccepts_eq tag slotK n g₁ g₂ heq hswap_0 hswap_K]
      exact relTriple_pure_pure ⟨rfl, rfl, hAdv⟩
  · exact ⟨rfl, hAdv⟩


/-! ## Exact equality through a missing bisimulation rule

The callers only need the distributional statement above, but the exact `=` of the original is
one generic rule away: handlers that agree on an invariant the second one preserves give equal
simulations. VCVio has the `RelTriple` form
(`relTriple_simulateQ_run_eqRel_of_impl_eq_preservesInv`) but not the equation. -/

#count_heartbeats in
omit [DecidableEq TagId] [Fintype TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- **Missing rule.** Bisimulation on an invariant, as an equation of computations. -/
theorem simulateQ_run_eq_of_impl_eq_on_inv {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp)) (Inv : σ → Prop)
    (himpl : ∀ t s, Inv s →
      (impl₁ t).run s = (impl₂ t).run s ∧ ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (oa : OracleComp spec α) (s : σ) (hs : Inv s) :
    (simulateQ impl₁ oa).run s = (simulateQ impl₂ oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [(himpl t s hs).1]
    exact bind_congr_of_forall_mem_support _ fun z hz => ih _ _ ((himpl t s hs).2 z hz)

#count_heartbeats in
lemma swap_invariant_eq
    (tag : TagId) (slotK : Fin sessionsPerTag)
    (n : Nonce)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (hAdv : slotK.val < s.sessionsUsed tag)
    (g₁ g₂ : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (heq : ∀ x : (TagId × Fin sessionsPerTag) × Nonce,
        x ≠ ((tag, (0 : Fin sessionsPerTag)), n) → x ≠ ((tag, slotK), n) →
        g₁ x = g₂ x)
    (hswap_0 : g₁ ((tag, (0 : Fin sessionsPerTag)), n) = g₂ ((tag, slotK), n))
    (hswap_K : g₁ ((tag, slotK), n) = g₂ ((tag, (0 : Fin sessionsPerTag)), n)) :
    (simulateQ (singleTableHandler g₁) oa).run' s
    = (simulateQ (singleTableHandler g₂) oa).run' s := by
  refine congrArg (Prod.fst <$> ·) (simulateQ_run_eq_of_impl_eq_on_inv _ _
    (fun s => slotK.val < s.sessionsUsed tag) ?_ oa s hAdv)
  rintro (T | transcript) s₁ hAdv
  · by_cases hslot : s₁.sessionsUsed T < sessionsPerTag
    · change singleTableHandler g₁ (Sum.inl T) s₁ = singleTableHandler g₂ (Sum.inl T) s₁ ∧
        ∀ z ∈ support (singleTableHandler g₂ (Sum.inl T) s₁), _
      simp only [singleTableHandler_tag_run_of_lt _ T s₁ hslot, fun nonce => heq _
        (tagCell_ne tag T slotK n nonce s₁ hAdv hslot).1 (tagCell_ne tag T slotK n nonce s₁ hAdv hslot).2]
      refine ⟨rfl, fun z hz => ?_⟩
      simp at hz
      obtain ⟨nonce, rfl⟩ := hz
      change slotK.val < Function.update s₁.sessionsUsed T _ tag
      rw [Function.update_apply]
      split_ifs with h
      · subst h; omega
      · exact hAdv
    · change singleTableHandler g₁ (Sum.inl T) s₁ = singleTableHandler g₂ (Sum.inl T) s₁ ∧
        ∀ z ∈ support (singleTableHandler g₂ (Sum.inl T) s₁), _
      simp only [singleTableHandler_tag_run_of_not_lt _ T s₁ hslot]
      exact ⟨rfl, fun z hz => by subst hz; exact hAdv⟩
  · change singleTableHandler g₁ (Sum.inr transcript) s₁ =
        singleTableHandler g₂ (Sum.inr transcript) s₁ ∧
      ∀ z ∈ support (singleTableHandler g₂ (Sum.inr transcript) s₁), _
    simp only [singleTableHandler_reader_run, readerAccepts_eq tag slotK n g₁ g₂ heq hswap_0 hswap_K]
    exact ⟨rfl, fun z hz => by subst hz; exact hAdv⟩


/-! ## Which version the caller can use

`evalDist_singleTableHandler_cache_swap_eq` (and nine other `PRFTagReader` lemmas) take
`[EvalDistSemantics ProbComp] [LawfulEvalDistSemantics ProbComp]` as binders, so their `𝒟` is
an arbitrary lawful semantics. The relational version is about the canonical instance and does
not transfer (a lawful semantics need not agree with it on `$ᵗ`); the equation does. -/

example [inst : EvalDistSemantics ProbComp] [LawfulEvalDistSemantics ProbComp]
    (tag : TagId) (slotK : Fin sessionsPerTag) (_hslotK : slotK ≠ 0) (n : Nonce)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (hAdv : slotK.val < s.sessionsUsed tag)
    (g₁ g₂ : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (heq : ∀ x : (TagId × Fin sessionsPerTag) × Nonce,
        x ≠ ((tag, (0 : Fin sessionsPerTag)), n) → x ≠ ((tag, slotK), n) →
        g₁ x = g₂ x)
    (hswap_0 : g₁ ((tag, (0 : Fin sessionsPerTag)), n) = g₂ ((tag, slotK), n))
    (hswap_K : g₁ ((tag, slotK), n) = g₂ ((tag, (0 : Fin sessionsPerTag)), n)) :
    𝒟[(simulateQ (singleTableHandler g₁) oa).run' s] =
      𝒟[(simulateQ (singleTableHandler g₂) oa).run' s] := by
  fail_if_success exact swap_invariant_rel tag slotK _hslotK n oa s hAdv g₁ g₂ heq hswap_0 hswap_K
  rw [swap_invariant_eq tag slotK n oa s hAdv g₁ g₂ heq hswap_0 hswap_K]

end VCVioTest.ProgramLogic.Probes.P2
