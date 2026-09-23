/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.BodyResampling

/-!
# EUF-CMA for Fiat-Shamir with aborts: DeferredCoupling

The deferred-coupling reduction: the ghost-blind bad event is dominated by the
deferred-draw run, whose drawn and signed prefixes, expected length and attempt
count are bounded here (the attempt-count law).

Part of the CMA-to-NMA security development for the Fiat-Shamir-with-aborts
transform; `VCVio.CryptoFoundations.FiatShamir.WithAbort.Security` assembles
the headline `euf_cma_to_nma` and holds the overview docstring.
-/


public section

universe u v

open OracleComp OracleSpec
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

section EUF_CMA

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

section scaffold

variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
variable (adv : SignatureAlg.UnforgeableAdversary
  (FiatShamirWithAbort.inROM ids hr M maxAttempts))

/-! ### Stage 3a: the deferred-coupling reduction (Piece A)

The eager ghost-blind bad marginal reduces, through the deferred-draw handler `deferredDrawImpl`,
to the deferred run's bad marginal:

* **Piece A** (`ghostBlind_bad_le_deferredDraw`): a *pointwise coupling* of the eager ghost-blind
  run with the deferred-draw run, established on the pointwise mono skeleton
  `relTriple_simulateQ_run_mono` carrying the state invariant `deferredCoupleInv` (real cache and
  signed list equal; ghost domain covered by the drawn-commitment list; bad-flag ordered). The
  read step is an output-equal coupling (both answer from the real layer via `roStep`, and the
  membership flag fires more readily on the deferred side because it ignores the message component);
  the sign step couples the two bodies' `ids.commit` draws so the eager ghost writes and the
  deferred draws stay in lockstep. `probEvent_le_of_relTriple_imp` then reads off the ordered bad
  marginals.

The deferred run's bad marginal is then carried — through the read-recording reduction
(`deferredDraw_bad_le_readRecord`) and the first-moment Markov step
(`readRecord_pred_le_expected_coincidences`) — to the expected coincidence count bounded by
`readRecord_expected_coincidences_le`.

This reduction uses the pointwise coupling because the bad flags *are* pointwise linkable (eager
ghost-membership ⟹ deferred commitment-membership, since the drawn list grows in lockstep with the
ghost cache), so the pointwise `relTriple_simulateQ_run_mono` route applies. The value-free charge
that this reduction feeds into is `readRecord_expected_coincidences_le`.

The state invariant linking the eager `GhostState` and the deferred `DeferredState`: real cache and
signed-message list agree, every key in the ghost cache has its commitment recorded in the drawn
list, and the bad flag is ordered (eager-bad ⟹ deferred-bad). The read points coincide because both
sides answer from the (shared) real layer. -/
omit [SampleableType Stmt] in
/-- The coupling invariant between the eager ghost-blind state and the deferred-draw state: real
cache and signed list agree, every ghost-cache key's commitment is in the drawn list, and the bad
flag is ordered. -/
@[expose] def deferredCoupleInv
    (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal) : Prop :=
  s₁.1.1.1 = s₂.1.1.1 ∧ s₁.1.2 = s₂.1.1.2 ∧
    (∀ mc : M × Commit, s₁.1.1.2 mc ≠ none → mc.2 ∈ s₂.1.2) ∧
    (s₁.2 = true → s₂.2 = true)

omit [SampleableType Stmt] in
/-- **Per-query coupling step for the ghost-blind → deferred coupling.** From any pair of
`deferredCoupleInv`-related states, one step of the eager ghost-blind handler couples with one step
of the deferred-draw handler with equal output and the invariant preserved.

* **Uniform** steps forward the same draw; the state is untouched, so the invariant is inherited.
* **Read** steps answer from the shared real layer via `roStep` (same answer, same cache update);
  the eager bad flag fires on ghost-domain membership and the deferred one on drawn-list membership;
  the domain-coverage invariant makes the eager fire imply the deferred fire (it ignores the message
  component), preserving the bad ordering.
* **Sign** steps invoke `signBody_couple`: the matched `ids.commit` draws keep the outputs and real
  caches equal and extend the drawn list to cover the new ghost writes; the bad flag is intact. -/
theorem deferredCouple_step (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (u₁ : GhostState M Commit Chal) (u₂ : DeferredState M Commit Chal)
    (hu : deferredCoupleInv M u₁ u₂) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((ghostBlindImpl ids M maxAttempts pk sk t).run u₁)
      ((deferredDrawImpl ids M maxAttempts pk sk t).run u₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ deferredCoupleInv M p₁.2 p₂.2) := by
  obtain ⟨hre, hl, hdom, hbad⟩ := hu
  rcases t with (n | mc) | msg
  · -- UNIFORM: both forward the same draw; state untouched.
    have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inl n))).run u₁ =
        (fun u => (u, u₁)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
    have hrun₂ : (deferredDrawImpl ids M maxAttempts pk sk (.inl (.inl n))).run u₂ =
        (fun u => (u, u₂)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
    rw [hrun₁, hrun₂]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
    rintro a b (rfl : a = b)
    exact ⟨rfl, hre, hl, hdom, hbad⟩
  · -- READ: answer from the shared real layer; bad flag dominated under domain coverage.
    have hrun₂ : (deferredDrawImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₂ =
        (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, u₂.1.1.2), u₂.1.2), u₂.2 || decide (mc.2 ∈ u₂.1.2)))) <$>
          roStep M u₂.1.1.1 mc := rfl
    cases hgh : u₁.1.1.2 mc with
    | none =>
        have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₁ =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, (((cu.2, u₁.1.1.2), u₁.1.2), u₁.2))) <$> roStep M u₁.1.1.1 mc := by
          rw [ghostBlindImpl_eq_ghostHybridImpl_false]
          exact ghostHybridImpl_run_ro_ghost_none ids M maxAttempts false pk sk hgh
        rw [hrun₁, hrun₂, hre]
        refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
          (OracleComp.ProgramLogic.Relational.relTriple_post_mono
            (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
        rintro a b (rfl : a = b)
        exact ⟨rfl, rfl, hl, hdom, fun hb => by rw [hbad hb]; rfl⟩
    | some v =>
        have hgh2 : u₁.1.1.2 mc ≠ none := by rw [hgh]; exact Option.some_ne_none v
        have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₁ =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, (((cu.2, u₁.1.1.2), u₁.1.2), true))) <$> roStep M u₁.1.1.1 mc := by
          rw [ghostBlindImpl_eq_ghostHybridImpl_false,
            ghostHybridImpl_run_ro_ghost_some ids M maxAttempts false pk sk hgh,
            ite_eq_right Bool.false_ne_true]
        rw [hrun₁, hrun₂, hre]
        refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
          (OracleComp.ProgramLogic.Relational.relTriple_post_mono
            (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
        rintro a b (rfl : a = b)
        have hdef : (u₂.2 || decide (mc.2 ∈ u₂.1.2)) = true := by simp [hdom mc hgh2]
        exact ⟨rfl, rfl, hl, hdom, fun _ => hdef⟩
  · -- SIGN: couple the two signing bodies via `signBody_couple`; bad flag untouched.
    have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inr msg)).run u₁ =
        (fun alc : Option (Commit × Resp) ×
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
          (alc.1, ((alc.2, msg :: u₁.1.2), u₁.2))) <$>
          (ghostSignBody ids M pk sk msg maxAttempts).run u₁.1.1 := by
      rw [ghostBlindImpl_eq_ghostHybridImpl_false]
      exact ghostHybridImpl_run_sign ids M maxAttempts false pk sk msg u₁
    have hrun₂ : (deferredDrawImpl ids M maxAttempts pk sk (.inr msg)).run u₂ =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, (((alc.2, msg :: u₂.1.1.2), u₂.1.2 ++ alc.1.2), u₂.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run u₂.1.1.1 := rfl
    rw [hrun₁, hrun₂]
    have hu11 : u₁.1.1 = (u₂.1.1.1, u₁.1.1.2) := by rw [← hre]
    rw [hu11]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (signBody_couple ids M pk sk msg maxAttempts u₂.1.1.1 u₁.1.1.2 u₂.1.2 hdom) ?_)
    rintro p₁ p₂ ⟨hout, hcache, hghcov⟩
    exact ⟨hout, hcache, by rw [hl], hghcov, hbad⟩

omit [SampleableType Stmt] in
/-- **The ghost-blind → deferred run coupling.** By induction on the adversary computation `oa`,
the eager ghost-blind run and the deferred-draw run are coupled with the invariant
`deferredCoupleInv` preserved at every leaf, using `deferredCouple_step` at each query and the
inductive hypothesis for the continuation. -/
theorem deferredCouple_run {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal),
      deferredCoupleInv M s₁ s₂ →
      OracleComp.ProgramLogic.Relational.RelTriple
        ((simulateQ (ghostBlindImpl ids M maxAttempts pk sk) oa).run s₁)
        ((simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s₂)
        (fun q₁ q₂ => deferredCoupleInv M q₁.2 q₂.2) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s₁ s₂ hinv
      simp only [simulateQ_pure, StateT.run_pure]
      exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure hinv
  | query_bind t ob ih =>
      intro s₁ s₂ hinv
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (deferredCouple_step ids M maxAttempts pk sk t s₁ s₂ hinv) ?_
      rintro p₁ p₂ ⟨hout, hinv'⟩
      rw [show p₁.1 = p₂.1 from hout]
      exact ih p₂.1 p₁.2 p₂.2 hinv'

omit [SampleableType Stmt] in
/-- **Piece A: the ghost-blind → deferred coupling.** The ghost-blind run's bad marginal is at most
the deferred-draw run's bad marginal, from any pair of `deferredCoupleInv`-related start states.

Reads off the bad-flag ordering component of the invariant from the run coupling
`deferredCouple_run` via `probEvent_le_of_relTriple_imp`. -/
theorem ghostBlind_bad_le_deferredDraw {γ : Type}
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal)
    (hinv : deferredCoupleInv M s₁ s₂) :
    Pr[fun z : γ × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) oa).run s₁]
      ≤ Pr[fun z : γ × DeferredState M Commit Chal => z.2.2 = true |
          (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s₂] :=
  OracleComp.ProgramLogic.Relational.probEvent_le_of_relTriple_imp
    (deferredCouple_run ids M maxAttempts pk sk oa s₁ s₂ hinv)
    (fun _ _ hp => hp.2.2.2)

omit [SampleableType Stmt] in
/-- **The drawn list only grows.** Every reachable final state of the deferred-draw run from a
start state `s` has the start's drawn list `s.1.2` as a prefix: uniform and read steps leave the
drawn list untouched, and a signing step appends (`s.1.2 ++ alc.1.2`). Hence the number of *new*
draws is `final.length - s.1.2.length` and is well-behaved (`s.1.2.length ≤ final.length`). -/
theorem deferredDraw_run_drawn_prefix {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredState M Commit Chal)
      (z : γ × DeferredState M Commit Chal),
      z ∈ support ((simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s) →
      s.1.2 <+: z.2.1.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact List.prefix_rfl
  | query_bind t ob ih =>
      intro s z hz
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      refine List.IsPrefix.trans ?_ (ih x.1 x.2 z hzx)
      -- The step's output drawn list extends `s.1.2`.
      rcases t with (n | mc) | msg
      · have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs; exact List.prefix_rfl
      · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
              roStep M s.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs; exact List.prefix_rfl
      · have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs; exact List.prefix_append s.1.2 alc.1.2

omit [SampleableType Stmt] in
/-- **The signed-message list only grows in length.** Every reachable final state of the
deferred-draw run from a start state `s` has signed-message list at least as long as the start's
`s.1.1.2`: uniform and read steps leave it untouched, and a signing step prepends one message
(`msg :: s.1.1.2`). Hence the number of *new* signing queries is `final.length - s.1.1.2.length`. -/
theorem deferredDraw_run_signed_prefix {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredState M Commit Chal)
      (z : γ × DeferredState M Commit Chal),
      z ∈ support ((simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s) →
      s.1.1.2.length ≤ z.2.1.1.2.length := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact le_rfl
  | query_bind t ob ih =>
      intro s z hz
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      refine le_trans ?_ (ih x.1 x.2 z hzx)
      rcases t with (n | mc) | msg
      · have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
              roStep M s.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs; simp

omit [SampleableType Stmt] in
/-- **Run-level expected drawn-list length of the deferred-draw run.** By induction on the
adversary computation `oa`, the expected final drawn-list length of the deferred-draw run from a
start state `s` is at most `s.1.2.length + qSrem · (1/(1-p))`, where `qSrem` bounds the number of
signing queries `oa` makes (the `(· matches .inr _)` component of `signHashQueryBound`). Each
signing query grows the expected drawn length by at most `1/(1-p)` (the per-step charge
`deferredDrawImpl_step_expected_length_le`), and uniform/read queries leave it unchanged; the
signing-query budget `qSrem` telescopes across the fold exactly as in
`IsQueryBoundP.simulateQ_run_StateT_of_step`. This is the mean bound that the constructed count law
`kn` of Piece B inherits. -/
theorem deferredDraw_run_expected_length_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredState M Commit Chal),
        (∑' z : γ × DeferredState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s] *
            (z.2.1.2.length : ℝ≥0∞))
          ≤ (s.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - p_abort)) with hc
      -- Total mass of one deferred step is `1` (no failure).
      have hmass : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range t) × DeferredState M Commit Chal,
          Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s]) = 1 :=
        tsum_probOutput_eq_one' (by
          rcases t with (n | mc) | msg
          · simp [deferredDrawImpl]
          · simp only [deferredDrawImpl, StateT.run_mk]
            rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
          · simp [deferredDrawImpl])
      -- Abstract the continuation's carried budget `b` and the per-step abort charge.
      -- Generic combiner: with continuation bound `≤ x.length + b·c`, step charge `extra`,
      -- and `extra + b·c ≤ qSrem·c`, the fold gives the run bound.
      have hfold : ∀ (b : ℕ) (extra : ℝ≥0∞),
          (∀ x : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × DeferredState M Commit Chal,
            (∑' z : γ × DeferredState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                (z.2.1.2.length : ℝ≥0∞))
              ≤ (x.2.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c) →
          (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
            (x.2.1.2.length : ℝ≥0∞)) ≤ (s.1.2.length : ℝ≥0∞) + extra →
          extra + (b : ℝ≥0∞) * c ≤ (qSrem : ℝ≥0∞) * c →
          (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
              ∑' z : γ × DeferredState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                  (z.2.1.2.length : ℝ≥0∞))
            ≤ (s.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
        intro b extra hcont hstep hbudget
        calc (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                ∑' z : γ × DeferredState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk)
                      (ob x.1)).run x.2] * (z.2.1.2.length : ℝ≥0∞))
            ≤ ∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                ((x.2.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c) :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact hcont x
          _ = (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                  (x.2.1.2.length : ℝ≥0∞)) + (b : ℝ≥0∞) * c := by
              rw [show (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                    ((x.2.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c))
                  = ∑' x, (Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                      (x.2.1.2.length : ℝ≥0∞) +
                    Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                      ((b : ℝ≥0∞) * c)) from tsum_congr fun x => by rw [mul_add]]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          _ ≤ ((s.1.2.length : ℝ≥0∞) + extra) + (b : ℝ≥0∞) * c := by gcongr
          _ ≤ (s.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by rw [add_assoc]; gcongr
      -- Case on the query head so the `if p t` budget/charge reduce concretely.
      rcases t with (n | mc) | msg
      · -- UNIFORM: budget unchanged, no charge.
        refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawImpl_step_expected_length_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inl n)) s
      · -- READ: budget unchanged, no charge.
        refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawImpl_step_expected_length_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inr mc)) s
      · -- SIGN: budget decrements; `0 < qSrem`, charge `c`, recombine `c + (qSrem-1)·c = qSrem·c`.
        have hpos : 0 < qSrem := by
          rcases hQ1 with hno | hpos
          · exact absurd (by simp) hno
          · exact hpos
        refine hfold (qSrem - 1) c (fun x => ih x.1 (qSrem - 1) (by simpa using hQ2 x.1) x.2) ?_ ?_
        · have hstep := deferredDrawImpl_step_expected_length_le ids M maxAttempts pk sk
            hp₀ hp hAbort (.inr msg) s
          rwa [ite_eq_left (by rfl), ← hc] at hstep
        · rw [add_comm, ← add_one_mul,
            show ((qSrem - 1 : ℕ) : ℝ≥0∞) + 1 = (qSrem : ℝ≥0∞) by
              have : qSrem - 1 + 1 = qSrem := by omega
              rw [← this]; push_cast; ring]

omit [SampleableType Stmt] in
/-- **The deferred-draw run never fails.** Every step of `deferredDrawImpl` is a pushforward of a
non-failing `ProbComp` (uniform sampling, `roStep`, or the draw-collecting signing body), so the
whole `simulateQ` fold has zero failure mass. -/
theorem deferredDraw_run_neverFail {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredState M Commit Chal),
      Pr[⊥ | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s] = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s; simp [simulateQ_pure]
  | query_bind t ob ih =>
      intro s
      rw [simulateQ_query_bind, StateT.run_bind, probFailure_bind_eq_zero_iff]
      refine ⟨?_, fun x _ => ih x.1 x.2⟩
      rcases t with (n | mc) | msg
      · simp [deferredDrawImpl]
      · simp only [deferredDrawImpl]
        rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
      · simp [deferredDrawImpl]

omit [SampleableType Stmt] in
/-- **The constructed count law of Piece B and its mean bound.** Mapping the deferred-draw run to
its number of *new* draws beyond the start prefix `ws₀` (i.e. `final.length - ws₀.length`) gives a
count law `kn` whose mean is at most `qSrem/(1-p)`. The mean equals the expected total drawn length
minus `ws₀.length` (valid because `ws₀` is always a prefix, `deferredDraw_run_drawn_prefix`), and
the expected total length is bounded by `ws₀.length + qSrem·(1/(1-p))`
(`deferredDraw_run_expected_length_le`), so the `ws₀.length` cancels. This is the mean obligation of
Piece B, discharged for the constructed `kn`. -/
theorem deferredDraw_kn_mean_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ) (hQ : oa.IsQueryBoundP (· matches Sum.inr _) qSrem)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) (ws₀ : List Commit) :
    (∑' n : ℕ, Pr[= n |
        (fun z : γ × DeferredState M Commit Chal => z.2.1.2.length - ws₀.length) <$>
          (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run (((re, l), ws₀), false)] *
        (n : ℝ≥0∞))
      ≤ ENNReal.ofReal ((qSrem : ℝ) / (1 - p_abort)) := by
  classical
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  set run : ProbComp (γ × DeferredState M Commit Chal) :=
    (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run (((re, l), ws₀), false) with hrun
  -- The mean of `kn` equals the run-expectation of the new-draw count.
  have hmean : (∑' n : ℕ, Pr[= n |
        (fun z : γ × DeferredState M Commit Chal => z.2.1.2.length - ws₀.length) <$> run] *
        (n : ℝ≥0∞))
      = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
          ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞) :=
    tsum_probOutput_map_mul run
      (fun z => z.2.1.2.length - ws₀.length) (fun n => (n : ℝ≥0∞))
  rw [hmean]
  -- Add back `ws₀.length` to recover the total-length expectation, bounded by the fold lemma.
  have hsplit : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
        ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞)) + (ws₀.length : ℝ≥0∞)
      ≤ (ws₀.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    have hmass : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run]) = 1 := by
      rw [hrun]
      exact tsum_probOutput_eq_one'
        (deferredDraw_run_neverFail ids M maxAttempts pk sk oa (((re, l), ws₀), false))
    calc (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞)) + (ws₀.length : ℝ≥0∞)
        = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            (((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞) + (ws₀.length : ℝ≥0∞)) := by
          rw [show (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                (((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞) + (ws₀.length : ℝ≥0∞)))
              = (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                  ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞)) +
                ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] * (ws₀.length : ℝ≥0∞) from by
              rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]]
          rw [ENNReal.tsum_mul_right, hmass, one_mul]
      _ = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            (z.2.1.2.length : ℝ≥0∞) := by
          refine tsum_congr fun z => ?_
          by_cases hz : z ∈ support run
          · have hpre : ws₀.length ≤ z.2.1.2.length :=
              (deferredDraw_run_drawn_prefix ids M maxAttempts pk sk oa _ z hz).length_le
            congr 1
            rw [← Nat.cast_add, Nat.sub_add_cancel hpre]
          · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
      _ ≤ (ws₀.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
          have := deferredDraw_run_expected_length_le ids M maxAttempts pk sk hp₀ hp hAbort oa
            qSrem hQ (((re, l), ws₀), false)
          rwa [← hrun] at this
  -- Cancel `ws₀.length` (finite) and rewrite `qSrem·ofReal(1/(1-p)) = ofReal(qSrem/(1-p))`.
  have hcancel : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
        ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞))
      ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [add_comm] at hsplit
    exact (ENNReal.add_le_add_iff_left (by simp : (ws₀.length : ℝ≥0∞) ≠ ∞)).mp hsplit
  refine hcancel.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_natCast qSrem, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-! ### Attempt-count law: the tight redraft of the deferral count

The firing event tests reads against the *actual* (rejected) drawn list, whose draws are skewed by
the rejection conditioning `commit | reject`. The `drawList`-game RHS, by contrast, draws *raw*
`Prod.fst <$> ids.commit pk sk`. A reject-count `kn = drawnlist.length` is therefore *too small* to
dominate the firing (the residual was false-as-stated with that `kn`). The sound count is the total
*attempt* count, which over-counts each query's rejected draws by the accepting attempt's one fresh
raw draw and whose mean is exactly `qSrem/(1-p)`.

The attempt count is recovered *without a new state field* as `(drawn-list growth) + (signed-list
growth)`: every signing query increments the signed-message list by exactly one (in
`deferredDrawImpl`'s sign branch) and the drawn list by its rejected-attempt count. Their sum
dominates the per-query attempt count and has the clean charge `∑_{a≤maxAttempts} p^a ≤ 1/(1-p)`,
combining the tight reject bound (`tsum_probOutput_run_ghostSignDrawBody_mul_length_le_tight`, the
`∑_{a<n} p^(a+1)` rejects) with the unconditional `+1` (signed list). -/

omit [SampleableType Stmt] in
/-- **Per-step expected attempt-count growth of the deferred-draw handler.** One step of
`deferredDrawImpl` grows the expected combined size `drawnlist.length + signedlist.length` by at
most `1/(1-p)` on a signing query and by `0` on uniform/read queries. On a signing query the drawn
list grows by the rejected-attempt count (expected `≤ ∑_{a<maxAttempts} p^(a+1)`, the tight bound)
and the signed list grows by exactly `1`; their sum is `∑_{a≤maxAttempts} p^a ≤ 1/(1-p)`. This is
the per-step charge for the attempt-count law `kn`. -/
lemma deferredDrawImpl_step_expected_attemptCount_le (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : DeferredState M Commit Chal) :
    (∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t) ×
        DeferredState M Commit Chal,
      Pr[= z | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
        ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
      ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) +
          (if (t matches Sum.inr _) then ENNReal.ofReal (1 / (1 - p_abort)) else 0) := by
  classical
  rcases t with (n | mc) | msg
  · -- UNIFORM: state untouched.
    rw [ite_eq_right (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ (by simp [deferredDrawImpl]))
    intro z hz
    have hzs : z ∈ support ((fun u => (u, s)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hz
    rw [support_map] at hzs
    obtain ⟨u, _, rfl⟩ := hzs; rfl
  · -- READ: writes only the base cache / bad flag; both lists preserved.
    rw [ite_eq_right (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ ?_)
    · intro z hz
      have hzs : z ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
            roStep M s.1.1.1 mc) := hz
      rw [support_map] at hzs
      obtain ⟨cu, _, rfl⟩ := hzs; rfl
    · simp only [deferredDrawImpl, StateT.run_mk]
      rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
  · -- SIGN: drawn list `s.1.2 ++ alc.1.2`, signed list `msg :: s.1.1.2` (one longer).
    rw [ite_eq_left (by simp)]
    have hrun : (deferredDrawImpl ids M maxAttempts pk sk (.inr msg)).run s =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1 := rfl
    rw [hrun]
    refine le_of_eq_of_le (tsum_probOutput_map_mul
      ((ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1)
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2)))
      (fun z => ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))) ?_
    calc _
        = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞) +
                (alc.1.2.length : ℝ≥0∞)) := by
          refine tsum_congr fun alc => ?_
          simp only [List.length_append, List.length_cons]
          push_cast
          ring
      _ = ((∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞))) +
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (alc.1.2.length : ℝ≥0∞)) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add]
      _ ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + ENNReal.ofReal (1 / (1 - p_abort)) := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
          rw [add_assoc]
          gcongr
          refine le_trans (add_le_add_right
            (tsum_probOutput_run_ghostSignDrawBody_mul_length_le_tight ids M pk sk msg
              hAbort maxAttempts s.1.1.1) _) ?_
          rw [add_comm]
          refine le_trans (le_of_eq ?_) (geomSum_le hp₀ hp (maxAttempts + 1))
          rw [Finset.sum_range_succ']
          simp only [pow_zero]

omit [SampleableType Stmt] in
/-- **Run-level expected attempt count of the deferred-draw run.** By induction on `oa`, the
expected combined size `drawnlist.length + signedlist.length` of the deferred-draw run from a start
state `s` is at most `(s.1.2.length + s.1.1.2.length) + qSrem · (1/(1-p))`, where `qSrem` bounds the
number of signing queries. Each signing query grows the expected combined size by at most `1/(1-p)`
(the per-step charge `deferredDrawImpl_step_expected_attemptCount_le`), and uniform/read queries
leave it unchanged; the signing-query budget telescopes across the fold exactly as in
`deferredDraw_run_expected_length_le`. The attempt-count law `kn` of the redrafted residual inherits
this mean. -/
theorem deferredDraw_run_expected_attemptCount_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredState M Commit Chal),
        (∑' z : γ × DeferredState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s] *
            ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
          ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) +
              (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - p_abort)) with hc
      have hmass : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range t) × DeferredState M Commit Chal,
          Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s]) = 1 :=
        tsum_probOutput_eq_one' (by
          rcases t with (n | mc) | msg
          · simp [deferredDrawImpl]
          · simp only [deferredDrawImpl, StateT.run_mk]
            rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
          · simp [deferredDrawImpl])
      have hfold : ∀ (b : ℕ) (extra : ℝ≥0∞),
          (∀ x : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × DeferredState M Commit Chal,
            (∑' z : γ × DeferredState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
              ≤ ((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c) →
          (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
            ((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞))
              ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + extra →
          extra + (b : ℝ≥0∞) * c ≤ (qSrem : ℝ≥0∞) * c →
          (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
              ∑' z : γ × DeferredState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                  ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
            ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
        intro b extra hcont hstep hbudget
        calc (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                ∑' z : γ × DeferredState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk)
                      (ob x.1)).run x.2] * ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
            ≤ ∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                (((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c) :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact hcont x
          _ = (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                  ((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞)) + (b : ℝ≥0∞) * c := by
              rw [show (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                    (((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c))
                  = ∑' x, (Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                      ((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞) +
                    Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                      ((b : ℝ≥0∞) * c)) from tsum_congr fun x => by rw [mul_add]]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          _ ≤ (((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + extra) + (b : ℝ≥0∞) * c := by gcongr
          _ ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
              rw [add_assoc]; gcongr
      rcases t with (n | mc) | msg
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inl n)) s
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inr mc)) s
      · have hpos : 0 < qSrem := by
          rcases hQ1 with hno | hpos
          · exact absurd (by simp) hno
          · exact hpos
        refine hfold (qSrem - 1) c (fun x => ih x.1 (qSrem - 1) (by simpa using hQ2 x.1) x.2) ?_ ?_
        · have hstep := deferredDrawImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
            hp₀ hp hAbort (.inr msg) s
          rwa [ite_eq_left (by rfl), ← hc] at hstep
        · rw [add_comm, ← add_one_mul,
            show ((qSrem - 1 : ℕ) : ℝ≥0∞) + 1 = (qSrem : ℝ≥0∞) by
              have : qSrem - 1 + 1 = qSrem := by omega
              rw [← this]; push_cast; ring]

omit [SampleableType Stmt] in
/-- **The attempt-count law of the redrafted residual and its mean bound.** Mapping the
deferred-draw run to its attempt count — the combined new growth of the drawn and signed lists,
`(drawnlist.length - ws₀.length) + (signedlist.length - l.length)` — gives a count law whose mean is
at most `qSrem/(1-p)`. The attempt count dominates the reject count (it adds the signed-list growth,
one per signing query, covering each accepting attempt's fresh raw draw) yet keeps the same clean
mean, because the per-query charge `(reject expectation) + 1 = ∑_{a≤maxAttempts} p^a ≤ 1/(1-p)` is
identical to the loose reject charge — the `+1` is absorbed by tightening the reject bound from
`∑_{a<n} p^a` to `∑_{a<n} p^(a+1)`. -/
theorem deferredDraw_attemptKn_mean_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ) (hQ : oa.IsQueryBoundP (· matches Sum.inr _) qSrem)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) (ws₀ : List Commit) :
    (∑' n : ℕ, Pr[= n |
        (fun z : γ × DeferredState M Commit Chal =>
            (z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length)) <$>
          (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run (((re, l), ws₀), false)] *
        (n : ℝ≥0∞))
      ≤ ENNReal.ofReal ((qSrem : ℝ) / (1 - p_abort)) := by
  classical
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  set run : ProbComp (γ × DeferredState M Commit Chal) :=
    (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run (((re, l), ws₀), false) with hrun
  have hmean : (∑' n : ℕ, Pr[= n |
        (fun z : γ × DeferredState M Commit Chal =>
            (z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length)) <$> run] *
        (n : ℝ≥0∞))
      = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
          (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞) :=
    tsum_probOutput_map_mul run
      (fun z => (z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length))
      (fun n => (n : ℝ≥0∞))
  rw [hmean]
  -- Add back `ws₀.length + l.length` to recover the total combined size, bounded by the fold.
  have hmass : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run]) = 1 := by
    rw [hrun]
    exact tsum_probOutput_eq_one'
      (deferredDraw_run_neverFail ids M maxAttempts pk sk oa (((re, l), ws₀), false))
  have hsplit : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
        (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
        ((ws₀.length + l.length : ℕ) : ℝ≥0∞)
      ≤ ((ws₀.length + l.length : ℕ) : ℝ≥0∞) +
          (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    calc (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
          ((ws₀.length + l.length : ℕ) : ℝ≥0∞)
        = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            ((((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞) +
              ((ws₀.length + l.length : ℕ) : ℝ≥0∞)) := by
          rw [show (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                ((((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞) +
                  ((ws₀.length + l.length : ℕ) : ℝ≥0∞)))
              = (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                  (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
                ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                  ((ws₀.length + l.length : ℕ) : ℝ≥0∞) from by
              rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]]
          rw [ENNReal.tsum_mul_right, hmass, one_mul]
      _ = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞) := by
          refine tsum_congr fun z => ?_
          by_cases hz : z ∈ support run
          · have hpre : ws₀.length ≤ z.2.1.2.length :=
              (deferredDraw_run_drawn_prefix ids M maxAttempts pk sk oa _ z hz).length_le
            have hpre2 : l.length ≤ z.2.1.1.2.length :=
              deferredDraw_run_signed_prefix ids M maxAttempts pk sk oa _ z hz
            congr 1
            rw [← Nat.cast_add]
            congr 1
            omega
          · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
      _ ≤ ((ws₀.length + l.length : ℕ) : ℝ≥0∞) +
            (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
          have := deferredDraw_run_expected_attemptCount_le ids M maxAttempts pk sk hp₀ hp hAbort
            oa qSrem hQ (((re, l), ws₀), false)
          rwa [← hrun] at this
  have hcancel : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
        (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞))
      ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [add_comm] at hsplit
    exact (ENNReal.add_le_add_iff_left (by simp : ((ws₀.length + l.length : ℕ) : ℝ≥0∞) ≠ ∞)).mp
      hsplit
  refine hcancel.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_natCast qSrem, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end scaffold

end EUF_CMA

end FiatShamirWithAbort
