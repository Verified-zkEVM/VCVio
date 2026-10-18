/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.DrawCollectingBody

/-!
# EUF-CMA for Fiat-Shamir with aborts: DeferredCoupling

The deferred-coupling reduction: the ghost-blind bad event is dominated by the bad
event of the deferred-draw run (`ghostBlind_bad_le_deferredDraw`).

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

/-! ### The deferred-coupling reduction

The eager ghost-blind bad marginal reduces, through the deferred-draw handler `deferredDrawImpl`,
to the deferred run's bad marginal:

* `ghostBlind_bad_le_deferredDraw` is a *pointwise coupling* of the eager ghost-blind
  run with the deferred-draw run, established on the pointwise mono skeleton
  `relTriple_simulateQ_run_mono` carrying the state invariant `deferredCoupleInv` (real cache and
  signed list equal; ghost domain covered by the drawn-commitment list; bad-flag ordered). The
  read step is an output-equal coupling (both answer from the real layer via `roStep`, and the
  membership flag fires more readily on the deferred side because it ignores the message component);
  the sign step couples the two bodies' `ids.commit` draws so the eager ghost writes and the
  deferred draws stay in lockstep. `prEvent_le_of_relTriple` then reads off the ordered bad
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
/-- **Ghost-blind → deferred coupling.** The ghost-blind run's bad marginal is at most
the deferred-draw run's bad marginal, from any pair of `deferredCoupleInv`-related start states.

Reads off the bad-flag ordering component of the invariant from the run coupling
`deferredCouple_run` via `prEvent_le_of_relTriple`. -/
theorem ghostBlind_bad_le_deferredDraw {γ : Type}
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal)
    (hinv : deferredCoupleInv M s₁ s₂) :
    Pr{let z ← (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) oa).run s₁}[z.2.2 = true]
      ≤ Pr{let z ← (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run
              s₂}[z.2.2 = true] :=
  OracleComp.ProgramLogic.Relational.prEvent_le_of_relTriple
    (deferredCouple_run ids M maxAttempts pk sk oa s₁ s₂ hinv)
    (fun _ _ hp => hp.2.2.2)

end scaffold

end EUF_CMA

end FiatShamirWithAbort
