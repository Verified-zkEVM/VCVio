/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.FlagHandlers
public import VCVio.ProgramLogic.Library

/-!
# Specifications for the GPV flag-instrumented handlers

Specifications for the handlers of `VCVio.CryptoFoundations.GPVHashAndSign.FlagHandlers` under the
necessary reading (`open scoped OracleComp.Necessary`): the collision-flag handlers
`gpvRealImplFlag`, `progGameRunImplNoRecFlag`, their signed-set variants `gpvRealImplFlagFresh`,
`progGameRunImplNoRecFlagFresh`, and the flag-free `gpvRealImplFresh`.

* *Non-signing queries* run the flagless handler on the cache and keep the rest of the state:
  `*_wp_inl` (`spec high`) reads the step through the weakest precondition of `gpvRealImpl` or
  `progGameRunImplNoRec`, so `vcgen` continues with their rules from
  `VCVio.ProgramLogic.Library.T3.GPVHashAndSign.GameRuns`; `mem_support_*_inl_iff` (in
  `simulateQ_nf`) is the support form.
* *Signing queries* are exact and in one branch (`*_wp_sign`, `spec high`;
  `mem_support_*_sign_iff`): the cache is updated at `(r, msg)`, the message inserted into the
  signed set, and the flag or-ed with `saltKeyed` of the pre-state cache at the drawn salt.
* *Whole runs.* Each handler is `QueryImpl.MonotoneState`: the real cache grows (the programmed
  one in its keys), the signed set grows and the flag is never lowered.
-/

@[expose] public section

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary

namespace GPVHashAndSign

/-! ## Steps that run a handler on one state component -/

section keep

variable {ρ σ α : Type} (x : StateT σ ProbComp α) (mx : StateT ρ ProbComp α) (get : ρ → σ)
  (put : σ → ρ → ρ)

/-- A step running `x` on the component `get s` and writing its final state back with `put` has
the weakest precondition of `x`. -/
theorem wp_of_run_eq_map (h : ∀ s, mx.run s = (fun p => (p.1, put p.2 s)) <$> x.run (get s))
    (post : α → ρ → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => wp x (fun a c => post a (put c s)) epost (get s) ⦄ mx ⦃ post; epost ⦄ :=
  ⟨fun s => by
    rw [StateT.wp_apply_eq, StateT.wp_apply_eq, h]
    exact WPMonad.map_le_wp_map (m := ProbComp) (fun p => (p.1, put p.2 s)) (x.run (get s))
      (fun z => post z.1 z.2) epost⟩

/-- The support form of `wp_of_run_eq_map`. -/
theorem mem_support_of_run_eq_map
    (h : ∀ s, mx.run s = (fun p => (p.1, put p.2 s)) <$> x.run (get s)) {s s' : ρ} {a : α} :
    (a, s') ∈ support (mx.run s) ↔ ∃ c, (a, c) ∈ support (x.run (get s)) ∧ s' = put c s := by
  rw [h, support_map]
  aesop

end keep

variable {PK SK Domain Range : Type} (psf : PreimageSampleableFunction PK SK Domain Range)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]

local notation "GSpec" => (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))
local notation "GCache" => OracleSpec.QueryCache (Salt × M →ₒ Range)

omit [SampleableType Salt] in
/-- Caching an answer never uncaches a key. -/
private theorem isSome_cacheQuery' {c : GCache} {t t' : Salt × M} {v : Range}
    (h : (c t).isSome) : ((c.cacheQuery t' v) t).isSome := by
  rcases eq_or_ne t t' with rfl | h' <;> simp_all

/-- Run one unfolded handler step into its support. -/
local macro "run_support" : tactic => `(tactic| simp only [support_map, Set.mem_image,
  mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, support_uniformSample,
  Set.mem_univ, true_and, Prod.exists, randomOracle.mem_support_run_iff])

/-! ## Real handlers -/

section real

variable [DecidableEq Range] [SampleableType Range] {p : PK → SK → Bool}
  (hr : GenerableRelation PK SK p) (pk : PK) (sk : SK)

/-- A non-signing query of the real handler only grows its cache. -/
private theorem gpvRealImpl_inl_le {q : (unifSpec + (Salt × M →ₒ Range)).Domain} {c : GCache} :
    ∀ z ∈ support ((gpvRealImpl psf hr M Salt pk sk (.inl q)).run c), c ≤ z.2 := by
  rcases q with n | mc
  · rw [gpvRealImpl_run_unif]; simp
  · rw [gpvRealImpl_run_read]; exact QueryImpl.withCaching_cache_le _ _ c

/-- A non-signing query of the flag handler is a real step on the cache, keeping the flag. -/
@[spec high]
theorem gpvRealImplFlag_wp_inl (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (post : (GSpec).Range (.inl q) → GCache × Bool → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => wp (gpvRealImpl psf hr M Salt pk sk (.inl q)) (fun a c => post a (c, s.2)) epost
        s.1 ⦄ gpvRealImplFlag psf hr M Salt pk sk (.inl q) ⦃ post; epost ⦄ :=
  wp_of_run_eq_map _ _ Prod.fst (fun c s => (c, s.2))
    (gpvRealImplFlag_run_inl psf hr M Salt pk sk q) post

/-- A reachable non-signing step of the flag handler is a real step keeping the flag. -/
@[simulateQ_nf]
theorem mem_support_gpvRealImplFlag_inl_iff {q : (unifSpec + (Salt × M →ₒ Range)).Domain}
    {s s' : GCache × Bool} {a : (GSpec).Range (.inl q)} :
    (a, s') ∈ support ((gpvRealImplFlag psf hr M Salt pk sk (.inl q)).run s) ↔
      (a, s'.1) ∈ support ((gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1) ∧ s'.2 = s.2 := by
  rw [mem_support_of_run_eq_map _ _ Prod.fst (fun c s => (c, s.2))
    (gpvRealImplFlag_run_inl psf hr M Salt pk sk q)]
  exact ⟨fun ⟨c, hc, he⟩ => he ▸ ⟨hc, rfl⟩, fun ⟨hc, he⟩ => ⟨s'.1, hc, Prod.ext rfl he⟩⟩

/-- A reachable signing step of the flag handler is a real signing step or-ing the flag with
`saltKeyed` at the drawn salt. -/
@[simulateQ_nf]
theorem mem_support_gpvRealImplFlag_sign_iff {msg : M} {s s' : GCache × Bool}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((gpvRealImplFlag psf hr M Salt pk sk (.inr msg)).run s) ↔
      (∃ v, ((s.1 (σ.1, msg) = some v ∧ s'.1 = s.1) ∨
        (s.1 (σ.1, msg) = none ∧ s'.1 = s.1.cacheQuery (σ.1, msg) v)) ∧
        σ.2 ∈ support (psf.trapdoorSample pk sk v)) ∧ s'.2 = (s.2 || saltKeyed M Salt s.1 σ.1) := by
  obtain ⟨r, sgn⟩ := σ
  rw [gpvRealImplFlag_run_inr]
  run_support
  aesop

/-- One signing query of the flag handler, exactly: the real signing step, with the flag or-ed
with `saltKeyed` of the pre-state cache at the drawn salt. -/
@[spec high]
theorem gpvRealImplFlag_wp_sign (msg : M) (post : (GSpec).Range (.inr msg) → GCache × Bool → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r v sgn, (s.1 (r, msg) = none ∨ s.1 (r, msg) = some v) →
        sgn ∈ support (psf.trapdoorSample pk sk v) →
        post (r, sgn) (s.1.cacheQuery (r, msg) v, s.2 || saltKeyed M Salt s.1 r) ⦄
      gpvRealImplFlag psf hr M Salt pk sk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h σ ⟨c', b'⟩ hz => by
    obtain ⟨⟨v, ⟨hc, rfl⟩ | ⟨hc, rfl⟩, hs⟩, rfl⟩ :=
      (mem_support_gpvRealImplFlag_sign_iff psf M Salt hr pk sk).1 hz
    · simpa [QueryCache.cacheQuery_eq_self_of_eq_some hc] using h σ.1 v σ.2 (.inr hc) hs
    · exact h σ.1 v σ.2 (.inl hc) hs

/-- The flag handler only grows its cache and never lowers its flag. -/
instance monotoneState_gpvRealImplFlag :
    (gpvRealImplFlag psf hr M Salt pk sk).MonotoneState
      fun s s' => s.1 ≤ s'.1 ∧ (s.2 = true → s'.2 = true) where
  refl _ := ⟨le_rfl, id⟩
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₂.2 ∘ h₁.2⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with q | msg
    · obtain ⟨hc, hb⟩ := (mem_support_gpvRealImplFlag_inl_iff psf M Salt hr pk sk).1 hz
      exact ⟨gpvRealImpl_inl_le psf M Salt hr pk sk _ hc, fun h => hb ▸ h⟩
    · obtain ⟨⟨v, ⟨-, h₁⟩ | ⟨hc, h₁⟩, -⟩, hb⟩ :=
        (mem_support_gpvRealImplFlag_sign_iff psf M Salt hr pk sk).1 hz <;>
        refine ⟨h₁ ▸ ?_, fun h => by simp [hb, h]⟩
      exacts [le_rfl, QueryCache.le_cacheQuery _ hc]

/-- A non-signing query of the fresh flag handler is a real step on the cache. -/
@[spec high]
theorem gpvRealImplFlagFresh_wp_inl (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (post : (GSpec).Range (.inl q) → (GCache × Finset M) × Bool → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => wp (gpvRealImpl psf hr M Salt pk sk (.inl q))
        (fun a c => post a ((c, s.1.2), s.2)) epost s.1.1 ⦄
      gpvRealImplFlagFresh psf hr M Salt pk sk (.inl q) ⦃ post; epost ⦄ :=
  wp_of_run_eq_map _ _ (fun s => s.1.1) (fun c s => ((c, s.1.2), s.2))
    (gpvRealImplFlagFresh_run_inl psf hr M Salt pk sk q) post

/-- A reachable signing step of the fresh flag handler also inserts the message. -/
@[simulateQ_nf]
theorem mem_support_gpvRealImplFlagFresh_sign_iff {msg : M} {s s' : (GCache × Finset M) × Bool}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((gpvRealImplFlagFresh psf hr M Salt pk sk (.inr msg)).run s) ↔
      (∃ v, ((s.1.1 (σ.1, msg) = some v ∧ s'.1.1 = s.1.1) ∨
        (s.1.1 (σ.1, msg) = none ∧ s'.1.1 = s.1.1.cacheQuery (σ.1, msg) v)) ∧
        σ.2 ∈ support (psf.trapdoorSample pk sk v)) ∧ s'.1.2 = insert msg s.1.2 ∧
        s'.2 = (s.2 || saltKeyed M Salt s.1.1 σ.1) := by
  obtain ⟨r, sgn⟩ := σ
  rw [gpvRealImplFlagFresh_run_inr]
  run_support
  aesop

/-- One signing query of the fresh flag handler, exactly. -/
@[spec high]
theorem gpvRealImplFlagFresh_wp_sign (msg : M)
    (post : (GSpec).Range (.inr msg) → (GCache × Finset M) × Bool → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r v sgn, (s.1.1 (r, msg) = none ∨ s.1.1 (r, msg) = some v) →
        sgn ∈ support (psf.trapdoorSample pk sk v) → post (r, sgn)
          ((s.1.1.cacheQuery (r, msg) v, insert msg s.1.2), s.2 || saltKeyed M Salt s.1.1 r) ⦄
      gpvRealImplFlagFresh psf hr M Salt pk sk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h σ ⟨⟨c', S'⟩, b'⟩ hz => by
    obtain ⟨⟨v, ⟨hc, rfl⟩ | ⟨hc, rfl⟩, hs⟩, rfl, rfl⟩ :=
      (mem_support_gpvRealImplFlagFresh_sign_iff psf M Salt hr pk sk).1 hz
    · simpa [QueryCache.cacheQuery_eq_self_of_eq_some hc] using h σ.1 v σ.2 (.inr hc) hs
    · exact h σ.1 v σ.2 (.inl hc) hs

/-- The fresh flag handler grows its cache and signed set and never lowers its flag. -/
instance monotoneState_gpvRealImplFlagFresh :
    (gpvRealImplFlagFresh psf hr M Salt pk sk).MonotoneState
      fun s s' => (s.1.1 ≤ s'.1.1 ∧ s.1.2 ⊆ s'.1.2) ∧ (s.2 = true → s'.2 = true) where
  refl _ := ⟨⟨le_rfl, subset_rfl⟩, id⟩
  trans _ _ _ h₁ h₂ := ⟨⟨h₁.1.1.trans h₂.1.1, h₁.1.2.trans h₂.1.2⟩, h₂.2 ∘ h₁.2⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with q | msg
    · obtain ⟨c, hc, rfl⟩ := (mem_support_of_run_eq_map _ _ (fun s => s.1.1)
        (fun c s => ((c, s.1.2), s.2)) (gpvRealImplFlagFresh_run_inl psf hr M Salt pk sk q)).1 hz
      exact ⟨⟨gpvRealImpl_inl_le psf M Salt hr pk sk _ hc, subset_rfl⟩, id⟩
    · obtain ⟨⟨v, ⟨-, h₁⟩ | ⟨hc, h₁⟩, -⟩, h₂, hb⟩ :=
        (mem_support_gpvRealImplFlagFresh_sign_iff psf M Salt hr pk sk).1 hz <;>
        refine ⟨⟨h₁ ▸ ?_, h₂ ▸ Finset.subset_insert _ _⟩, fun h => by simp [hb, h]⟩
      exacts [le_rfl, QueryCache.le_cacheQuery _ hc]

/-- A non-signing query of the flag-free fresh handler is a real step on the cache. -/
@[spec high]
theorem gpvRealImplFresh_wp_inl (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (post : (GSpec).Range (.inl q) → GCache × Finset M → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => wp (gpvRealImpl psf hr M Salt pk sk (.inl q)) (fun a c => post a (c, s.2)) epost
        s.1 ⦄ gpvRealImplFresh psf hr M Salt pk sk (.inl q) ⦃ post; epost ⦄ :=
  wp_of_run_eq_map _ _ Prod.fst (fun c s => (c, s.2))
    (gpvRealImplFresh_run_inl psf hr M Salt pk sk q) post

/-- A reachable signing step of the flag-free fresh handler inserts the message. -/
@[simulateQ_nf]
theorem mem_support_gpvRealImplFresh_sign_iff {msg : M} {s s' : GCache × Finset M}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((gpvRealImplFresh psf hr M Salt pk sk (.inr msg)).run s) ↔
      (∃ v, ((s.1 (σ.1, msg) = some v ∧ s'.1 = s.1) ∨
        (s.1 (σ.1, msg) = none ∧ s'.1 = s.1.cacheQuery (σ.1, msg) v)) ∧
        σ.2 ∈ support (psf.trapdoorSample pk sk v)) ∧ s'.2 = insert msg s.2 := by
  obtain ⟨r, sgn⟩ := σ
  rw [gpvRealImplFresh_run_inr]
  run_support
  aesop

/-- One signing query of the flag-free fresh handler, exactly. -/
@[spec high]
theorem gpvRealImplFresh_wp_sign (msg : M)
    (post : (GSpec).Range (.inr msg) → GCache × Finset M → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r v sgn, (s.1 (r, msg) = none ∨ s.1 (r, msg) = some v) →
        sgn ∈ support (psf.trapdoorSample pk sk v) →
        post (r, sgn) (s.1.cacheQuery (r, msg) v, insert msg s.2) ⦄
      gpvRealImplFresh psf hr M Salt pk sk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h σ ⟨c', S'⟩ hz => by
    obtain ⟨⟨v, ⟨hc, rfl⟩ | ⟨hc, rfl⟩, hs⟩, rfl⟩ :=
      (mem_support_gpvRealImplFresh_sign_iff psf M Salt hr pk sk).1 hz
    · simpa [QueryCache.cacheQuery_eq_self_of_eq_some hc] using h σ.1 v σ.2 (.inr hc) hs
    · exact h σ.1 v σ.2 (.inl hc) hs

/-- The flag-free fresh handler grows its cache and its signed set. -/
instance monotoneState_gpvRealImplFresh :
    (gpvRealImplFresh psf hr M Salt pk sk).MonotoneState
      fun s s' => s.1 ≤ s'.1 ∧ s.2 ⊆ s'.2 where
  refl _ := ⟨le_rfl, subset_rfl⟩
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with q | msg
    · obtain ⟨c, hc, rfl⟩ := (mem_support_of_run_eq_map _ _ Prod.fst (fun c s => (c, s.2))
        (gpvRealImplFresh_run_inl psf hr M Salt pk sk q)).1 hz
      exact ⟨gpvRealImpl_inl_le psf M Salt hr pk sk _ hc, subset_rfl⟩
    · obtain ⟨⟨v, ⟨-, h₁⟩ | ⟨hc, h₁⟩, -⟩, h₂⟩ :=
        (mem_support_gpvRealImplFresh_sign_iff psf M Salt hr pk sk).1 hz <;>
        refine ⟨h₁ ▸ ?_, h₂ ▸ Finset.subset_insert _ _⟩
      exacts [le_rfl, QueryCache.le_cacheQuery _ hc]

end real

/-! ## Programmed handlers -/

section prog

variable (domainSample : PK → ProbComp Domain) (pk : PK)

/-- A non-signing query of the programmed handler never uncaches a key. -/
private theorem progGameRunImplNoRec_inl_isSome {q : (unifSpec + (Salt × M →ₒ Range)).Domain}
    {c : GCache} : ∀ z ∈ support ((progGameRunImplNoRec psf M Salt domainSample pk (.inl q)).run c),
      ∀ t, (c t).isSome → (z.2 t).isSome := by
  rcases q with n | mc
  · rw [progGameRunImplNoRec_run_unif]; simp
  · rw [progGameRunImplNoRec_run_read]
    cases c mc <;> simp only [support_pure, Set.mem_singleton_iff, support_map, Set.mem_image] <;>
      aesop (add safe isSome_cacheQuery')

/-- A non-signing query of the programmed flag handler is a programmed step, keeping the flag. -/
@[spec high]
theorem progGameRunImplNoRecFlag_wp_inl (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (post : (GSpec).Range (.inl q) → GCache × Bool → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => wp (progGameRunImplNoRec psf M Salt domainSample pk (.inl q))
        (fun a c => post a (c, s.2)) epost s.1 ⦄
      progGameRunImplNoRecFlag psf M Salt domainSample pk (.inl q) ⦃ post; epost ⦄ :=
  wp_of_run_eq_map _ _ Prod.fst (fun c s => (c, s.2))
    (progGameRunImplNoRecFlag_run_inl psf M Salt domainSample pk q) post

/-- A reachable signing step of the programmed flag handler programs `(r, msg)` and or-s the flag
with `saltKeyed` at the drawn salt. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplNoRecFlag_sign_iff {msg : M} {s s' : GCache × Bool}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((progGameRunImplNoRecFlag psf M Salt domainSample pk (.inr msg)).run s) ↔
      σ.2 ∈ support (domainSample pk) ∧
        s' = (s.1.cacheQuery (σ.1, msg) (psf.eval pk σ.2), s.2 || saltKeyed M Salt s.1 σ.1) := by
  obtain ⟨r, sd⟩ := σ
  rw [progGameRunImplNoRecFlag_run_inr]
  run_support
  aesop

/-- One signing query of the programmed flag handler, exactly. -/
@[spec high]
theorem progGameRunImplNoRecFlag_wp_sign (msg : M)
    (post : (GSpec).Range (.inr msg) → GCache × Bool → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r sd, sd ∈ support (domainSample pk) →
        post (r, sd) (s.1.cacheQuery (r, msg) (psf.eval pk sd), s.2 || saltKeyed M Salt s.1 r) ⦄
      progGameRunImplNoRecFlag psf M Salt domainSample pk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h σ s' hz => by
    obtain ⟨hs, rfl⟩ :=
      (mem_support_progGameRunImplNoRecFlag_sign_iff psf M Salt domainSample pk).1 hz
    exact h σ.1 σ.2 hs

/-- A reachable signing step of the programmed fresh flag handler also inserts the message. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplNoRecFlagFresh_sign_iff {msg : M}
    {s s' : (GCache × Finset M) × Bool} {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈
        support ((progGameRunImplNoRecFlagFresh psf M Salt domainSample pk (.inr msg)).run s) ↔
      σ.2 ∈ support (domainSample pk) ∧
        s' = ((s.1.1.cacheQuery (σ.1, msg) (psf.eval pk σ.2), insert msg s.1.2),
          s.2 || saltKeyed M Salt s.1.1 σ.1) := by
  obtain ⟨r, sd⟩ := σ
  rw [progGameRunImplNoRecFlagFresh_run_inr]
  run_support
  aesop

/-- One signing query of the programmed fresh flag handler, exactly. -/
@[spec high]
theorem progGameRunImplNoRecFlagFresh_wp_sign (msg : M)
    (post : (GSpec).Range (.inr msg) → (GCache × Finset M) × Bool → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r sd, sd ∈ support (domainSample pk) → post (r, sd)
        ((s.1.1.cacheQuery (r, msg) (psf.eval pk sd), insert msg s.1.2),
          s.2 || saltKeyed M Salt s.1.1 r) ⦄
      progGameRunImplNoRecFlagFresh psf M Salt domainSample pk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h σ s' hz => by
    obtain ⟨hs, rfl⟩ :=
      (mem_support_progGameRunImplNoRecFlagFresh_sign_iff psf M Salt domainSample pk).1 hz
    exact h σ.1 σ.2 hs

/-- A non-signing query of the programmed fresh flag handler is a programmed step. -/
@[spec high]
theorem progGameRunImplNoRecFlagFresh_wp_inl (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (post : (GSpec).Range (.inl q) → (GCache × Finset M) × Bool → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => wp (progGameRunImplNoRec psf M Salt domainSample pk (.inl q))
        (fun a c => post a ((c, s.1.2), s.2)) epost s.1.1 ⦄
      progGameRunImplNoRecFlagFresh psf M Salt domainSample pk (.inl q) ⦃ post; epost ⦄ :=
  wp_of_run_eq_map _ _ (fun s => s.1.1) (fun c s => ((c, s.1.2), s.2))
    (progGameRunImplNoRecFlagFresh_run_inl psf M Salt domainSample pk q) post

/-- The programmed flag handler never uncaches a key and never lowers its flag. -/
instance monotoneState_progGameRunImplNoRecFlag :
    (progGameRunImplNoRecFlag psf M Salt domainSample pk).MonotoneState
      fun s s' => (∀ t, (s.1 t).isSome → (s'.1 t).isSome) ∧ (s.2 = true → s'.2 = true) where
  refl _ := ⟨fun _ => id, id⟩
  trans _ _ _ h₁ h₂ := ⟨fun t => h₂.1 t ∘ h₁.1 t, h₂.2 ∘ h₁.2⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with q | msg
    · obtain ⟨c, hc, rfl⟩ := (mem_support_of_run_eq_map _ _ Prod.fst (fun c s => (c, s.2))
        (progGameRunImplNoRecFlag_run_inl psf M Salt domainSample pk q)).1 hz
      exact ⟨progGameRunImplNoRec_inl_isSome psf M Salt domainSample pk _ hc, id⟩
    · obtain ⟨-, rfl⟩ :=
        (mem_support_progGameRunImplNoRecFlag_sign_iff psf M Salt domainSample pk).1 hz
      exact ⟨fun _ => isSome_cacheQuery' M Salt, fun h => by simp [h]⟩

/-- The programmed fresh flag handler never uncaches a key, grows its signed set and never
lowers its flag. -/
instance monotoneState_progGameRunImplNoRecFlagFresh :
    (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk).MonotoneState
      fun s s' => ((∀ t, (s.1.1 t).isSome → (s'.1.1 t).isSome) ∧ s.1.2 ⊆ s'.1.2) ∧
        (s.2 = true → s'.2 = true) where
  refl _ := ⟨⟨fun _ => id, subset_rfl⟩, id⟩
  trans _ _ _ h₁ h₂ := ⟨⟨fun t => h₂.1.1 t ∘ h₁.1.1 t, h₁.1.2.trans h₂.1.2⟩, h₂.2 ∘ h₁.2⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with q | msg
    · obtain ⟨c, hc, rfl⟩ := (mem_support_of_run_eq_map _ _ (fun s => s.1.1)
        (fun c s => ((c, s.1.2), s.2))
        (progGameRunImplNoRecFlagFresh_run_inl psf M Salt domainSample pk q)).1 hz
      exact ⟨⟨progGameRunImplNoRec_inl_isSome psf M Salt domainSample pk _ hc, subset_rfl⟩, id⟩
    · obtain ⟨-, rfl⟩ :=
        (mem_support_progGameRunImplNoRecFlagFresh_sign_iff psf M Salt domainSample pk).1 hz
      exact ⟨⟨fun _ => isSome_cacheQuery' M Salt, Finset.subset_insert _ _⟩, fun h => by simp [h]⟩

end prog

end GPVHashAndSign
