/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.GameRuns
public import VCVio.ProgramLogic.Library

/-!
# Specifications for the GPV game-run handlers

Specifications for the handlers of `VCVio.CryptoFoundations.GPVHashAndSign.GameRuns` under the
necessary reading (`open scoped OracleComp.Necessary`): `gpvRealImpl`, `progGameRunImplNoRec`
and their salt-tape variants `gpvRealImplTape`, `progGameRunImplTape`.

* *Support.* `mem_support_*_{unif,read,sign}_iff` (in `simulateQ_nf`) describe a reachable step
  by its answer and final state. Answers and posts are typed at the sum's answer type, the form
  `simulateQ_nf` produces and `vcgen` matches.
* *One query.* `*_wp_{unif,read,sign}` (`spec high`) are exact and have one branch: the state is
  updated at the queried point, the answer constrained by the hit/miss case; a tape signing query
  consumes the head salt (`s.2 = [] ∨ s.2.head? = some r`).
* *Whole runs* (`QueryImpl.MonotoneState`). `gpvRealImpl` grows its cache (`≤`); the programmed
  handlers, which overwrite on signing, grow their set of cached keys; the tape handlers also
  consume their tape (`<:+`).
-/

@[expose] public section

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary

namespace GPVHashAndSign

variable {PK SK Domain Range : Type} (psf : PreimageSampleableFunction PK SK Domain Range)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]

local notation "GSpec" => (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))
local notation "GCache" => OracleSpec.QueryCache (Salt × M →ₒ Range)

/-- Run one unfolded handler step into its support. -/
local macro "run_support" : tactic => `(tactic| simp only [support_map, Set.mem_image,
  mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, support_uniformSample,
  Set.mem_univ, true_and, List.head?_nil, List.tail_nil, true_or, List.head?_cons, List.tail_cons,
  reduceCtorEq, false_or, Option.some.injEq, Prod.exists, randomOracle.mem_support_run_iff])

omit [SampleableType Salt] in
/-- Caching an answer never uncaches a key. -/
theorem isSome_cacheQuery {c : GCache} {t t' : Salt × M} {v : Range} (h : (c t).isSome) :
    ((c.cacheQuery t' v) t).isSome := by
  rcases eq_or_ne t t' with rfl | h' <;> simp_all

section real

variable [DecidableEq Range] [SampleableType Range] {p : PK → SK → Bool}
  (hr : GenerableRelation PK SK p) (pk : PK) (sk : SK)

/-- A uniform query of the real handler keeps the cache. -/
@[simulateQ_nf]
theorem mem_support_gpvRealImpl_unif_iff {n : ℕ} {c c' : GCache}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, c') ∈ support ((gpvRealImpl psf hr M Salt pk sk (.inl (.inl n))).run c) ↔ c' = c := by
  rw [gpvRealImpl_run_unif]; simp [eq_comm]

/-- A random-oracle query of the real handler is a lazy random-oracle step. -/
@[simulateQ_nf]
theorem mem_support_gpvRealImpl_read_iff {mc : Salt × M} {c c' : GCache}
    {v : (GSpec).Range (.inl (.inr mc))} :
    (v, c') ∈ support ((gpvRealImpl psf hr M Salt pk sk (.inl (.inr mc))).run c) ↔
      (c mc = some v ∧ c' = c) ∨ (c mc = none ∧ c' = c.cacheQuery mc v) := by
  rw [gpvRealImpl_run_read]
  exact randomOracle.mem_support_run_iff

/-- A real signing query reads the random oracle at `(r, msg)` for some salt `r`. -/
@[simulateQ_nf]
theorem mem_support_gpvRealImpl_sign_iff {msg : M} {c c' : GCache} {σ : (GSpec).Range (.inr msg)} :
    (σ, c') ∈ support ((gpvRealImpl psf hr M Salt pk sk (.inr msg)).run c) ↔
      ∃ v, ((c (σ.1, msg) = some v ∧ c' = c) ∨
        (c (σ.1, msg) = none ∧ c' = c.cacheQuery (σ.1, msg) v)) ∧
        σ.2 ∈ support (psf.trapdoorSample pk sk v) := by
  obtain ⟨r, sgn⟩ := σ
  rw [gpvRealImpl_run_sign]
  run_support
  aesop

/-- One uniform query of the real handler: any answer, the cache unchanged. -/
@[spec high]
theorem gpvRealImpl_wp_unif (n : ℕ) (post : (GSpec).Range (.inl (.inl n)) → GCache → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ u, post u c ⦄ gpvRealImpl psf hr M Salt pk sk (.inl (.inl n)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_gpvRealImpl_unif_iff psf M Salt hr pk sk).1 hz ▸ h u

/-- One random-oracle query of the real handler, exactly. -/
@[spec high]
theorem gpvRealImpl_wp_read (mc : Salt × M) (post : (GSpec).Range (.inl (.inr mc)) → GCache → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ v, (c mc = none ∨ c mc = some v) → post v (c.cacheQuery mc v) ⦄
      gpvRealImpl psf hr M Salt pk sk (.inl (.inr mc)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun c h v c' hz => by
    rcases (mem_support_gpvRealImpl_read_iff psf M Salt hr pk sk).1 hz with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
    · simpa [QueryCache.cacheQuery_eq_self_of_eq_some hc] using h v (.inr hc)
    · exact h v (.inl hc)

/-- One real signing query: the answer `v` at `(r, msg)` is cached, a preimage returned. -/
@[spec high]
theorem gpvRealImpl_wp_sign (msg : M) (post : (GSpec).Range (.inr msg) → GCache → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ r v sgn, (c (r, msg) = none ∨ c (r, msg) = some v) →
        sgn ∈ support (psf.trapdoorSample pk sk v) → post (r, sgn) (c.cacheQuery (r, msg) v) ⦄
      gpvRealImpl psf hr M Salt pk sk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun c h σ c' hz => by
    obtain ⟨v, ⟨hc, rfl⟩ | ⟨hc, rfl⟩, hs⟩ :=
      (mem_support_gpvRealImpl_sign_iff psf M Salt hr pk sk).1 hz
    · simpa [QueryCache.cacheQuery_eq_self_of_eq_some hc] using h σ.1 v σ.2 (.inr hc) hs
    · exact h σ.1 v σ.2 (.inl hc) hs

/-- The real handler only grows its cache, so whole runs are framed by the cache order. -/
instance monotoneState_gpvRealImpl :
    (gpvRealImpl psf hr M Salt pk sk).MonotoneState (· ≤ ·) :=
  .of_le fun t c ⟨a, c'⟩ hz => by
    rcases t with (n | mc) | msg
    · exact ((mem_support_gpvRealImpl_unif_iff psf M Salt hr pk sk).1 hz).ge
    · rcases (mem_support_gpvRealImpl_read_iff psf M Salt hr pk sk).1 hz with
        ⟨-, rfl⟩ | ⟨hc, rfl⟩
      exacts [le_rfl, QueryCache.le_cacheQuery _ hc]
    · obtain ⟨_, ⟨-, rfl⟩ | ⟨hc, rfl⟩, -⟩ :=
        (mem_support_gpvRealImpl_sign_iff psf M Salt hr pk sk).1 hz
      exacts [le_rfl, QueryCache.le_cacheQuery _ hc]

end real

section prog

variable (domainSample : PK → ProbComp Domain) (pk : PK)

/-- A uniform query of the programmed handler keeps the cache. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplNoRec_unif_iff {n : ℕ} {c c' : GCache}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, c') ∈ support ((progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inl n))).run c) ↔
      c' = c := by
  rw [progGameRunImplNoRec_run_unif]; simp [eq_comm]

/-- A programmed random-oracle query is a hit, or a miss programming a forward image. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplNoRec_read_iff {mc : Salt × M} {c c' : GCache}
    {v : (GSpec).Range (.inl (.inr mc))} :
    (v, c') ∈ support ((progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inr mc))).run c) ↔
      (c mc = some v ∧ c' = c) ∨ (c mc = none ∧
        (∃ sd ∈ support (domainSample pk), psf.eval pk sd = v) ∧ c' = c.cacheQuery mc v) := by
  rw [progGameRunImplNoRec_run_read]
  cases h : c mc <;> simp only [support_map, support_pure, Set.mem_image, Set.mem_singleton_iff,
    Prod.mk.injEq] <;> aesop

/-- A programmed signing query programs `(r, msg) ↦ psf.eval pk sd` for a forward sample. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplNoRec_sign_iff {msg : M} {c c' : GCache}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, c') ∈ support ((progGameRunImplNoRec psf M Salt domainSample pk (.inr msg)).run c) ↔
      σ.2 ∈ support (domainSample pk) ∧ c' = c.cacheQuery (σ.1, msg) (psf.eval pk σ.2) := by
  obtain ⟨r, sd⟩ := σ
  rw [progGameRunImplNoRec_run_sign]
  run_support
  aesop

/-- One uniform query of the programmed handler: any answer, the cache unchanged. -/
@[spec high]
theorem progGameRunImplNoRec_wp_unif (n : ℕ)
    (post : (GSpec).Range (.inl (.inl n)) → GCache → Prop) {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ u, post u c ⦄ progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inl n))
      ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_progGameRunImplNoRec_unif_iff psf M Salt domainSample pk).1 hz ▸ h u

/-- One random-oracle query of the programmed handler, exactly. -/
@[spec high]
theorem progGameRunImplNoRec_wp_read (mc : Salt × M)
    (post : (GSpec).Range (.inl (.inr mc)) → GCache → Prop) {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ v, (c mc = some v ∨
        (c mc = none ∧ ∃ sd ∈ support (domainSample pk), psf.eval pk sd = v)) →
        post v (c.cacheQuery mc v) ⦄
      progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inr mc)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun c h v c' hz => by
    rcases (mem_support_progGameRunImplNoRec_read_iff psf M Salt domainSample pk).1 hz with
      ⟨hc, rfl⟩ | ⟨hc, hv, rfl⟩
    · simpa [QueryCache.cacheQuery_eq_self_of_eq_some hc] using h v (.inl hc)
    · exact h v (.inr ⟨hc, hv⟩)

/-- One programmed signing query, exactly: `(r, msg)` is programmed to `psf.eval pk sd`. -/
@[spec high]
theorem progGameRunImplNoRec_wp_sign (msg : M) (post : (GSpec).Range (.inr msg) → GCache → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ r sd, sd ∈ support (domainSample pk) →
        post (r, sd) (c.cacheQuery (r, msg) (psf.eval pk sd)) ⦄
      progGameRunImplNoRec psf M Salt domainSample pk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun c h σ c' hz => by
    obtain ⟨hs, rfl⟩ := (mem_support_progGameRunImplNoRec_sign_iff psf M Salt domainSample pk).1 hz
    exact h σ.1 σ.2 hs

/-- The programmed handler never uncaches a key. -/
instance monotoneState_progGameRunImplNoRec :
    (progGameRunImplNoRec psf M Salt domainSample pk).MonotoneState
      fun c c' => ∀ t, (c t).isSome → (c' t).isSome where
  refl _ _ := id
  trans _ _ _ h₁ h₂ t := h₂ t ∘ h₁ t
  step t c := by
    rintro ⟨a, c'⟩ hz t' ht'
    rcases t with (n | mc) | msg
    · rwa [(mem_support_progGameRunImplNoRec_unif_iff psf M Salt domainSample pk).1 hz]
    · rcases (mem_support_progGameRunImplNoRec_read_iff psf M Salt domainSample pk).1 hz with
        ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      exacts [ht', isSome_cacheQuery M Salt ht']
    · obtain ⟨-, rfl⟩ := (mem_support_progGameRunImplNoRec_sign_iff psf M Salt domainSample pk).1 hz
      exact isSome_cacheQuery M Salt ht'

end prog

local notation "TState" => OracleSpec.QueryCache (Salt × M →ₒ Range) × List Salt

section realTape

variable [SampleableType Range] (pk : PK) (sk : SK)

/-- A uniform query of the real tape handler keeps the state. -/
@[simulateQ_nf]
theorem mem_support_gpvRealImplTape_unif_iff {n : ℕ} {s s' : TState}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, s') ∈ support ((gpvRealImplTape psf M Salt pk sk (.inl (.inl n))).run s) ↔ s' = s := by
  rw [gpvRealImplTape_run_unif]; simp [eq_comm]

/-- A random-oracle query of the real tape handler is a lazy random-oracle step on the cache. -/
@[simulateQ_nf]
theorem mem_support_gpvRealImplTape_read_iff {mc : Salt × M} {s s' : TState}
    {v : (GSpec).Range (.inl (.inr mc))} :
    (v, s') ∈ support ((gpvRealImplTape psf M Salt pk sk (.inl (.inr mc))).run s) ↔
      (s.1 mc = some v ∧ s' = s) ∨ (s.1 mc = none ∧ s' = (s.1.cacheQuery mc v, s.2)) := by
  rw [gpvRealImplTape_run_read]
  simp only [support_map, Set.mem_image, Prod.exists, randomOracle.mem_support_run_iff,
    Prod.mk.injEq]
  aesop

/-- A real tape signing query consumes the head salt `r` (any on an empty tape). -/
@[simulateQ_nf]
theorem mem_support_gpvRealImplTape_sign_iff {msg : M} {s s' : TState}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((gpvRealImplTape psf M Salt pk sk (.inr msg)).run s) ↔
      (s.2 = [] ∨ s.2.head? = some σ.1) ∧ s'.2 = s.2.tail ∧ ∃ v,
        ((s.1 (σ.1, msg) = some v ∧ s'.1 = s.1) ∨
          (s.1 (σ.1, msg) = none ∧ s'.1 = s.1.cacheQuery (σ.1, msg) v)) ∧
        σ.2 ∈ support (psf.trapdoorSample pk sk v) := by
  obtain ⟨c, _ | ⟨r, tl⟩⟩ := s <;> obtain ⟨c', tl'⟩ := s' <;> obtain ⟨r', sgn⟩ := σ <;>
    simp only [gpvRealImplTape, StateT.run_mk] <;> run_support <;> aesop

/-- One uniform query of the real tape handler: any answer, the state unchanged. -/
@[spec high]
theorem gpvRealImplTape_wp_unif (n : ℕ) (post : (GSpec).Range (.inl (.inl n)) → TState → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ u, post u s ⦄ gpvRealImplTape psf M Salt pk sk (.inl (.inl n)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_gpvRealImplTape_unif_iff psf M Salt pk sk).1 hz ▸ h u

/-- One random-oracle query of the real tape handler, exactly; the tape is unchanged. -/
@[spec high]
theorem gpvRealImplTape_wp_read (mc : Salt × M)
    (post : (GSpec).Range (.inl (.inr mc)) → TState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v, (s.1 mc = none ∨ s.1 mc = some v) → post v (s.1.cacheQuery mc v, s.2) ⦄
      gpvRealImplTape psf M Salt pk sk (.inl (.inr mc)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h v s' hz => by
    rcases (mem_support_gpvRealImplTape_read_iff psf M Salt pk sk).1 hz with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
    · simpa [QueryCache.cacheQuery_eq_self_of_eq_some hc] using h v (.inr hc)
    · exact h v (.inl hc)

/-- One real tape signing query, exactly: the head salt is consumed. -/
@[spec high]
theorem gpvRealImplTape_wp_sign (msg : M) (post : (GSpec).Range (.inr msg) → TState → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r v sgn, (s.2 = [] ∨ s.2.head? = some r) →
        (s.1 (r, msg) = none ∨ s.1 (r, msg) = some v) → sgn ∈ support (psf.trapdoorSample pk sk v) →
        post (r, sgn) (s.1.cacheQuery (r, msg) v, s.2.tail) ⦄
      gpvRealImplTape psf M Salt pk sk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h σ ⟨c', tl'⟩ hz => by
    obtain ⟨hr, rfl, v, ⟨hc, rfl⟩ | ⟨hc, rfl⟩, hs⟩ :=
      (mem_support_gpvRealImplTape_sign_iff psf M Salt pk sk).1 hz
    · simpa [QueryCache.cacheQuery_eq_self_of_eq_some hc] using h σ.1 v σ.2 hr (.inr hc) hs
    · exact h σ.1 v σ.2 hr (.inl hc) hs

/-- The real tape handler only grows its cache and only consumes its tape. -/
instance monotoneState_gpvRealImplTape :
    (gpvRealImplTape psf M Salt pk sk).MonotoneState fun s s' => s.1 ≤ s'.1 ∧ s'.2 <:+ s.2 where
  refl _ := ⟨le_rfl, List.suffix_refl _⟩
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with (n | mc) | msg
    · rw [(mem_support_gpvRealImplTape_unif_iff psf M Salt pk sk).1 hz]
      exact ⟨le_rfl, List.suffix_refl _⟩
    · rcases (mem_support_gpvRealImplTape_read_iff psf M Salt pk sk).1 hz with
        ⟨-, rfl⟩ | ⟨hc, rfl⟩
      exacts [⟨le_rfl, List.suffix_refl _⟩, ⟨QueryCache.le_cacheQuery _ hc, List.suffix_refl _⟩]
    · obtain ⟨-, h₂, _, ⟨-, h₁⟩ | ⟨hc, h₁⟩, -⟩ :=
        (mem_support_gpvRealImplTape_sign_iff psf M Salt pk sk).1 hz <;>
        refine ⟨h₁ ▸ ?_, h₂ ▸ List.tail_suffix _⟩
      exacts [le_rfl, QueryCache.le_cacheQuery _ hc]

end realTape

section progTape

variable (domainSample : PK → ProbComp Domain) (pk : PK)

/-- A uniform query of the programmed tape handler keeps the state. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplTape_unif_iff {n : ℕ} {s s' : TState}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, s') ∈ support ((progGameRunImplTape psf M Salt domainSample pk (.inl (.inl n))).run s) ↔
      s' = s := by
  rw [progGameRunImplTape_run_unif]; simp [eq_comm]

/-- A programmed tape random-oracle query is a programmed read; the tape is unchanged. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplTape_read_iff {mc : Salt × M} {s s' : TState}
    {v : (GSpec).Range (.inl (.inr mc))} :
    (v, s') ∈ support ((progGameRunImplTape psf M Salt domainSample pk (.inl (.inr mc))).run s) ↔
      (s.1 mc = some v ∧ s' = s) ∨ (s.1 mc = none ∧
        (∃ sd ∈ support (domainSample pk), psf.eval pk sd = v) ∧
          s' = (s.1.cacheQuery mc v, s.2)) := by
  rw [progGameRunImplTape_run_read]
  cases h : s.1 mc <;> run_support <;> aesop

/-- A programmed tape signing query consumes the head salt and programs `(r, msg)`. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplTape_sign_iff {msg : M} {s s' : TState}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run s) ↔
      (s.2 = [] ∨ s.2.head? = some σ.1) ∧ σ.2 ∈ support (domainSample pk) ∧
        s' = (s.1.cacheQuery (σ.1, msg) (psf.eval pk σ.2), s.2.tail) := by
  obtain ⟨c, _ | ⟨r, tl⟩⟩ := s <;> obtain ⟨r', sd⟩ := σ <;>
    simp only [progGameRunImplTape, StateT.run_mk] <;> run_support <;> aesop

/-- One uniform query of the programmed tape handler: any answer, the state unchanged. -/
@[spec high]
theorem progGameRunImplTape_wp_unif (n : ℕ)
    (post : (GSpec).Range (.inl (.inl n)) → TState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ u, post u s ⦄ progGameRunImplTape psf M Salt domainSample pk (.inl (.inl n))
      ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_progGameRunImplTape_unif_iff psf M Salt domainSample pk).1 hz ▸ h u

/-- One random-oracle query of the programmed tape handler, exactly; the tape is unchanged. -/
@[spec high]
theorem progGameRunImplTape_wp_read (mc : Salt × M)
    (post : (GSpec).Range (.inl (.inr mc)) → TState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v, (s.1 mc = some v ∨
        (s.1 mc = none ∧ ∃ sd ∈ support (domainSample pk), psf.eval pk sd = v)) →
        post v (s.1.cacheQuery mc v, s.2) ⦄
      progGameRunImplTape psf M Salt domainSample pk (.inl (.inr mc)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h v s' hz => by
    rcases (mem_support_progGameRunImplTape_read_iff psf M Salt domainSample pk).1 hz with
      ⟨hc, rfl⟩ | ⟨hc, hv, rfl⟩
    · simpa [QueryCache.cacheQuery_eq_self_of_eq_some hc] using h v (.inl hc)
    · exact h v (.inr ⟨hc, hv⟩)

/-- One programmed tape signing query, exactly: the head salt is consumed. -/
@[spec high]
theorem progGameRunImplTape_wp_sign (msg : M) (post : (GSpec).Range (.inr msg) → TState → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r sd, (s.2 = [] ∨ s.2.head? = some r) → sd ∈ support (domainSample pk) →
        post (r, sd) (s.1.cacheQuery (r, msg) (psf.eval pk sd), s.2.tail) ⦄
      progGameRunImplTape psf M Salt domainSample pk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h σ s' hz => by
    obtain ⟨hr, hs, rfl⟩ :=
      (mem_support_progGameRunImplTape_sign_iff psf M Salt domainSample pk).1 hz
    exact h σ.1 σ.2 hr hs

/-- The programmed tape handler never uncaches a key and only consumes its tape. -/
instance monotoneState_progGameRunImplTape :
    (progGameRunImplTape psf M Salt domainSample pk).MonotoneState
      fun s s' => (∀ t, (s.1 t).isSome → (s'.1 t).isSome) ∧ s'.2 <:+ s.2 where
  refl _ := ⟨fun _ => id, List.suffix_refl _⟩
  trans _ _ _ h₁ h₂ := ⟨fun t => h₂.1 t ∘ h₁.1 t, h₂.2.trans h₁.2⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with (n | mc) | msg
    · rw [(mem_support_progGameRunImplTape_unif_iff psf M Salt domainSample pk).1 hz]
      exact ⟨fun _ => id, List.suffix_refl _⟩
    · rcases (mem_support_progGameRunImplTape_read_iff psf M Salt domainSample pk).1 hz with
        ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      exacts [⟨fun _ => id, List.suffix_refl _⟩,
        ⟨fun _ => isSome_cacheQuery M Salt, List.suffix_refl _⟩]
    · obtain ⟨-, -, rfl⟩ :=
        (mem_support_progGameRunImplTape_sign_iff psf M Salt domainSample pk).1 hz
      exact ⟨fun _ => isSome_cacheQuery M Salt, List.tail_suffix _⟩

end progTape

end GPVHashAndSign
