/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.CombinedHandler
public import VCVio.ProgramLogic.Library

/-!
# Specifications for the GPV combined and embedding handlers

Specifications for the handlers of `VCVio.CryptoFoundations.GPVHashAndSign.CombinedHandler` under
the necessary reading (`open scoped OracleComp.Necessary`): the trap-sibling embedding handler
`embedTrapImpl`, the combined handler `progGameRunImplCombined`, its trapdoor-recording sibling
`progGameRunImplCombinedTrap`, and the collision reduction's handler `reductionImpl`.

* *Support.* `mem_support_*_{unif,read,sign}_iff` (in `simulateQ_nf`) describe a reachable step by
  its answer and final state: a hit keeps the state, a miss and a signing query write the cache
  (and the hidden table, signed set, flag or counter) at the queried point.
* *One query.* `*_wp_{unif,read,sign}` (`spec high`) are exact and have one branch, which `vcgen`
  needs to continue: a read quantifies over the answer and final state reachable on a hit (state
  unchanged) or a miss (state written); a signing query names its final state.
* *Whole runs* (`QueryImpl.MonotoneState`). The handlers only grow their set of cached keys
  (signing overwrites), their counter, signed set and table keys, and never lower their flag.
-/

@[expose] public section

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary

namespace GPVHashAndSign

variable {PK SK Domain Range : Type} (psf : PreimageSampleableFunction PK SK Domain Range)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]

local notation "GSpec" => (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))
local notation "GCache" => OracleSpec.QueryCache (Salt × M →ₒ Range)
local notation "CState" =>
  ((OracleSpec.QueryCache (Salt × M →ₒ Range) × Finset M) × Bool) × ((Salt × M) → Option Domain)

/-- Run one unfolded handler step into its support. -/
local macro "run_support" : tactic => `(tactic| simp only [support_map, Set.mem_image,
  mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, support_uniformSample,
  Set.mem_univ, true_and, Prod.exists, Function.comp_apply])

omit [SampleableType Salt] in
/-- Caching an answer never uncaches a key. -/
private theorem isSome_cacheQuery'' {c : GCache} {t t' : Salt × M} {v : Range}
    (h : (c t).isSome) : ((c.cacheQuery t' v) t).isSome := by
  rcases eq_or_ne t t' with rfl | h' <;> simp_all

omit [SampleableType Salt] in
/-- Writing a table entry never removes one. -/
private theorem isSome_update_of_isSome {τ : Type} {f : (Salt × M) → Option τ} {t q : Salt × M}
    {x : τ} (h : (f t).isSome) : ((fun t' => if t' = q then some x else f t') t).isSome := by
  dsimp only; split_ifs <;> simp_all

/-! ## The trap-sibling embedding handler `embedTrapImpl` -/

section embedTrap

variable [SampleableType Range] (pk : PK) (sk : SK) (w : ℕ) (y : Range)

/-- A uniform query of the embedding handler keeps the state. -/
@[simulateQ_nf]
theorem mem_support_embedTrapImpl_unif_iff {n : ℕ} {s s' : GCache × ℕ}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, s') ∈ support ((embedTrapImpl psf M Salt pk sk w y (.inl (.inl n))).run s) ↔ s' = s := by
  rw [embedTrapImpl_run_inl_inl]; run_support; aesop

/-- A random-oracle query of the embedding handler is a hit, or a miss caching a uniform answer,
or the target `y` at the winner index `w`, and advancing the counter. -/
@[simulateQ_nf]
theorem mem_support_embedTrapImpl_read_iff {q : Salt × M} {s s' : GCache × ℕ}
    {v : (GSpec).Range (.inl (.inr q))} :
    (v, s') ∈ support ((embedTrapImpl psf M Salt pk sk w y (.inl (.inr q))).run s) ↔
      (s.1 q = some v ∧ s' = s) ∨
        (s.1 q = none ∧ (s.2 = w → v = y) ∧ s' = (s.1.cacheQuery q v, s.2 + 1)) := by
  rw [embedTrapImpl_run_inl_inr]
  cases s.1 q <;> run_support <;> aesop

/-- A signing query of the embedding handler caches a uniform image `c` at `(r, msg)`, returns a
trapdoor preimage of `c` and advances the counter. -/
@[simulateQ_nf]
theorem mem_support_embedTrapImpl_sign_iff {msg : M} {s s' : GCache × ℕ}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((embedTrapImpl psf M Salt pk sk w y (.inr msg)).run s) ↔
      ∃ c, σ.2 ∈ support (psf.trapdoorSample pk sk c) ∧
        s' = (s.1.cacheQuery (σ.1, msg) c, s.2 + 1) := by
  obtain ⟨r, x⟩ := σ
  rw [embedTrapImpl_run_inr]; run_support; aesop

/-- One uniform query of the embedding handler: any answer, the state unchanged. -/
@[spec high]
theorem embedTrapImpl_wp_unif (n : ℕ) (post : (GSpec).Range (.inl (.inl n)) → GCache × ℕ → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ u, post u s ⦄ embedTrapImpl psf M Salt pk sk w y (.inl (.inl n))
      ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_embedTrapImpl_unif_iff psf M Salt pk sk w y).1 hz ▸ h u

/-- One random-oracle query of the embedding handler, exactly: a hit keeps the state, a miss
caches its answer (`y` at the winner index) and advances the counter. -/
@[spec high]
theorem embedTrapImpl_wp_read (q : Salt × M)
    (post : (GSpec).Range (.inl (.inr q)) → GCache × ℕ → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v s', ((s.1 q = some v ∧ s' = s) ∨
        (s.1 q = none ∧ (s.2 = w → v = y) ∧ s' = (s.1.cacheQuery q v, s.2 + 1))) → post v s' ⦄
      embedTrapImpl psf M Salt pk sk w y (.inl (.inr q)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h v s' hz =>
    h v s' ((mem_support_embedTrapImpl_read_iff psf M Salt pk sk w y).1 hz)

/-- One signing query of the embedding handler, exactly. -/
@[spec high]
theorem embedTrapImpl_wp_sign (msg : M) (post : (GSpec).Range (.inr msg) → GCache × ℕ → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r c x, x ∈ support (psf.trapdoorSample pk sk c) →
        post (r, x) (s.1.cacheQuery (r, msg) c, s.2 + 1) ⦄
      embedTrapImpl psf M Salt pk sk w y (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h σ s' hz => by
    obtain ⟨c, hx, rfl⟩ := (mem_support_embedTrapImpl_sign_iff psf M Salt pk sk w y).1 hz
    exact h σ.1 c σ.2 hx

/-- The embedding handler never uncaches a key and its counter only grows. -/
instance monotoneState_embedTrapImpl :
    (embedTrapImpl psf M Salt pk sk w y).MonotoneState
      fun s s' => (∀ t, (s.1 t).isSome → (s'.1 t).isSome) ∧ s.2 ≤ s'.2 where
  refl _ := ⟨fun _ => id, le_rfl⟩
  trans _ _ _ h₁ h₂ := ⟨fun t => h₂.1 t ∘ h₁.1 t, h₁.2.trans h₂.2⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with (n | q) | msg
    · rw [(mem_support_embedTrapImpl_unif_iff psf M Salt pk sk w y).1 hz]
      exact ⟨fun _ => id, le_rfl⟩
    · rcases (mem_support_embedTrapImpl_read_iff psf M Salt pk sk w y).1 hz with
        ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      exacts [⟨fun _ => id, le_rfl⟩, ⟨fun _ => isSome_cacheQuery'' M Salt, Nat.le_succ _⟩]
    · obtain ⟨c, -, rfl⟩ := (mem_support_embedTrapImpl_sign_iff psf M Salt pk sk w y).1 hz
      exact ⟨fun _ => isSome_cacheQuery'' M Salt, Nat.le_succ _⟩

end embedTrap

/-! ## The combined handler `progGameRunImplCombined` -/

section combined

variable (domainSample : PK → ProbComp Domain) (pk : PK)

/-- A uniform query of the combined handler keeps the state. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplCombined_unif_iff {n : ℕ} {s s' : CState}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, s') ∈ support ((progGameRunImplCombined psf M Salt domainSample pk (.inl (.inl n))).run s) ↔
      s' = s := by
  rw [progGameRunImplCombined_run_inl_inl]; run_support; aesop

/-- A random-oracle query of the combined handler is a hit, or a miss programming the image of a
forward sample `sd` and recording `sd` in the hidden table. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplCombined_read_iff {q : Salt × M} {s s' : CState}
    {v : (GSpec).Range (.inl (.inr q))} :
    (v, s') ∈ support ((progGameRunImplCombined psf M Salt domainSample pk (.inl (.inr q))).run s) ↔
      (s.1.1.1 q = some v ∧ s' = s) ∨ (s.1.1.1 q = none ∧ ∃ sd ∈ support (domainSample pk),
        v = psf.eval pk sd ∧ s' = (((s.1.1.1.cacheQuery q v, s.1.1.2), s.1.2),
          fun t' => if t' = q then some sd else s.2 t')) := by
  rw [progGameRunImplCombined_run_inl_inr]
  cases s.1.1.1 q <;> run_support <;> aesop

/-- A signing query of the combined handler programs `(r, msg)` to the image of a forward sample
`sd`, records `sd`, signs the message and or-s the flag with `saltKeyed`. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplCombined_sign_iff {msg : M} {s s' : CState}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((progGameRunImplCombined psf M Salt domainSample pk (.inr msg)).run s) ↔
      σ.2 ∈ support (domainSample pk) ∧
        s' = (((s.1.1.1.cacheQuery (σ.1, msg) (psf.eval pk σ.2), insert msg s.1.1.2),
          s.1.2 || saltKeyed M Salt s.1.1.1 σ.1), fun t' => if t' = (σ.1, msg) then some σ.2
            else s.2 t') := by
  obtain ⟨r, sd⟩ := σ
  rw [progGameRunImplCombined_run_inr]; run_support; aesop

/-- One uniform query of the combined handler: any answer, the state unchanged. -/
@[spec high]
theorem progGameRunImplCombined_wp_unif (n : ℕ)
    (post : (GSpec).Range (.inl (.inl n)) → CState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ u, post u s ⦄ progGameRunImplCombined psf M Salt domainSample pk (.inl (.inl n))
      ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_progGameRunImplCombined_unif_iff psf M Salt domainSample pk).1 hz ▸ h u

/-- One random-oracle query of the combined handler, exactly: a hit keeps the state, a miss
programs the cache and records the forward sample. -/
@[spec high]
theorem progGameRunImplCombined_wp_read (q : Salt × M)
    (post : (GSpec).Range (.inl (.inr q)) → CState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v s', ((s.1.1.1 q = some v ∧ s' = s) ∨ (s.1.1.1 q = none ∧
        ∃ sd ∈ support (domainSample pk), v = psf.eval pk sd ∧
          s' = (((s.1.1.1.cacheQuery q v, s.1.1.2), s.1.2),
            fun t' => if t' = q then some sd else s.2 t'))) → post v s' ⦄
      progGameRunImplCombined psf M Salt domainSample pk (.inl (.inr q)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h v s' hz =>
    h v s' ((mem_support_progGameRunImplCombined_read_iff psf M Salt domainSample pk).1 hz)

/-- One signing query of the combined handler, exactly. -/
@[spec high]
theorem progGameRunImplCombined_wp_sign (msg : M) (post : (GSpec).Range (.inr msg) → CState → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r sd, sd ∈ support (domainSample pk) → post (r, sd)
        (((s.1.1.1.cacheQuery (r, msg) (psf.eval pk sd), insert msg s.1.1.2),
          s.1.2 || saltKeyed M Salt s.1.1.1 r), fun t' => if t' = (r, msg) then some sd
            else s.2 t') ⦄
      progGameRunImplCombined psf M Salt domainSample pk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h σ s' hz => by
    obtain ⟨hs, rfl⟩ :=
      (mem_support_progGameRunImplCombined_sign_iff psf M Salt domainSample pk).1 hz
    exact h σ.1 σ.2 hs

/-- The combined handler never uncaches a key or a table entry, grows its signed set and never
lowers its flag. -/
instance monotoneState_progGameRunImplCombined :
    (progGameRunImplCombined psf M Salt domainSample pk).MonotoneState
      fun s s' => ((∀ t, (s.1.1.1 t).isSome → (s'.1.1.1 t).isSome) ∧ s.1.1.2 ⊆ s'.1.1.2) ∧
        (s.1.2 = true → s'.1.2 = true) ∧ ∀ t, (s.2 t).isSome → (s'.2 t).isSome where
  refl _ := ⟨⟨fun _ => id, subset_rfl⟩, id, fun _ => id⟩
  trans _ _ _ h₁ h₂ := ⟨⟨fun t => h₂.1.1 t ∘ h₁.1.1 t, h₁.1.2.trans h₂.1.2⟩, h₂.2.1 ∘ h₁.2.1,
    fun t => h₂.2.2 t ∘ h₁.2.2 t⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with (n | q) | msg
    · rw [(mem_support_progGameRunImplCombined_unif_iff psf M Salt domainSample pk).1 hz]
      exact ⟨⟨fun _ => id, subset_rfl⟩, id, fun _ => id⟩
    · rcases (mem_support_progGameRunImplCombined_read_iff psf M Salt domainSample pk).1 hz with
        ⟨-, rfl⟩ | ⟨-, sd, -, rfl, rfl⟩
      · exact ⟨⟨fun _ => id, subset_rfl⟩, id, fun _ => id⟩
      · exact ⟨⟨fun _ => isSome_cacheQuery'' M Salt, subset_rfl⟩, id,
          fun _ => isSome_update_of_isSome M Salt⟩
    · obtain ⟨-, rfl⟩ :=
        (mem_support_progGameRunImplCombined_sign_iff psf M Salt domainSample pk).1 hz
      exact ⟨⟨fun _ => isSome_cacheQuery'' M Salt, Finset.subset_insert _ _⟩,
        fun h => by simp [h], fun _ => isSome_update_of_isSome M Salt⟩

end combined

/-! ## The trapdoor-recording combined handler `progGameRunImplCombinedTrap` -/

section combinedTrap

variable [SampleableType Range] (pk : PK) (sk : SK)

/-- A uniform query of the trapdoor-recording handler keeps the state. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplCombinedTrap_unif_iff {n : ℕ} {s s' : CState}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, s') ∈ support ((progGameRunImplCombinedTrap psf M Salt pk sk (.inl (.inl n))).run s) ↔
      s' = s := by
  rw [progGameRunImplCombinedTrap_run_inl_inl]; run_support; aesop

/-- A random-oracle query of the trapdoor-recording handler is a hit, or a miss caching a uniform
image `v` and recording a trapdoor preimage of `v` in the hidden table. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplCombinedTrap_read_iff {q : Salt × M} {s s' : CState}
    {v : (GSpec).Range (.inl (.inr q))} :
    (v, s') ∈ support ((progGameRunImplCombinedTrap psf M Salt pk sk (.inl (.inr q))).run s) ↔
      (s.1.1.1 q = some v ∧ s' = s) ∨ (s.1.1.1 q = none ∧
        ∃ x ∈ support (psf.trapdoorSample pk sk v), s' = (((s.1.1.1.cacheQuery q v, s.1.1.2),
          s.1.2), fun t' => if t' = q then some x else s.2 t')) := by
  rw [progGameRunImplCombinedTrap_run_inl_inr]
  cases s.1.1.1 q <;> run_support <;> aesop

/-- A signing query of the trapdoor-recording handler caches a uniform image `v` at `(r, msg)`,
returns and records a trapdoor preimage of `v`, signs the message and or-s the flag. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplCombinedTrap_sign_iff {msg : M} {s s' : CState}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((progGameRunImplCombinedTrap psf M Salt pk sk (.inr msg)).run s) ↔
      ∃ v, σ.2 ∈ support (psf.trapdoorSample pk sk v) ∧
        s' = (((s.1.1.1.cacheQuery (σ.1, msg) v, insert msg s.1.1.2),
          s.1.2 || saltKeyed M Salt s.1.1.1 σ.1), fun t' => if t' = (σ.1, msg) then some σ.2
            else s.2 t') := by
  obtain ⟨r, x⟩ := σ
  rw [progGameRunImplCombinedTrap_run_inr]; run_support; aesop

/-- One uniform query of the trapdoor-recording handler: any answer, the state unchanged. -/
@[spec high]
theorem progGameRunImplCombinedTrap_wp_unif (n : ℕ)
    (post : (GSpec).Range (.inl (.inl n)) → CState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ u, post u s ⦄ progGameRunImplCombinedTrap psf M Salt pk sk (.inl (.inl n))
      ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_progGameRunImplCombinedTrap_unif_iff psf M Salt pk sk).1 hz ▸ h u

/-- One random-oracle query of the trapdoor-recording handler, exactly. -/
@[spec high]
theorem progGameRunImplCombinedTrap_wp_read (q : Salt × M)
    (post : (GSpec).Range (.inl (.inr q)) → CState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v s', ((s.1.1.1 q = some v ∧ s' = s) ∨ (s.1.1.1 q = none ∧
        ∃ x ∈ support (psf.trapdoorSample pk sk v), s' = (((s.1.1.1.cacheQuery q v, s.1.1.2),
          s.1.2), fun t' => if t' = q then some x else s.2 t'))) → post v s' ⦄
      progGameRunImplCombinedTrap psf M Salt pk sk (.inl (.inr q)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h v s' hz =>
    h v s' ((mem_support_progGameRunImplCombinedTrap_read_iff psf M Salt pk sk).1 hz)

/-- One signing query of the trapdoor-recording handler, exactly. -/
@[spec high]
theorem progGameRunImplCombinedTrap_wp_sign (msg : M)
    (post : (GSpec).Range (.inr msg) → CState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r v x, x ∈ support (psf.trapdoorSample pk sk v) → post (r, x)
        (((s.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.2),
          s.1.2 || saltKeyed M Salt s.1.1.1 r), fun t' => if t' = (r, msg) then some x
            else s.2 t') ⦄
      progGameRunImplCombinedTrap psf M Salt pk sk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h σ s' hz => by
    obtain ⟨v, hx, rfl⟩ :=
      (mem_support_progGameRunImplCombinedTrap_sign_iff psf M Salt pk sk).1 hz
    exact h σ.1 v σ.2 hx

/-- The trapdoor-recording handler grows like the combined handler. -/
instance monotoneState_progGameRunImplCombinedTrap :
    (progGameRunImplCombinedTrap psf M Salt pk sk).MonotoneState
      fun s s' => ((∀ t, (s.1.1.1 t).isSome → (s'.1.1.1 t).isSome) ∧ s.1.1.2 ⊆ s'.1.1.2) ∧
        (s.1.2 = true → s'.1.2 = true) ∧ ∀ t, (s.2 t).isSome → (s'.2 t).isSome where
  refl _ := ⟨⟨fun _ => id, subset_rfl⟩, id, fun _ => id⟩
  trans _ _ _ h₁ h₂ := ⟨⟨fun t => h₂.1.1 t ∘ h₁.1.1 t, h₁.1.2.trans h₂.1.2⟩, h₂.2.1 ∘ h₁.2.1,
    fun t => h₂.2.2 t ∘ h₁.2.2 t⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with (n | q) | msg
    · rw [(mem_support_progGameRunImplCombinedTrap_unif_iff psf M Salt pk sk).1 hz]
      exact ⟨⟨fun _ => id, subset_rfl⟩, id, fun _ => id⟩
    · rcases (mem_support_progGameRunImplCombinedTrap_read_iff psf M Salt pk sk).1 hz with
        ⟨-, rfl⟩ | ⟨-, x, -, rfl⟩
      · exact ⟨⟨fun _ => id, subset_rfl⟩, id, fun _ => id⟩
      · exact ⟨⟨fun _ => isSome_cacheQuery'' M Salt, subset_rfl⟩, id,
          fun _ => isSome_update_of_isSome M Salt⟩
    · obtain ⟨v, -, rfl⟩ :=
        (mem_support_progGameRunImplCombinedTrap_sign_iff psf M Salt pk sk).1 hz
      exact ⟨⟨fun _ => isSome_cacheQuery'' M Salt, Finset.subset_insert _ _⟩,
        fun h => by simp [h], fun _ => isSome_update_of_isSome M Salt⟩

end combinedTrap

section reduction

variable (domainSample : PK → ProbComp Domain) (pk : PK)

local notation "RState" => GCache × ((Salt × M) → Option Domain)

/-- A random-oracle query of the reduction is a hit, or a miss programming the image of a forward
sample `sd` and recording `sd`. -/
@[simulateQ_nf]
theorem mem_support_reductionImpl_read_iff {q : Salt × M} {s s' : RState}
    {v : (GSpec).Range (.inl (.inr q))} :
    (v, s') ∈ support ((reductionImpl psf M Salt domainSample pk (.inl (.inr q))).run s) ↔
      (s.1 q = some v ∧ s' = s) ∨ (s.1 q = none ∧ ∃ sd ∈ support (domainSample pk),
        v = psf.eval pk sd ∧ s' = (s.1.cacheQuery q v, fun t' => if t' = q then some sd
          else s.2 t')) := by
  rw [reductionImpl_run_inl_inr]
  cases s.1 q <;> run_support <;> aesop

/-- A signing query of the reduction programs `(r, msg)` to the image of a forward sample `sd` and
records `sd`. -/
@[simulateQ_nf]
theorem mem_support_reductionImpl_sign_iff {msg : M} {s s' : RState}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((reductionImpl psf M Salt domainSample pk (.inr msg)).run s) ↔
      σ.2 ∈ support (domainSample pk) ∧ s' = (s.1.cacheQuery (σ.1, msg) (psf.eval pk σ.2),
        fun t' => if t' = (σ.1, msg) then some σ.2 else s.2 t') := by
  obtain ⟨r, sd⟩ := σ
  rw [reductionImpl_run_inr]; run_support; aesop

/-- The reduction never uncaches a key or a table entry. -/
instance monotoneState_reductionImpl :
    (reductionImpl psf M Salt domainSample pk).MonotoneState
      fun s s' => (∀ t, (s.1 t).isSome → (s'.1 t).isSome) ∧
        ∀ t, (s.2 t).isSome → (s'.2 t).isSome where
  refl _ := ⟨fun _ => id, fun _ => id⟩
  trans _ _ _ h₁ h₂ := ⟨fun t => h₂.1 t ∘ h₁.1 t, fun t => h₂.2 t ∘ h₁.2 t⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with (n | q) | msg
    · simp only [reductionImpl_run_inl_inl, support_map, Set.mem_image, Prod.mk.injEq] at hz
      obtain ⟨_, -, -, rfl⟩ := hz
      exact ⟨fun _ => id, fun _ => id⟩
    · rcases (mem_support_reductionImpl_read_iff psf M Salt domainSample pk).1 hz with
        ⟨-, rfl⟩ | ⟨-, sd, -, rfl, rfl⟩
      · exact ⟨fun _ => id, fun _ => id⟩
      · exact ⟨fun _ => isSome_cacheQuery'' M Salt, fun _ => isSome_update_of_isSome M Salt⟩
    · obtain ⟨-, rfl⟩ := (mem_support_reductionImpl_sign_iff psf M Salt domainSample pk).1 hz
      exact ⟨fun _ => isSome_cacheQuery'' M Salt, fun _ => isSome_update_of_isSome M Salt⟩

end reduction

end GPVHashAndSign
