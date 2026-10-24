/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.TrapCount
public import VCVio.ProgramLogic.Library

/-!
# Specifications for the GPV counting and index-embedding handlers

Specifications for the handlers of `VCVio.CryptoFoundations.GPVHashAndSign.TrapCount` under the
necessary reading (`open scoped OracleComp.Necessary`): the counter-augmented trap run
`progGameRunImplCombinedTrapCount`, the inline-fresh embedding handler `embedTrapFreshImpl`, and
the index-recording embedding handlers `embedTrapIdxImpl` and `embedTrapFreshIdxImpl`.

* *Support.* `mem_support_*_{unif,read,sign}_iff` (in `simulateQ_nf`): a hit keeps the state; a
  miss and a signing query write the cache (and the tables) at the queried point, record the
  current counter value in the index table and advance the counter.
* *One query.* `*_wp_{unif,read,sign}` (`spec high`) are exact and have one branch: a read
  quantifies over the reachable answer and final state, a signing query names its final state.
* *Whole runs* (`QueryImpl.MonotoneState`). The handlers only grow their sets of cached, recorded
  and indexed keys, their signed set and their counter, and never lower their flag; so an index
  recorded before an opaque adversary stays recorded, and the counter bounds stay valid.
-/

@[expose] public section

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary

namespace GPVHashAndSign

variable {PK SK Domain Range : Type} [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range) (M Salt : Type) [DecidableEq M]
  [DecidableEq Salt] [SampleableType Salt] (pk : PK) (sk : SK)

local notation "GSpec" => (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))
local notation "GCache" => OracleSpec.QueryCache (Salt × M →ₒ Range)
local notation "TCState" =>
  (((OracleSpec.QueryCache (Salt × M →ₒ Range) × Finset M) × Bool) ×
    ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)
local notation "IState" =>
  (OracleSpec.QueryCache (Salt × M →ₒ Range) × ℕ) × ((Salt × M) → Option ℕ)

/-- Run one unfolded handler step into its support. -/
local macro "run_support" : tactic => `(tactic| simp only [support_map, Set.mem_image,
  mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, support_uniformSample,
  Set.mem_univ, true_and, Prod.exists, Function.comp_apply])

omit [SampleableType Range] [SampleableType Salt] in
/-- Caching an answer never uncaches a key. -/
private theorem isSome_cacheQuery₃ {c : GCache} {t t' : Salt × M} {v : Range}
    (h : (c t).isSome) : ((c.cacheQuery t' v) t).isSome := by
  rcases eq_or_ne t t' with rfl | h' <;> simp_all

omit [SampleableType Salt] in
/-- Writing a table entry never removes one. -/
private theorem isSome_update₃ {τ : Type} {f : (Salt × M) → Option τ} {t q : Salt × M}
    {x : τ} (h : (f t).isSome) : ((fun t' => if t' = q then some x else f t') t).isSome := by
  dsimp only; split_ifs <;> simp_all

/-! ## The counter-augmented trap run `progGameRunImplCombinedTrapCount` -/

/-- A uniform query of the counting trap run keeps the state. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplCombinedTrapCount_unif_iff {n : ℕ} {s s' : TCState}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, s') ∈ support ((progGameRunImplCombinedTrapCount psf M Salt pk sk (.inl (.inl n))).run s) ↔
      s' = s := by
  rw [progGameRunImplCombinedTrapCount_run_inl_inl]; run_support; aesop

/-- A random-oracle query of the counting trap run is a hit, or a miss caching a uniform image `v`,
recording a trapdoor preimage of `v` and the current counter, and advancing the counter. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplCombinedTrapCount_read_iff {q : Salt × M} {s s' : TCState}
    {v : (GSpec).Range (.inl (.inr q))} :
    (v, s') ∈ support ((progGameRunImplCombinedTrapCount psf M Salt pk sk (.inl (.inr q))).run s) ↔
      (s.1.1.1.1 q = some v ∧ s' = s) ∨ (s.1.1.1.1 q = none ∧
        ∃ x ∈ support (psf.trapdoorSample pk sk v), s' = ((((s.1.1.1.1.cacheQuery q v,
          s.1.1.1.2), s.1.1.2), fun t' => if t' = q then some x else s.1.2 t'),
            ((fun t' => if t' = q then some s.2.2 else s.2.1 t'), s.2.2 + 1))) := by
  rw [progGameRunImplCombinedTrapCount_run_inl_inr]
  cases s.1.1.1.1 q <;> run_support <;> aesop

/-- A signing query of the counting trap run is a trap signing step that also records the current
counter at `(r, msg)` and advances it. -/
@[simulateQ_nf]
theorem mem_support_progGameRunImplCombinedTrapCount_sign_iff {msg : M} {s s' : TCState}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((progGameRunImplCombinedTrapCount psf M Salt pk sk (.inr msg)).run s) ↔
      ∃ v, σ.2 ∈ support (psf.trapdoorSample pk sk v) ∧
        s' = ((((s.1.1.1.1.cacheQuery (σ.1, msg) v, insert msg s.1.1.1.2),
          s.1.1.2 || saltKeyed M Salt s.1.1.1.1 σ.1),
            fun t' => if t' = (σ.1, msg) then some σ.2 else s.1.2 t'),
          ((fun t' => if t' = (σ.1, msg) then some s.2.2 else s.2.1 t'), s.2.2 + 1)) := by
  obtain ⟨r, x⟩ := σ
  rw [progGameRunImplCombinedTrapCount_run_inr]; run_support; aesop

/-- One uniform query of the counting trap run: any answer, the state unchanged. -/
@[spec high]
theorem progGameRunImplCombinedTrapCount_wp_unif (n : ℕ)
    (post : (GSpec).Range (.inl (.inl n)) → TCState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ u, post u s ⦄ progGameRunImplCombinedTrapCount psf M Salt pk sk (.inl (.inl n))
      ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_progGameRunImplCombinedTrapCount_unif_iff psf M Salt pk sk).1 hz ▸ h u

/-- One random-oracle query of the counting trap run, exactly. -/
@[spec high]
theorem progGameRunImplCombinedTrapCount_wp_read (q : Salt × M)
    (post : (GSpec).Range (.inl (.inr q)) → TCState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v s', ((s.1.1.1.1 q = some v ∧ s' = s) ∨ (s.1.1.1.1 q = none ∧
        ∃ x ∈ support (psf.trapdoorSample pk sk v), s' = ((((s.1.1.1.1.cacheQuery q v,
          s.1.1.1.2), s.1.1.2), fun t' => if t' = q then some x else s.1.2 t'),
            ((fun t' => if t' = q then some s.2.2 else s.2.1 t'), s.2.2 + 1)))) → post v s' ⦄
      progGameRunImplCombinedTrapCount psf M Salt pk sk (.inl (.inr q)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h v s' hz =>
    h v s' ((mem_support_progGameRunImplCombinedTrapCount_read_iff psf M Salt pk sk).1 hz)

/-- One signing query of the counting trap run, exactly. -/
@[spec high]
theorem progGameRunImplCombinedTrapCount_wp_sign (msg : M)
    (post : (GSpec).Range (.inr msg) → TCState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r v x, x ∈ support (psf.trapdoorSample pk sk v) → post (r, x)
        ((((s.1.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.1.2),
          s.1.1.2 || saltKeyed M Salt s.1.1.1.1 r), fun t' => if t' = (r, msg) then some x
            else s.1.2 t'),
          ((fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t'), s.2.2 + 1)) ⦄
      progGameRunImplCombinedTrapCount psf M Salt pk sk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h σ _ hz => by
    obtain ⟨v, hx, rfl⟩ :=
      (mem_support_progGameRunImplCombinedTrapCount_sign_iff psf M Salt pk sk).1 hz
    exact h σ.1 v σ.2 hx

/-- The counting trap run grows its cached, recorded and indexed keys, its signed set and its
counter, and never lowers its flag. -/
instance monotoneState_progGameRunImplCombinedTrapCount :
    (progGameRunImplCombinedTrapCount psf M Salt pk sk).MonotoneState
      fun s s' => ((∀ t, (s.1.1.1.1 t).isSome → (s'.1.1.1.1 t).isSome) ∧
        s.1.1.1.2 ⊆ s'.1.1.1.2 ∧ (s.1.1.2 = true → s'.1.1.2 = true)) ∧
        (∀ t, (s.1.2 t).isSome → (s'.1.2 t).isSome) ∧
        (∀ t, (s.2.1 t).isSome → (s'.2.1 t).isSome) ∧ s.2.2 ≤ s'.2.2 where
  refl _ := ⟨⟨fun _ => id, subset_rfl, id⟩, fun _ => id, fun _ => id, le_rfl⟩
  trans _ _ _ h₁ h₂ := ⟨⟨fun t => h₂.1.1 t ∘ h₁.1.1 t, h₁.1.2.1.trans h₂.1.2.1,
    h₂.1.2.2 ∘ h₁.1.2.2⟩, fun t => h₂.2.1 t ∘ h₁.2.1 t, fun t => h₂.2.2.1 t ∘ h₁.2.2.1 t,
    h₁.2.2.2.trans h₂.2.2.2⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with (n | q) | msg
    · rw [(mem_support_progGameRunImplCombinedTrapCount_unif_iff psf M Salt pk sk).1 hz]
      exact ⟨⟨fun _ => id, subset_rfl, id⟩, fun _ => id, fun _ => id, le_rfl⟩
    · rcases (mem_support_progGameRunImplCombinedTrapCount_read_iff psf M Salt pk sk).1 hz with
        ⟨-, rfl⟩ | ⟨-, x, -, rfl⟩
      · exact ⟨⟨fun _ => id, subset_rfl, id⟩, fun _ => id, fun _ => id, le_rfl⟩
      · exact ⟨⟨fun _ => isSome_cacheQuery₃ M Salt, subset_rfl, id⟩,
          fun _ => isSome_update₃ M Salt, fun _ => isSome_update₃ M Salt, Nat.le_succ _⟩
    · obtain ⟨v, -, rfl⟩ :=
        (mem_support_progGameRunImplCombinedTrapCount_sign_iff psf M Salt pk sk).1 hz
      exact ⟨⟨fun _ => isSome_cacheQuery₃ M Salt, Finset.subset_insert _ _, fun h => by simp [h]⟩,
        fun _ => isSome_update₃ M Salt, fun _ => isSome_update₃ M Salt, Nat.le_succ _⟩

/-! ## The index-recording embedding handler `embedTrapIdxImpl` -/

section idx

variable (j : ℕ) (y : Range)

/-- A uniform query of the index-recording embedding handler keeps the state. -/
@[simulateQ_nf]
theorem mem_support_embedTrapIdxImpl_unif_iff {n : ℕ} {s s' : IState}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, s') ∈ support ((embedTrapIdxImpl psf M Salt pk sk j y (.inl (.inl n))).run s) ↔
      s' = s := by
  rw [embedTrapIdxImpl_run_inl_inl]; run_support; aesop

/-- A random-oracle query of the index-recording embedding handler is a hit, or a miss caching a
uniform answer (the target `y` at the winner index `j`), recording the counter and advancing it. -/
@[simulateQ_nf]
theorem mem_support_embedTrapIdxImpl_read_iff {q : Salt × M} {s s' : IState}
    {v : (GSpec).Range (.inl (.inr q))} :
    (v, s') ∈ support ((embedTrapIdxImpl psf M Salt pk sk j y (.inl (.inr q))).run s) ↔
      (s.1.1 q = some v ∧ s' = s) ∨ (s.1.1 q = none ∧ (s.1.2 = j → v = y) ∧
        s' = ((s.1.1.cacheQuery q v, s.1.2 + 1), fun t' => if t' = q then some s.1.2
          else s.2 t')) := by
  rw [embedTrapIdxImpl_run_inl_inr]
  cases s.1.1 q <;> run_support <;> aesop

/-- A signing query of the index-recording embedding handler caches a uniform image `c` at
`(r, msg)`, returns a trapdoor preimage of `c`, records the counter and advances it. -/
@[simulateQ_nf]
theorem mem_support_embedTrapIdxImpl_sign_iff {msg : M} {s s' : IState}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((embedTrapIdxImpl psf M Salt pk sk j y (.inr msg)).run s) ↔
      ∃ c, σ.2 ∈ support (psf.trapdoorSample pk sk c) ∧
        s' = ((s.1.1.cacheQuery (σ.1, msg) c, s.1.2 + 1),
          fun t' => if t' = (σ.1, msg) then some s.1.2 else s.2 t') := by
  obtain ⟨r, x⟩ := σ
  rw [embedTrapIdxImpl_run_inr]; run_support; aesop

/-- One uniform query of the index-recording embedding handler: the state unchanged. -/
@[spec high]
theorem embedTrapIdxImpl_wp_unif (n : ℕ) (post : (GSpec).Range (.inl (.inl n)) → IState → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ u, post u s ⦄ embedTrapIdxImpl psf M Salt pk sk j y (.inl (.inl n))
      ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_embedTrapIdxImpl_unif_iff psf M Salt pk sk j y).1 hz ▸ h u

/-- One random-oracle query of the index-recording embedding handler, exactly. -/
@[spec high]
theorem embedTrapIdxImpl_wp_read (q : Salt × M)
    (post : (GSpec).Range (.inl (.inr q)) → IState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v s', ((s.1.1 q = some v ∧ s' = s) ∨ (s.1.1 q = none ∧ (s.1.2 = j → v = y) ∧
        s' = ((s.1.1.cacheQuery q v, s.1.2 + 1), fun t' => if t' = q then some s.1.2
          else s.2 t'))) → post v s' ⦄
      embedTrapIdxImpl psf M Salt pk sk j y (.inl (.inr q)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h v s' hz =>
    h v s' ((mem_support_embedTrapIdxImpl_read_iff psf M Salt pk sk j y).1 hz)

/-- One signing query of the index-recording embedding handler, exactly. -/
@[spec high]
theorem embedTrapIdxImpl_wp_sign (msg : M) (post : (GSpec).Range (.inr msg) → IState → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r c x, x ∈ support (psf.trapdoorSample pk sk c) → post (r, x)
        ((s.1.1.cacheQuery (r, msg) c, s.1.2 + 1),
          fun t' => if t' = (r, msg) then some s.1.2 else s.2 t') ⦄
      embedTrapIdxImpl psf M Salt pk sk j y (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h σ _ hz => by
    obtain ⟨c, hx, rfl⟩ := (mem_support_embedTrapIdxImpl_sign_iff psf M Salt pk sk j y).1 hz
    exact h σ.1 c σ.2 hx

/-- The index-recording embedding handler grows its cached and indexed keys and its counter. -/
instance monotoneState_embedTrapIdxImpl :
    (embedTrapIdxImpl psf M Salt pk sk j y).MonotoneState
      fun s s' => ((∀ t, (s.1.1 t).isSome → (s'.1.1 t).isSome) ∧ s.1.2 ≤ s'.1.2) ∧
        ∀ t, (s.2 t).isSome → (s'.2 t).isSome where
  refl _ := ⟨⟨fun _ => id, le_rfl⟩, fun _ => id⟩
  trans _ _ _ h₁ h₂ := ⟨⟨fun t => h₂.1.1 t ∘ h₁.1.1 t, h₁.1.2.trans h₂.1.2⟩,
    fun t => h₂.2 t ∘ h₁.2 t⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with (n | q) | msg
    · rw [(mem_support_embedTrapIdxImpl_unif_iff psf M Salt pk sk j y).1 hz]
      exact ⟨⟨fun _ => id, le_rfl⟩, fun _ => id⟩
    · rcases (mem_support_embedTrapIdxImpl_read_iff psf M Salt pk sk j y).1 hz with
        ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · exact ⟨⟨fun _ => id, le_rfl⟩, fun _ => id⟩
      · exact ⟨⟨fun _ => isSome_cacheQuery₃ M Salt, Nat.le_succ _⟩, fun _ => isSome_update₃ M Salt⟩
    · obtain ⟨c, -, rfl⟩ := (mem_support_embedTrapIdxImpl_sign_iff psf M Salt pk sk j y).1 hz
      exact ⟨⟨fun _ => isSome_cacheQuery₃ M Salt, Nat.le_succ _⟩, fun _ => isSome_update₃ M Salt⟩

end idx

/-! ## The inline-fresh embedding handlers `embedTrapFreshImpl` and `embedTrapFreshIdxImpl` -/

/-- A uniform query of the inline-fresh embedding handler keeps the state. -/
@[simulateQ_nf]
theorem mem_support_embedTrapFreshImpl_unif_iff {n : ℕ} {s s' : GCache × ℕ}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, s') ∈ support ((embedTrapFreshImpl psf M Salt pk sk (.inl (.inl n))).run s) ↔ s' = s := by
  rw [embedTrapFreshImpl_run_inl_inl]; run_support; aesop

/-- A random-oracle query of the inline-fresh embedding handler is a lazy random-oracle step that
advances the counter on a miss. -/
@[simulateQ_nf]
theorem mem_support_embedTrapFreshImpl_read_iff {q : Salt × M} {s s' : GCache × ℕ}
    {v : (GSpec).Range (.inl (.inr q))} :
    (v, s') ∈ support ((embedTrapFreshImpl psf M Salt pk sk (.inl (.inr q))).run s) ↔
      (s.1 q = some v ∧ s' = s) ∨ (s.1 q = none ∧ s' = (s.1.cacheQuery q v, s.2 + 1)) := by
  rw [embedTrapFreshImpl_run_inl_inr]
  cases s.1 q <;> run_support <;> aesop

/-- A signing query of the inline-fresh embedding handler is a trapdoor signing step. -/
@[simulateQ_nf]
theorem mem_support_embedTrapFreshImpl_sign_iff {msg : M} {s s' : GCache × ℕ}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((embedTrapFreshImpl psf M Salt pk sk (.inr msg)).run s) ↔
      ∃ c, σ.2 ∈ support (psf.trapdoorSample pk sk c) ∧
        s' = (s.1.cacheQuery (σ.1, msg) c, s.2 + 1) := by
  obtain ⟨r, x⟩ := σ
  rw [embedTrapFreshImpl_run_inr]; run_support; aesop

/-- One uniform query of the inline-fresh embedding handler: the state unchanged. -/
@[spec high]
theorem embedTrapFreshImpl_wp_unif (n : ℕ)
    (post : (GSpec).Range (.inl (.inl n)) → GCache × ℕ → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ u, post u s ⦄ embedTrapFreshImpl psf M Salt pk sk (.inl (.inl n))
      ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_embedTrapFreshImpl_unif_iff psf M Salt pk sk).1 hz ▸ h u

/-- One random-oracle query of the inline-fresh embedding handler, exactly. -/
@[spec high]
theorem embedTrapFreshImpl_wp_read (q : Salt × M)
    (post : (GSpec).Range (.inl (.inr q)) → GCache × ℕ → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v s', ((s.1 q = some v ∧ s' = s) ∨
        (s.1 q = none ∧ s' = (s.1.cacheQuery q v, s.2 + 1))) → post v s' ⦄
      embedTrapFreshImpl psf M Salt pk sk (.inl (.inr q)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h v s' hz =>
    h v s' ((mem_support_embedTrapFreshImpl_read_iff psf M Salt pk sk).1 hz)

/-- One signing query of the inline-fresh embedding handler, exactly. -/
@[spec high]
theorem embedTrapFreshImpl_wp_sign (msg : M) (post : (GSpec).Range (.inr msg) → GCache × ℕ → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r c x, x ∈ support (psf.trapdoorSample pk sk c) →
        post (r, x) (s.1.cacheQuery (r, msg) c, s.2 + 1) ⦄
      embedTrapFreshImpl psf M Salt pk sk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h σ _ hz => by
    obtain ⟨c, hx, rfl⟩ := (mem_support_embedTrapFreshImpl_sign_iff psf M Salt pk sk).1 hz
    exact h σ.1 c σ.2 hx

/-- The inline-fresh embedding handler never uncaches a key and its counter only grows. -/
instance monotoneState_embedTrapFreshImpl :
    (embedTrapFreshImpl psf M Salt pk sk).MonotoneState
      fun s s' => (∀ t, (s.1 t).isSome → (s'.1 t).isSome) ∧ s.2 ≤ s'.2 where
  refl _ := ⟨fun _ => id, le_rfl⟩
  trans _ _ _ h₁ h₂ := ⟨fun t => h₂.1 t ∘ h₁.1 t, h₁.2.trans h₂.2⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with (n | q) | msg
    · rw [(mem_support_embedTrapFreshImpl_unif_iff psf M Salt pk sk).1 hz]
      exact ⟨fun _ => id, le_rfl⟩
    · rcases (mem_support_embedTrapFreshImpl_read_iff psf M Salt pk sk).1 hz with
        ⟨-, rfl⟩ | ⟨-, rfl⟩
      exacts [⟨fun _ => id, le_rfl⟩, ⟨fun _ => isSome_cacheQuery₃ M Salt, Nat.le_succ _⟩]
    · obtain ⟨c, -, rfl⟩ := (mem_support_embedTrapFreshImpl_sign_iff psf M Salt pk sk).1 hz
      exact ⟨fun _ => isSome_cacheQuery₃ M Salt, Nat.le_succ _⟩

/-- A uniform query of the inline-fresh index-recording handler keeps the state. -/
@[simulateQ_nf]
theorem mem_support_embedTrapFreshIdxImpl_unif_iff {n : ℕ} {s s' : IState}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, s') ∈ support ((embedTrapFreshIdxImpl psf M Salt pk sk (.inl (.inl n))).run s) ↔
      s' = s := by
  rw [embedTrapFreshIdxImpl_run_inl_inl]; run_support; aesop

/-- One uniform query of the inline-fresh index-recording handler: the state unchanged. -/
@[spec high]
theorem embedTrapFreshIdxImpl_wp_unif (n : ℕ)
    (post : (GSpec).Range (.inl (.inl n)) → IState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ u, post u s ⦄ embedTrapFreshIdxImpl psf M Salt pk sk (.inl (.inl n))
      ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_embedTrapFreshIdxImpl_unif_iff psf M Salt pk sk).1 hz ▸ h u

/-- A random-oracle query of the inline-fresh index-recording handler is a lazy random-oracle step
that records the counter and advances it on a miss. -/
@[simulateQ_nf]
theorem mem_support_embedTrapFreshIdxImpl_read_iff {q : Salt × M} {s s' : IState}
    {v : (GSpec).Range (.inl (.inr q))} :
    (v, s') ∈ support ((embedTrapFreshIdxImpl psf M Salt pk sk (.inl (.inr q))).run s) ↔
      (s.1.1 q = some v ∧ s' = s) ∨ (s.1.1 q = none ∧ s' = ((s.1.1.cacheQuery q v, s.1.2 + 1),
        fun t' => if t' = q then some s.1.2 else s.2 t')) := by
  rw [embedTrapFreshIdxImpl_run_inl_inr]
  cases s.1.1 q <;> run_support <;> aesop

/-- A signing query of the inline-fresh index-recording handler is an index-recording trapdoor
signing step. -/
@[simulateQ_nf]
theorem mem_support_embedTrapFreshIdxImpl_sign_iff {msg : M} {s s' : IState}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((embedTrapFreshIdxImpl psf M Salt pk sk (.inr msg)).run s) ↔
      ∃ c, σ.2 ∈ support (psf.trapdoorSample pk sk c) ∧
        s' = ((s.1.1.cacheQuery (σ.1, msg) c, s.1.2 + 1),
          fun t' => if t' = (σ.1, msg) then some s.1.2 else s.2 t') := by
  obtain ⟨r, x⟩ := σ
  rw [embedTrapFreshIdxImpl_run_inr]; run_support; aesop

/-- One random-oracle query of the inline-fresh index-recording handler, exactly. -/
@[spec high]
theorem embedTrapFreshIdxImpl_wp_read (q : Salt × M)
    (post : (GSpec).Range (.inl (.inr q)) → IState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v s', ((s.1.1 q = some v ∧ s' = s) ∨ (s.1.1 q = none ∧
        s' = ((s.1.1.cacheQuery q v, s.1.2 + 1), fun t' => if t' = q then some s.1.2
          else s.2 t'))) → post v s' ⦄
      embedTrapFreshIdxImpl psf M Salt pk sk (.inl (.inr q)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h v s' hz =>
    h v s' ((mem_support_embedTrapFreshIdxImpl_read_iff psf M Salt pk sk).1 hz)

/-- One signing query of the inline-fresh index-recording handler, exactly. -/
@[spec high]
theorem embedTrapFreshIdxImpl_wp_sign (msg : M) (post : (GSpec).Range (.inr msg) → IState → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r c x, x ∈ support (psf.trapdoorSample pk sk c) → post (r, x)
        ((s.1.1.cacheQuery (r, msg) c, s.1.2 + 1),
          fun t' => if t' = (r, msg) then some s.1.2 else s.2 t') ⦄
      embedTrapFreshIdxImpl psf M Salt pk sk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h σ _ hz => by
    obtain ⟨c, hx, rfl⟩ := (mem_support_embedTrapFreshIdxImpl_sign_iff psf M Salt pk sk).1 hz
    exact h σ.1 c σ.2 hx

end GPVHashAndSign
