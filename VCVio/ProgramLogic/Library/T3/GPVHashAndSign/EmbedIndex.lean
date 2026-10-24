/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.EmbedIndex
public import VCVio.ProgramLogic.Library

/-!
# Specifications for the GPV signed-set index-embedding handlers

Specifications for the handlers of `VCVio.CryptoFoundations.GPVHashAndSign.EmbedIndex` under the
necessary reading (`open scoped OracleComp.Necessary`): `embedTrapIdxSigImpl` and
`embedTrapFreshIdxSigImpl`, the index-recording embedding handlers with a passive signed set.

* *Support.* `mem_support_*_{unif,read,sign}_iff` (in `simulateQ_nf`): a hit keeps the state; a
  miss caches a uniform answer (the target `y` at the winner index of `embedTrapIdxSigImpl`),
  records the counter and advances it; a signing query also inserts the message.
* *One query.* `*_wp_{unif,read,sign}` (`spec high`) are exact and have one branch.
* *Whole runs* (`QueryImpl.MonotoneState`). Both handlers grow their cached and indexed keys,
  their counter and their signed set.
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
local notation "SState" =>
  ((OracleSpec.QueryCache (Salt × M →ₒ Range) × ℕ) × ((Salt × M) → Option ℕ)) × Finset M

/-- Run one unfolded handler step into its support. -/
local macro "run_support" : tactic => `(tactic| simp only [support_map, Set.mem_image,
  mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, support_uniformSample,
  Set.mem_univ, true_and, Prod.exists, Function.comp_apply])

omit [SampleableType Range] [SampleableType Salt] in
/-- Caching an answer never uncaches a key. -/
private theorem isSome_cacheQuery₄ {c : GCache} {t t' : Salt × M} {v : Range}
    (h : (c t).isSome) : ((c.cacheQuery t' v) t).isSome := by
  rcases eq_or_ne t t' with rfl | h' <;> simp_all

omit [SampleableType Salt] in
/-- Writing an index entry never removes one. -/
private theorem isSome_update₄ {f : (Salt × M) → Option ℕ} {t q : Salt × M} {x : ℕ}
    (h : (f t).isSome) : ((fun t' => if t' = q then some x else f t') t).isSome := by
  dsimp only; split_ifs <;> simp_all

section idxSig

variable (j : ℕ) (y : Range)

/-- A uniform query of the signed-set index-embedding handler keeps the state. -/
@[simulateQ_nf]
theorem mem_support_embedTrapIdxSigImpl_unif_iff {n : ℕ} {s s' : SState}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, s') ∈ support ((embedTrapIdxSigImpl psf M Salt pk sk j y (.inl (.inl n))).run s) ↔
      s' = s := by
  rw [embedTrapIdxSigImpl_run_inl_inl]; run_support; aesop

/-- A random-oracle query of the signed-set index-embedding handler is a hit, or a miss caching a
uniform answer (`y` at the winner index `j`), recording the counter and advancing it. -/
@[simulateQ_nf]
theorem mem_support_embedTrapIdxSigImpl_read_iff {q : Salt × M} {s s' : SState}
    {v : (GSpec).Range (.inl (.inr q))} :
    (v, s') ∈ support ((embedTrapIdxSigImpl psf M Salt pk sk j y (.inl (.inr q))).run s) ↔
      (s.1.1.1 q = some v ∧ s' = s) ∨ (s.1.1.1 q = none ∧ (s.1.1.2 = j → v = y) ∧
        s' = (((s.1.1.1.cacheQuery q v, s.1.1.2 + 1),
          fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2)) := by
  rw [embedTrapIdxSigImpl_run_inl_inr]
  cases s.1.1.1 q <;> run_support <;> aesop

/-- A signing query of the signed-set index-embedding handler caches a uniform image `c` at
`(r, msg)`, returns a trapdoor preimage of `c`, records the counter and signs the message. -/
@[simulateQ_nf]
theorem mem_support_embedTrapIdxSigImpl_sign_iff {msg : M} {s s' : SState}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((embedTrapIdxSigImpl psf M Salt pk sk j y (.inr msg)).run s) ↔
      ∃ c, σ.2 ∈ support (psf.trapdoorSample pk sk c) ∧
        s' = (((s.1.1.1.cacheQuery (σ.1, msg) c, s.1.1.2 + 1),
          fun t' => if t' = (σ.1, msg) then some s.1.1.2 else s.1.2 t'), insert msg s.2) := by
  obtain ⟨r, x⟩ := σ
  rw [embedTrapIdxSigImpl_run_inr]; run_support; aesop

/-- One uniform query of the signed-set index-embedding handler: the state unchanged. -/
@[spec high]
theorem embedTrapIdxSigImpl_wp_unif (n : ℕ)
    (post : (GSpec).Range (.inl (.inl n)) → SState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ u, post u s ⦄ embedTrapIdxSigImpl psf M Salt pk sk j y (.inl (.inl n))
      ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_embedTrapIdxSigImpl_unif_iff psf M Salt pk sk j y).1 hz ▸ h u

/-- One random-oracle query of the signed-set index-embedding handler, exactly. -/
@[spec high]
theorem embedTrapIdxSigImpl_wp_read (q : Salt × M)
    (post : (GSpec).Range (.inl (.inr q)) → SState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v s', ((s.1.1.1 q = some v ∧ s' = s) ∨ (s.1.1.1 q = none ∧
        (s.1.1.2 = j → v = y) ∧ s' = (((s.1.1.1.cacheQuery q v, s.1.1.2 + 1),
          fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2))) → post v s' ⦄
      embedTrapIdxSigImpl psf M Salt pk sk j y (.inl (.inr q)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h v s' hz =>
    h v s' ((mem_support_embedTrapIdxSigImpl_read_iff psf M Salt pk sk j y).1 hz)

/-- One signing query of the signed-set index-embedding handler, exactly. -/
@[spec high]
theorem embedTrapIdxSigImpl_wp_sign (msg : M) (post : (GSpec).Range (.inr msg) → SState → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r c x, x ∈ support (psf.trapdoorSample pk sk c) → post (r, x)
        (((s.1.1.1.cacheQuery (r, msg) c, s.1.1.2 + 1),
          fun t' => if t' = (r, msg) then some s.1.1.2 else s.1.2 t'), insert msg s.2) ⦄
      embedTrapIdxSigImpl psf M Salt pk sk j y (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h σ _ hz => by
    obtain ⟨c, hx, rfl⟩ := (mem_support_embedTrapIdxSigImpl_sign_iff psf M Salt pk sk j y).1 hz
    exact h σ.1 c σ.2 hx

/-- The signed-set index-embedding handler grows its cached and indexed keys, its counter and its
signed set. -/
instance monotoneState_embedTrapIdxSigImpl :
    (embedTrapIdxSigImpl psf M Salt pk sk j y).MonotoneState
      fun s s' => ((∀ t, (s.1.1.1 t).isSome → (s'.1.1.1 t).isSome) ∧ s.1.1.2 ≤ s'.1.1.2) ∧
        (∀ t, (s.1.2 t).isSome → (s'.1.2 t).isSome) ∧ s.2 ⊆ s'.2 where
  refl _ := ⟨⟨fun _ => id, le_rfl⟩, fun _ => id, subset_rfl⟩
  trans _ _ _ h₁ h₂ := ⟨⟨fun t => h₂.1.1 t ∘ h₁.1.1 t, h₁.1.2.trans h₂.1.2⟩,
    fun t => h₂.2.1 t ∘ h₁.2.1 t, h₁.2.2.trans h₂.2.2⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with (n | q) | msg
    · rw [(mem_support_embedTrapIdxSigImpl_unif_iff psf M Salt pk sk j y).1 hz]
      exact ⟨⟨fun _ => id, le_rfl⟩, fun _ => id, subset_rfl⟩
    · rcases (mem_support_embedTrapIdxSigImpl_read_iff psf M Salt pk sk j y).1 hz with
        ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · exact ⟨⟨fun _ => id, le_rfl⟩, fun _ => id, subset_rfl⟩
      · exact ⟨⟨fun _ => isSome_cacheQuery₄ M Salt, Nat.le_succ _⟩, fun _ => isSome_update₄ M Salt,
          subset_rfl⟩
    · obtain ⟨c, -, rfl⟩ := (mem_support_embedTrapIdxSigImpl_sign_iff psf M Salt pk sk j y).1 hz
      exact ⟨⟨fun _ => isSome_cacheQuery₄ M Salt, Nat.le_succ _⟩, fun _ => isSome_update₄ M Salt,
        Finset.subset_insert _ _⟩

end idxSig

/-- A uniform query of the inline-fresh signed-set handler keeps the state. -/
@[simulateQ_nf]
theorem mem_support_embedTrapFreshIdxSigImpl_unif_iff {n : ℕ} {s s' : SState}
    {u : (GSpec).Range (.inl (.inl n))} :
    (u, s') ∈ support ((embedTrapFreshIdxSigImpl psf M Salt pk sk (.inl (.inl n))).run s) ↔
      s' = s := by
  rw [embedTrapFreshIdxSigImpl_run_inl_inl]; run_support; aesop

/-- A random-oracle query of the inline-fresh signed-set handler is a lazy random-oracle step that
records the counter and advances it on a miss. -/
@[simulateQ_nf]
theorem mem_support_embedTrapFreshIdxSigImpl_read_iff {q : Salt × M} {s s' : SState}
    {v : (GSpec).Range (.inl (.inr q))} :
    (v, s') ∈ support ((embedTrapFreshIdxSigImpl psf M Salt pk sk (.inl (.inr q))).run s) ↔
      (s.1.1.1 q = some v ∧ s' = s) ∨ (s.1.1.1 q = none ∧ s' = (((s.1.1.1.cacheQuery q v,
        s.1.1.2 + 1), fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2)) := by
  rw [embedTrapFreshIdxSigImpl_run_inl_inr]
  cases s.1.1.1 q <;> run_support <;> aesop

/-- A signing query of the inline-fresh signed-set handler is an index-recording trapdoor signing
step inserting the message. -/
@[simulateQ_nf]
theorem mem_support_embedTrapFreshIdxSigImpl_sign_iff {msg : M} {s s' : SState}
    {σ : (GSpec).Range (.inr msg)} :
    (σ, s') ∈ support ((embedTrapFreshIdxSigImpl psf M Salt pk sk (.inr msg)).run s) ↔
      ∃ c, σ.2 ∈ support (psf.trapdoorSample pk sk c) ∧
        s' = (((s.1.1.1.cacheQuery (σ.1, msg) c, s.1.1.2 + 1),
          fun t' => if t' = (σ.1, msg) then some s.1.1.2 else s.1.2 t'), insert msg s.2) := by
  obtain ⟨r, x⟩ := σ
  rw [embedTrapFreshIdxSigImpl_run_inr]; run_support; aesop

/-- One uniform query of the inline-fresh signed-set handler: the state unchanged. -/
@[spec high]
theorem embedTrapFreshIdxSigImpl_wp_unif (n : ℕ)
    (post : (GSpec).Range (.inl (.inl n)) → SState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ u, post u s ⦄ embedTrapFreshIdxSigImpl psf M Salt pk sk (.inl (.inl n))
      ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_embedTrapFreshIdxSigImpl_unif_iff psf M Salt pk sk).1 hz ▸ h u

/-- One random-oracle query of the inline-fresh signed-set handler, exactly. -/
@[spec high]
theorem embedTrapFreshIdxSigImpl_wp_read (q : Salt × M)
    (post : (GSpec).Range (.inl (.inr q)) → SState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v s', ((s.1.1.1 q = some v ∧ s' = s) ∨ (s.1.1.1 q = none ∧
        s' = (((s.1.1.1.cacheQuery q v, s.1.1.2 + 1),
          fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2))) → post v s' ⦄
      embedTrapFreshIdxSigImpl psf M Salt pk sk (.inl (.inr q)) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h v s' hz =>
    h v s' ((mem_support_embedTrapFreshIdxSigImpl_read_iff psf M Salt pk sk).1 hz)

/-- One signing query of the inline-fresh signed-set handler, exactly. -/
@[spec high]
theorem embedTrapFreshIdxSigImpl_wp_sign (msg : M)
    (post : (GSpec).Range (.inr msg) → SState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r c x, x ∈ support (psf.trapdoorSample pk sk c) → post (r, x)
        (((s.1.1.1.cacheQuery (r, msg) c, s.1.1.2 + 1),
          fun t' => if t' = (r, msg) then some s.1.1.2 else s.1.2 t'), insert msg s.2) ⦄
      embedTrapFreshIdxSigImpl psf M Salt pk sk (.inr msg) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h σ _ hz => by
    obtain ⟨c, hx, rfl⟩ := (mem_support_embedTrapFreshIdxSigImpl_sign_iff psf M Salt pk sk).1 hz
    exact h σ.1 c σ.2 hx

/-- The inline-fresh signed-set handler grows its cached and indexed keys, its counter and its
signed set. -/
instance monotoneState_embedTrapFreshIdxSigImpl :
    (embedTrapFreshIdxSigImpl psf M Salt pk sk).MonotoneState
      fun s s' => ((∀ t, (s.1.1.1 t).isSome → (s'.1.1.1 t).isSome) ∧ s.1.1.2 ≤ s'.1.1.2) ∧
        (∀ t, (s.1.2 t).isSome → (s'.1.2 t).isSome) ∧ s.2 ⊆ s'.2 where
  refl _ := ⟨⟨fun _ => id, le_rfl⟩, fun _ => id, subset_rfl⟩
  trans _ _ _ h₁ h₂ := ⟨⟨fun t => h₂.1.1 t ∘ h₁.1.1 t, h₁.1.2.trans h₂.1.2⟩,
    fun t => h₂.2.1 t ∘ h₁.2.1 t, h₁.2.2.trans h₂.2.2⟩
  step t s := by
    rintro ⟨a, s'⟩ hz
    rcases t with (n | q) | msg
    · rw [(mem_support_embedTrapFreshIdxSigImpl_unif_iff psf M Salt pk sk).1 hz]
      exact ⟨⟨fun _ => id, le_rfl⟩, fun _ => id, subset_rfl⟩
    · rcases (mem_support_embedTrapFreshIdxSigImpl_read_iff psf M Salt pk sk).1 hz with
        ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ⟨⟨fun _ => id, le_rfl⟩, fun _ => id, subset_rfl⟩
      · exact ⟨⟨fun _ => isSome_cacheQuery₄ M Salt, Nat.le_succ _⟩, fun _ => isSome_update₄ M Salt,
          subset_rfl⟩
    · obtain ⟨c, -, rfl⟩ := (mem_support_embedTrapFreshIdxSigImpl_sign_iff psf M Salt pk sk).1 hz
      exact ⟨⟨fun _ => isSome_cacheQuery₄ M Salt, Nat.le_succ _⟩, fun _ => isSome_update₄ M Salt,
        Finset.subset_insert _ _⟩

end GPVHashAndSign
