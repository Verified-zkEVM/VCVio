/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.EmbedIndex

/-! # GPV Hash-and-Sign: Trapdoor-Recording Run Projections

The counter-augmented trapdoor-recording run `progGameRunImplCombinedTrapCount` projects onto the
signed-set-augmented inline-fresh embed run, its signed set only grows, entries it has frozen stay
frozen, and its write-only preimage table is independent of the run until read. These facts feed
the per-slot deferred-sampling bound `trap_freshSig_le_winnerSlot_deferred`, which the reservoir
extraction in `GPVHashAndSign.Reservoir` consumes.
-/

public section

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool}
  [DecidableEq Range] [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt]

/-! ### Trap-count → fresh-sig cache/counter/idx/signedSet projection

The counter-augmented trapdoor-recording run `progGameRunImplCombinedTrapCount` and the
signed-set-augmented inline-fresh embed run `embedTrapFreshIdxSigImpl` draw their cached
random-oracle images identically: both cache a *fresh* uniform draw at every programming event (the
trap handler embeds nothing, and the fresh-sig handler has no winner branch).  They differ only in
the *extra* book-keeping the trap run carries — the freshness Bool flag and the write-only trapdoor
preimage table — both of which are distributionally passive.  Dropping them and reshaping the tuple
recovers the fresh-sig run's `(((cache × counter) × idx) × signedSet)` state exactly
(`map_run_progGameRunImplCombinedTrapCount_freshSig_proj`), at the *distribution* level: the trap
run's per-programming-event trapdoor draw `x ← trapdoorSample pk sk v` is never read by either run,
so under `NeverFail` it contributes only its (unit) mass. -/

/-- **`evalSPMF`-level state-projection transport (differing state types).** If every oracle step of
`impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec'))` becomes the corresponding `impl₂` step after
mapping the state with `proj : σ₁ → σ₂` *at the distribution level*, then the full simulated runs
agree under the same projection at the distribution level.  This is the `evalSPMF`-level relaxation
of `OracleComp.map_run_simulateQ_eq_of_query_map_eq`: the per-query hypothesis may discard a
never-failing answer-irrelevant draw (e.g. a write-only trapdoor sample) that breaks the *monadic*
equality but preserves the distribution. -/
theorem evalSPMF_map_run_simulateQ_eq_of_query_evalSPMF_map_eq
    {ι : Type} {spec : OracleSpec ι}
    {σ₁ σ₂ : Type} {α : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      𝒮[Prod.map id proj <$> (impl₁ t).run s] = 𝒮[(impl₂ t).run (proj s)])
    (oa : OracleComp spec α) (s : σ₁) :
    𝒮[Prod.map id proj <$> (simulateQ impl₁ oa).run s] =
      𝒮[(simulateQ impl₂ oa).run (proj s)] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      rw [evalSPMF_bind_congr' ((impl₁ t).run s)
        (ob₂ := fun x => (simulateQ impl₂ (oa x.1)).run (proj x.2))
        (fun x => ih x.1 x.2)]
      rw [show ((impl₁ t).run s >>= fun x => (simulateQ impl₂ (oa x.1)).run (proj x.2))
            = ((Prod.map id proj <$> (impl₁ t).run s) >>= fun x =>
                (simulateQ impl₂ (oa x.1)).run x.2) from by
        rw [bind_map_left]; rfl]
      rw [evalSPMF_bind, hproj t s, ← evalSPMF_bind]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-query trap-count → fresh-sig distribution projection.** Dropping the freshness Bool flag
and the write-only trapdoor table from one `progGameRunImplCombinedTrapCount` query step — and
reshaping the remaining `(cache, signedSet, idx, counter)` components into the fresh-sig
`(((cache × counter) × idx) × signedSet)` layout — recovers the corresponding
`embedTrapFreshIdxSigImpl` step at the distribution level.  Both handlers cache a fresh uniform draw
at every programming event; the trap run's extra trapdoor sample `x ← trapdoorSample pk sk v` is
never read, so under `hNF` it is a never-failing value-irrelevant prefix that drops out. -/
lemma progGameRunImplCombinedTrapCount_freshSig_proj (pk : PK) (sk : SK)
    (hNF : ∀ c : Range, NeverFail (psf.trapdoorSample pk sk c))
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    𝒮[Prod.map id
        (fun s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
              ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) =>
          ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2) :
            (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)) <$>
        (progGameRunImplCombinedTrapCount psf M Salt pk sk t).run s] =
      𝒮[(embedTrapFreshIdxSigImpl psf M Salt pk sk t).run
        ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2))] := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombinedTrapCount_run_inl_inl, embedTrapFreshIdxSigImpl_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [progGameRunImplCombinedTrapCount_run_inl_inr, embedTrapFreshIdxSigImpl_run_inl_inr]
          cases hq : s.1.1.1.1 q with
          | none =>
              -- RO miss: the trapdoor sample `x` is recorded write-only in the table (which the
              -- projection drops), so the projected output is `x`-independent and `x` drops out.
              simp only [map_bind, map_pure, Prod.map, id_eq]
              rw [map_eq_bind_pure_comp]
              refine evalSPMF_bind_congr' _ (fun v => ?_)
              rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails
                (psf.trapdoorSample pk sk v) (hNF v).probFailure_eq_zero _]
              rfl
          | some v => simp [Prod.map]
  | inr msg =>
      -- Signing: the trapdoor sample `x` *is* part of the output `(r, x)` on both sides, so the two
      -- signing steps draw `x ← trapdoorSample pk sk c` and output `(r, x)` identically.
      rw [progGameRunImplCombinedTrapCount_run_inr, embedTrapFreshIdxSigImpl_run_inr]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, Prod.map, id_eq, pure_bind]
      rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **Run-level trap-count → fresh-sig distribution projection.** Transports the per-query step
`progGameRunImplCombinedTrapCount_freshSig_proj` through the whole adaptive fold via
`evalSPMF_map_run_simulateQ_eq_of_query_evalSPMF_map_eq`: dropping the freshness Bool flag and the
write-only trapdoor table from the full simulated trap-count run, and reshaping to the fresh-sig
state layout, recovers the `embedTrapFreshIdxSigImpl` run distribution. -/
lemma map_run_progGameRunImplCombinedTrapCount_freshSig_proj (pk : PK) (sk : SK)
    (hNF : ∀ c : Range, NeverFail (psf.trapdoorSample pk sk c))
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    𝒮[Prod.map id
        (fun s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
              ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) =>
          ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2) :
            (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)) <$>
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] =
      𝒮[(simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run
        ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2))] := by
  exact evalSPMF_map_run_simulateQ_eq_of_query_evalSPMF_map_eq
    (progGameRunImplCombinedTrapCount psf M Salt pk sk)
    (embedTrapFreshIdxSigImpl psf M Salt pk sk)
    (fun s => ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2)))
    (progGameRunImplCombinedTrapCount_freshSig_proj psf M Salt pk sk hNF) oa s

omit [Fintype Salt] in
/-- **Step-2 embed-side reduction to the common freshness-confined deferred functional.**  The
inline-fresh-run expectation of the *freshness-confined winner-slot deferred-trapdoor* functional

  `Wf w := if forged.msg ∉ signedSet_w ∧ idx_w(forged) = some j then
              Pr[= forged.dom | trapdoorSample (cache_w forged)] else 0`

is a lower bound for the winner-slot-restricted per-target embedding win
(`reservoir_embed_winnerIdx_le`'s left side, i.e. the right side of the floor-free coupling).  The
front target average `∑' y, Pr[= y] · embedTrapIdxImpl … j y` is lifted to the signed-set-augmented
index run (`map_run_embedTrapIdxSigImpl_proj`, signed set passive) and then to the inline-fresh run
(`evalSPMF_frontDraw_embedTrapIdxSigImpl_eq_embedTrapFreshSigImpl`).  On the inline-fresh run the
freshness recovery (`embedTrapIdxSigImpl_fresh_idx_cache_eq`) makes the diagonal
`cache(forged) = some y` automatic on the freshness-confined winner slot, so the front `y` is
recovered as the cached image and the embed win event's literal `cache(forged) = some y` is matched;
the residual freshness restriction `forged.msg ∉ signedSet` only *decreases* the inline-fresh-run
expectation relative to the (freshness-free) embed win mass, so the bound is an inequality. -/
lemma freshSig_winnerSlot_deferred_le_embed [DecidableEq Domain] [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    (∑' w : (M × (Salt × Domain)) ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
        Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) (adv.main pk)).run
            ((((∅, 0), fun _ => none), ∅))] *
          (if w.1.1 ∉ w.2.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some j then
              Pr[= w.1.2.2 | psf.trapdoorSample pk sk
                ((w.2.1.1.1 (w.1.2.1, w.1.1)).getD default)]
            else 0)) ≤
      ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
          Pr[= true | (do
            let r ← (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (adv.main pk)).run
              (((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none))
            let x ← psf.trapdoorSample pk sk ((r.2.1.1 (r.1.2.1, r.1.1)).getD y)
            pure (decide (r.1.2.2 = x) && decide (r.2.1.1 (r.1.2.1, r.1.1) = some y) &&
              decide (r.2.2 (r.1.2.1, r.1.1) = some j)) : ProbComp Bool)] := by
  classical
  -- Rewrite each per-target embed win on the Sig-augmented run (signed set passive), then express
  -- the win mass as a `tsum` over the run output `r`.
  rw [tsum_probOutput_embedTrapFreshIdxSig_mul_eq_frontDraw psf M Salt pk sk j (adv.main pk)
    ((((∅, 0), fun _ => none), ∅))]
  refine ENNReal.tsum_le_tsum fun y => ?_
  refine mul_le_mul' le_rfl ?_
  -- Lift the un-augmented embed run on the RHS to the signed-set-augmented run.
  rw [show (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (adv.main pk)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none))
      = Prod.map id (Prod.fst :
          (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
            ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) <$>
        (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((((∅, 0), fun _ => none), ∅)) from
    (map_run_embedTrapIdxSigImpl_proj psf M Salt pk sk j y (adv.main pk)
      ((((∅, 0), fun _ => none), ∅))).symm]
  rw [bind_map_left]
  -- Express the win mass as a `tsum` over the Sig run output and compare termwise.
  rw [probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun w => ?_
  simp only [Prod.map, id_eq]
  -- Compare `Pr[= w | run] · Wf w ≤ Pr[= w | run] · winContinuation w`; off-support both vanish,
  -- on-support the freshness recovery aligns the literals.
  by_cases hsupp : w ∈ support ((simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y)
      (adv.main pk)).run ((((∅, 0), fun _ => none), ∅)))
  · refine mul_le_mul' le_rfl ?_
    -- The win predicate is `decide (r.dom = x) && decide (cache forged = some y) &&
    -- decide (idx forged = some j)`, with the trapdoor draw `x ← trapdoor ((cache forged).getD y)`.
    by_cases hWf : w.1.1 ∉ w.2.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some j
    · obtain ⟨hfresh, hidx⟩ := hWf
      -- Freshness recovery on the Sig run: `idx forged = some j` and forged unsigned force
      -- `cache forged = some y`.
      have hcache : w.2.1.1.1 (w.1.2.1, w.1.1) = some y :=
        embedTrapIdxSigImpl_fresh_idx_cache_eq psf M Salt pk sk j y (adv.main pk) w hsupp
          (w.1.2.1, w.1.1) hidx hfresh
      rw [ite_eq_left ⟨hfresh, hidx⟩, probOutput_bind_eq_tsum]
      -- The continuation `pure (decide (dom = x) && decide (cache = some y) && decide (idx = j))`
      -- has both run-only literals `true`; it reduces to matching `dom = x`, so the `tsum` over `x`
      -- collapses to the single diagonal term at `x = dom`.
      refine le_of_eq ?_
      simp only [hcache, hidx, Option.getD_some, decide_true, Bool.and_true]
      rw [tsum_eq_single w.1.2.2 (fun x hx => by
        rw [probOutput_pure_eq_indicator]
        simp only [Set.indicator_apply, Set.mem_singleton_iff, eq_comm (a := true),
          decide_eq_true_eq, Ne.symm hx, ite_false, mul_zero])]
      rw [probOutput_pure_eq_indicator]
      simp only [Set.indicator_apply, Set.mem_singleton_iff, eq_comm (a := true),
        decide_eq_true_eq, ite_true, Function.const_apply, mul_one]
    · rw [ite_eq_right hWf]; exact zero_le
  · rw [probOutput_eq_zero_of_not_mem_support hsupp, zero_mul]; exact zero_le

omit [DecidableEq Range] [Fintype Salt] in
/-- **The signed set only grows along the trap-count run.**  Every reachable final state's signed
set contains the start signed set: signing inserts the queried message and no step removes from the
signed set. -/
lemma progGameRunImplCombinedTrapCount_signedSet_grows (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)),
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        s.1.1.1.2 ⊆ z.2.1.1.1.2 := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact subset_rfl
  | query_bind t mx ih =>
      intro s z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        have := ih pv pst z hz; rw [hpst] at this; exact this
      · rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            have := ih pv pst z hz; rw [hpst] at this; exact this
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, -, x, -, -, hpst⟩ := hps
            have := ih pv pst z hz; rw [hpst] at this; exact this
      · rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, -, -, hpst⟩ := hps
        have hih := ih pv pst z hz
        rw [hpst] at hih
        exact (Finset.subset_insert _ _).trans hih

omit [DecidableEq Range] [Fintype Salt] in
/-- **Write-once freezing of a programmed, unsigned key on the trap-count run.**  Once a key `k₀` is
cached (`cache_s(k₀) ≠ none`) and its message stays unsigned through the run (`k₀.2 ∉ z.signedSet`
at the reachable final state `z`), both its cached image and its recorded trapdoor preimage are
frozen: `cache_z(k₀) = cache_s(k₀)` and `table_z(k₀) = table_s(k₀)`.  Random-oracle misses fire only
on cache misses, so they cannot overwrite an already-cached `k₀`; the signing branch writes at
`(r, msg)` and inserts `msg` into the signed set, so if it touched `k₀` it would sign `k₀.2`,
contradicting the final-state freshness (the signed set only grows). -/
lemma progGameRunImplCombinedTrapCount_frozen (pk : PK) (sk : SK) (k₀ : Salt × M) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)),
      s.1.1.1.1 k₀ ≠ none →
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        k₀.2 ∉ z.2.1.1.1.2 →
        z.2.1.1.1.1 k₀ = s.1.1.1.1 k₀ ∧ z.2.1.2 k₀ = s.1.2 k₀ := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s hs z hz hfresh
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl⟩
  | query_bind t mx ih =>
      intro s hs z hz hfresh
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        rw [hpst] at hz
        exact ih pv s hs z hz hfresh
      · rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            rw [hpst] at hz
            exact ih pv s hs z hz hfresh
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, -, x, -, -, hpst⟩ := hps
            -- The miss is at `mc ≠ k₀` (since `cache_s(k₀) ≠ none = cache_s(mc)`), so `k₀` is
            -- untouched; apply the IH from the post-step state, which still has `cache(k₀) ≠ none`.
            have hne : k₀ ≠ mc := fun h => hs (by rw [h]; exact hq)
            obtain ⟨hcache, htbl⟩ := ih pv pst (by
              rw [hpst]; simp only [QueryCache.cacheQuery_of_ne _ _ hne]; exact hs) z hz hfresh
            rw [hcache, htbl, hpst]
            simp only [QueryCache.cacheQuery_of_ne _ _ hne, ite_eq_right hne]
            exact ⟨trivial, trivial⟩
      · rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, -, -, hpst⟩ := hps
        -- The signing inserts `msg` into the signed set; since the post-state's signed set is
        -- contained in the final `z`'s signed set, and `k₀.2 ∉ z.signedSet`, we get `msg ≠ k₀.2`,
        -- hence `(r, msg) ≠ k₀`, so the signing step left `k₀` untouched.
        have hmsg : msg ≠ k₀.2 := by
          intro hmeq
          have hpst_sgn : k₀.2 ∈ pst.1.1.1.2 := by
            rw [hpst]; simp only [hmeq, Finset.mem_insert, true_or]
          have hgrow := progGameRunImplCombinedTrapCount_signedSet_grows psf M Salt pk sk
            (mx pv) pst z hz
          exact hfresh (hgrow hpst_sgn)
        have hk : k₀ ≠ (r, msg) := fun h => hmsg (by rw [h])
        obtain ⟨hcache, htbl⟩ := ih pv pst (by
          rw [hpst]; simp only [QueryCache.cacheQuery_of_ne _ _ hk]; exact hs) z hz hfresh
        rw [hcache, htbl, hpst]
        simp only [QueryCache.cacheQuery_of_ne _ _ hk, ite_eq_right hk]
        exact ⟨trivial, trivial⟩

omit [DecidableEq Range] [Fintype Salt] in
/-- **Table-independence of any output/cache/idx/signedSet expectation on the trap-count run.**  The
trap handler never reads the write-only preimage table, so any output functional `F` of the output
and the projected `(cache, counter, idx, signedSet)` state has the same expectation from two start
states `s₁`, `s₂` that agree on everything except the table (`s₁.1.1 = s₂.1.1` and `s₁.2 = s₂.2`,
i.e. the cache/signed-set/bad components and the idx/counter components coincide).  Instance of the
generic state-relation transfer `tsum_probOutput_simulateQ_run_mul_of_rel`. -/
lemma progGameRunImplCombinedTrapCount_table_indep (pk : PK) (sk : SK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (F : β →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞)
    (s₁ s₂ : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ))
    (h11 : s₁.1.1 = s₂.1.1) (h2 : s₁.2 = s₂.2) :
    (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s₁] *
        F z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2))) =
      ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s₂] *
        F z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) := by
  classical
  exact OracleComp.DeferredSampling.tsum_probOutput_simulateQ_run_mul_of_rel
    (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa
    (fun u₁ u₂ => u₁.1.1 = u₂.1.1 ∧ u₁.2 = u₂.2)
    (fun t a b hab K hKinv => by
      obtain ⟨hb11, hb2⟩ := hab
      rcases t with (n | mc) | msg
      · rw [progGameRunImplCombinedTrapCount_run_inl_inl,
          progGameRunImplCombinedTrapCount_run_inl_inl]
        rw [tsum_probOutput_bind_mul,
          tsum_probOutput_bind_mul]
        refine tsum_congr fun v => ?_
        rw [tsum_probOutput_pure_mul,
          tsum_probOutput_pure_mul]
        exact congrArg _ (hKinv v a b ⟨hb11, hb2⟩)
      · rw [progGameRunImplCombinedTrapCount_run_inl_inr,
          progGameRunImplCombinedTrapCount_run_inl_inr]
        have hcache : a.1.1.1.1 mc = b.1.1.1.1 mc := by rw [hb11]
        rw [hcache]
        cases hq : b.1.1.1.1 mc with
        | some v =>
            rw [tsum_probOutput_pure_mul,
              tsum_probOutput_pure_mul]
            exact hKinv v a b ⟨hb11, hb2⟩
        | none =>
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun v => congrArg _ ?_
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun x => congrArg _ ?_
            rw [tsum_probOutput_pure_mul,
              tsum_probOutput_pure_mul]
            refine hKinv v _ _ ⟨?_, ?_⟩
            · simp only [hb11]
            · simp only [hb2]
      · rw [progGameRunImplCombinedTrapCount_run_inr, progGameRunImplCombinedTrapCount_run_inr]
        rw [tsum_probOutput_bind_mul,
          tsum_probOutput_bind_mul]
        refine tsum_congr fun r => congrArg _ ?_
        rw [tsum_probOutput_bind_mul,
          tsum_probOutput_bind_mul]
        refine tsum_congr fun v => congrArg _ ?_
        rw [tsum_probOutput_bind_mul,
          tsum_probOutput_bind_mul]
        refine tsum_congr fun x => congrArg _ ?_
        rw [tsum_probOutput_pure_mul,
          tsum_probOutput_pure_mul]
        refine hKinv _ _ _ ⟨?_, ?_⟩
        · simp only [hb11]
        · simp only [hb2])
    (fun g st => F g ((((st.1.1.1.1, st.2.2), st.2.1), st.1.1.1.2)))
    (fun g u₁ u₂ huv => by
      obtain ⟨hu11, hu2⟩ := huv
      have hst : ((((u₁.1.1.1.1, u₁.2.2), u₁.2.1), u₁.1.1.1.2) :
            (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
          = ((((u₂.1.1.1.1, u₂.2.2), u₂.2.1), u₂.1.1.1.2)) := by
        rw [show u₁.1.1.1.1 = u₂.1.1.1.1 from by rw [hu11],
          show u₁.1.1.1.2 = u₂.1.1.1.2 from by rw [hu11],
          show u₁.2.1 = u₂.2.1 from by rw [hu2], show u₁.2.2 = u₂.2.2 from by rw [hu2]]
      rw [hst])
    s₁ s₂ ⟨h11, h2⟩

open Classical in
omit [DecidableEq Range] [Fintype Salt] in
/-- **Frozen-table expectation on the trap-count run.**  When the forged key `k₀` is already cached
at the start (`cache_s(k₀) ≠ none`) and the output functional `G` vanishes off the freshness event
`k₀.2 ∉ signedSet`, the recorded table at `k₀` is frozen on the relevant support, so the
`G · 1_{table(k₀) = some sStar}` expectation factors as the constant frozen indicator
`1_{table_s(k₀) = some sStar}` times the `G` expectation. -/
lemma progGameRunImplCombinedTrapCount_table_frozen_eq (pk : PK) (sk : SK)
    (k₀ : Salt × M) (sStar : Domain)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (G : β →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞)
    (hGfresh : ∀ b w, k₀.2 ∈ w.2 → G b w = 0)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
        (((Salt × M) → Option ℕ) × ℕ))
    (hs : s.1.1.1.1 k₀ ≠ none) :
    (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] *
        (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
          (if z.2.1.2 k₀ = some sStar then 1 else 0))) =
      (if s.1.2 k₀ = some sStar then 1 else 0) *
        ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] *
          G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2) ) := by
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun z => ?_
  by_cases hz : z ∈ support
      ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s)
  · by_cases hzfresh : k₀.2 ∈ z.2.1.1.1.2
    · rw [hGfresh z.1 _ (by exact hzfresh)]; ring
    · obtain ⟨-, htbl⟩ := progGameRunImplCombinedTrapCount_frozen psf M Salt pk sk k₀ oa s hs z hz
        hzfresh
      rw [htbl]; ring
  · rw [probOutput_eq_zero_of_not_mem_support hz]; ring

open Classical in
omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-step deferral of one write-only trapdoor draw on the trap-count run (state-general
form).**  For a fixed key `k₀` and recorded value `sStar`, and any nonnegative output functional
`G` of the run output and the projected `(cache, counter, idx, signedSet)` state, the trap-count run
expectation of `G · 1_{table(k₀) = some sStar}` equals the run expectation of `G · D s`, where the
*deferred* value `D s z` is:

* the frozen indicator `1_{table_s(k₀) = some sStar}` if `k₀` was already programmed at the start
  state `s` (`cache_s(k₀) ≠ none`); or
* the deferred trapdoor-draw probability `Pr[= sStar | trapdoorSample (cache_z(k₀))]` if `k₀` is
  freshly programmed during the run (`cache_s(k₀) = none` and `cache_z(k₀) ≠ none`), and `0` if `k₀`
  is never programmed (`cache_z(k₀) = none`).

The recorded preimage `x ← trapdoorSample (cache k₀)` is sampled write-only at the `k₀` programming
event and never read, so its position in the adaptive fold is irrelevant: at the programming step
the inline `x`-draw is integrated against the frozen continuation (`cache(k₀)` and `table(k₀)` are
both frozen afterwards), turning `1_{table(k₀) = some sStar}` into the trapdoor-draw probability;
off the programming step the table at `k₀` is untouched, so the IH carries through.  This is the
defer-to-end twin of the front-loading lift, *keeping* the forged draw rather than dropping it. -/
lemma progGameRunImplCombinedTrapCount_table_defer (pk : PK) (sk : SK)
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (k₀ : Salt × M) (sStar : Domain)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (G : β →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞)
    (hGfresh : ∀ b w, k₀.2 ∈ w.2 → G b w = 0) :
    ∀ (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
        (((Salt × M) → Option ℕ) × ℕ)),
      (s.1.2 k₀ ≠ none → s.1.1.1.1 k₀ ≠ none) →
      (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] *
          (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
            (if z.2.1.2 k₀ = some sStar then 1 else 0))) =
        ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] *
          (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
            (match s.1.1.1.1 k₀ with
              | some _ => (if s.1.2 k₀ = some sStar then 1 else 0)
              | none =>
                  match z.2.1.1.1.1 k₀ with
                  | some v => Pr[= sStar | psf.trapdoorSample pk sk v]
                  | none => 0)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s htc
      simp only [simulateQ_pure, StateT.run_pure,
        tsum_probOutput_pure_mul]
      -- At `pure`, the final state is the start state, so the table at `k₀` is `s.1.2 k₀`.
      rcases hc : s.1.1.1.1 k₀ with _ | v
      · -- `k₀` unprogrammed at start (and at end): the deferred branch gives `0`; the table/cache
        -- lockstep `htc` forces `table_s(k₀) = none`, so the indicator branch is also `0`.
        have htbl : s.1.2 k₀ = none := by
          by_contra hne; exact (htc hne) hc
        rw [ite_eq_right (by rw [htbl]; simp)]
      · rfl
  | query_bind t mx ih =>
      intro s htc
      -- **Branch A: `k₀` already programmed at the start.**  The deferred value is the constant
      -- frozen indicator; both sides factor through the frozen-table expectation lemma.
      rcases hcs : s.1.1.1.1 k₀ with _ | v₀
      · -- **Branch B: `k₀` not yet programmed at the start.**  Split the leading step from the
        -- continuation and integrate the (single) `k₀`-programming draw to the front.
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rcases t with (n | mc) | msg
        · -- Uniform query: the state is untouched, `cache(k₀)` stays `none`; apply the IH at `s`.
          rw [progGameRunImplCombinedTrapCount_run_inl_inl, bind_assoc]
          simp only [pure_bind]
          rw [tsum_probOutput_bind_mul,
            tsum_probOutput_bind_mul]
          refine tsum_congr fun v => congrArg _ ?_
          have hih := ih v s htc
          simp only [hcs] at hih
          exact hih
        · -- Random-oracle query at `mc`.
          rw [progGameRunImplCombinedTrapCount_run_inl_inr]
          cases hmcq : s.1.1.1.1 mc with
          | some v =>
              -- Cache hit: state untouched; apply the IH at `s`.
              simp only [pure_bind]
              have hih := ih v s htc
              simp only [hcs] at hih
              exact hih
          | none =>
              have htbls : s.1.2 k₀ = none := by
                by_contra hne; exact (htc hne) hcs
              simp only [bind_assoc, pure_bind]
              by_cases hmck : mc = k₀
              · -- **The forged random-oracle miss: integrate the single trapdoor draw.**
                subst hmck
                rw [tsum_probOutput_bind_mul,
                  tsum_probOutput_bind_mul]
                refine tsum_congr fun v => congrArg _ ?_
                -- Abbreviate the per-`(v, x)` `G`-expectation `Q x` from the post-state.
                set Q : Domain → ℝ≥0∞ := fun x =>
                  ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
                      (mx v)).run
                      ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                        fun t' => if t' = mc then some x else s.1.2 t'),
                        (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1)] *
                    G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) with hQ
                -- **LHS inner**, per `x`: apply the deferral IH at the post-state (where `cache mc`
                -- is `some v ≠ none`), turning `1_{table_z(mc) = sStar}` into the *frozen* value
                -- `1_{table_post(mc) = sStar} = 1_{x = sStar}`; then the constant factors out.
                have hLHS : ∀ x : Domain,
                    (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
                        (mx v)).run
                        ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                          fun t' => if t' = mc then some x else s.1.2 t'),
                          (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1)] *
                      (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
                        (if z.2.1.2 mc = some sStar then 1 else 0)))
                      = (if x = sStar then 1 else 0) * Q x := by
                  intro x
                  have hihx := ih v
                    ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                        fun t' => if t' = mc then some x else s.1.2 t'),
                        (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1) (by
                      simp only [QueryCache.cacheQuery_self]; exact fun _ => Option.some_ne_none v)
                  simp only [QueryCache.cacheQuery_self] at hihx
                  rw [hihx]
                  -- the post-state's `table mc = some x`, so the frozen indicator is `1_{x=sStar}`
                  simp only [ite_true, Option.some.injEq]
                  rw [hQ]
                  simp only []
                  rw [← ENNReal.tsum_mul_left]
                  refine tsum_congr fun z => ?_; ring
                -- **RHS inner**, per `x`: the cache at `mc` is frozen to `some v`, so the deferred
                -- value is the constant `Pr[= sStar | trapdoorSample v]`; factor it out.
                have hRHS : ∀ x : Domain,
                    (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
                        (mx v)).run
                        ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                          fun t' => if t' = mc then some x else s.1.2 t'),
                          (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1)] *
                      (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
                        (match z.2.1.1.1.1 mc with
                          | some w => Pr[= sStar | psf.trapdoorSample pk sk w]
                          | none => 0)))
                      = Pr[= sStar | psf.trapdoorSample pk sk v] * Q x := by
                  intro x
                  rw [hQ]
                  simp only []
                  rw [← ENNReal.tsum_mul_left]
                  refine tsum_congr fun z => ?_
                  by_cases hz : z ∈ support
                      ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (mx v)).run
                        ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                          fun t' => if t' = mc then some x else s.1.2 t'),
                          (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1))
                  · by_cases hzfresh : mc.2 ∈ z.2.1.1.1.2
                    · -- `mc.2` signed at `z` ⟹ `G = 0`, so the term vanishes on both sides.
                      rw [hGfresh z.1 _ (by exact hzfresh)]; ring
                    · have hpostc : ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                          fun t' => if t' = mc then some x else s.1.2 t'),
                          (fun t' => if t' = mc then some s.2.2 else s.2.1 t'),
                          s.2.2 + 1).1.1.1.1 mc ≠ none := by
                        simp only [QueryCache.cacheQuery_self]; exact Option.some_ne_none v
                      obtain ⟨hzcache, -⟩ := progGameRunImplCombinedTrapCount_frozen psf M Salt pk
                        sk mc (mx v) _ hpostc z hz hzfresh
                      rw [hzcache]
                      simp only [QueryCache.cacheQuery_self]; ring
                  · rw [probOutput_eq_zero_of_not_mem_support hz]; ring
                -- **Combine.**  Per `x`, the inner sum is `Pr[= sStar | trapdoorSample v] · Q x` on
                -- the right and `1_{x = sStar} · Q x` on the left, and `Q` is table-independent
                -- (`progGameRunImplCombinedTrapCount_table_indep`), so `Q x = Q sStar`; integrating
                -- `x ← trapdoorSample v` turns the left indicator into `Pr[= sStar | trapdoor v]`.
                rw [tsum_probOutput_bind_mul,
                  tsum_probOutput_bind_mul]
                simp only [hLHS, hRHS]
                -- `Q` is independent of the table value `x`, so `Q x = Q sStar` for all `x`.
                have hQindep : ∀ x : Domain, Q x = Q sStar := fun x => by
                  rw [hQ]
                  exact progGameRunImplCombinedTrapCount_table_indep psf M Salt pk sk (mx v) _ _ _
                    rfl rfl
                simp_rw [hQindep]
                -- LHS: `∑' x, Pr[= x] · (1_{x = sStar} · Q sStar) = Pr[= sStar | trapdoor v] · Q`.
                rw [show (∑' x : Domain, Pr[= x | psf.trapdoorSample pk sk v] *
                        ((if x = sStar then 1 else 0) * Q sStar))
                      = Pr[= sStar | psf.trapdoorSample pk sk v] * Q sStar from by
                    rw [tsum_eq_single sStar
                      (fun x hx => by rw [ite_eq_right hx, zero_mul, mul_zero])]
                    rw [ite_eq_left rfl, one_mul]]
                -- RHS: `∑' x, Pr[= x] · (Pr[= sStar | trapdoor v] · Q sStar) = 1 · (… · Q)`.
                rw [ENNReal.tsum_mul_right,
                  tsum_probOutput_eq_one' (hNF v).probFailure_eq_zero, one_mul]
              · -- Miss at `mc ≠ k₀`: `cache(k₀)` stays `none`; apply the IH at the post-state.
                rw [tsum_probOutput_bind_mul,
                  tsum_probOutput_bind_mul]
                refine tsum_congr fun v => congrArg _ ?_
                rw [tsum_probOutput_bind_mul,
                  tsum_probOutput_bind_mul]
                refine tsum_congr fun x => congrArg _ ?_
                -- Apply the IH at the post-state; `cache(k₀)` is unchanged (miss at `mc ≠ k₀`),
                -- so its outer deferred branch stays `none`, matching the goal.
                have hih := ih v
                  ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                      fun t' => if t' = mc then some x else s.1.2 t'),
                      (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1) (by
                    simp only [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hmck), hcs, ite_eq_right
                      (Ne.symm hmck), htbls]
                    exact fun h => absurd rfl h)
                simp only [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hmck), hcs] at hih
                exact hih
        · -- Signing query on `msg`.
          rw [progGameRunImplCombinedTrapCount_run_inr]
          simp only [bind_assoc, pure_bind]
          have htbls : s.1.2 k₀ = none := by
            by_contra hne; exact (htc hne) hcs
          by_cases hmsg : msg = k₀.2
          · -- Signing the forged message inserts `k₀.2` into the (monotone) signed set, so every
            -- continuation has `k₀.2 ∈ signedSet` and `G = 0`; both sides vanish termwise.
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun r => congrArg _ ?_
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun v => congrArg _ ?_
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun x => congrArg _ ?_
            refine tsum_congr fun z => ?_
            by_cases hz : z ∈ support
                ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (mx (r, x))).run
                  ((((s.1.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.1.2),
                    s.1.1.2 || saltKeyed M Salt s.1.1.1.1 r),
                    fun t' => if t' = (r, msg) then some x else s.1.2 t'),
                    (fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t'), s.2.2 + 1))
            · have hgrow := progGameRunImplCombinedTrapCount_signedSet_grows psf M Salt pk sk
                (mx (r, x)) _ z hz
              have hmem : k₀.2 ∈ z.2.1.1.1.2 :=
                hgrow (by simp only [hmsg, Finset.mem_insert, true_or])
              rw [hGfresh z.1 _ hmem]; ring
            · rw [probOutput_eq_zero_of_not_mem_support hz]; ring
          · -- `msg ≠ k₀.2` forces `(r, msg) ≠ k₀`, so `cache(k₀)` stays `none`; apply the IH.
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun r => congrArg _ ?_
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun v => congrArg _ ?_
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun x => congrArg _ ?_
            have hk : k₀ ≠ (r, msg) := fun h => hmsg (by rw [h])
            have hih := ih (r, x)
              ((((s.1.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.1.2),
                  s.1.1.2 || saltKeyed M Salt s.1.1.1.1 r),
                  fun t' => if t' = (r, msg) then some x else s.1.2 t'),
                  (fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t'), s.2.2 + 1) (by
                simp only [QueryCache.cacheQuery_of_ne _ _ hk, hcs, ite_eq_right hk, htbls]
                exact fun h => absurd rfl h)
            simp only [QueryCache.cacheQuery_of_ne _ _ hk, hcs] at hih
            exact hih
      · rw [progGameRunImplCombinedTrapCount_table_frozen_eq psf M Salt pk sk k₀ sStar _ G hGfresh s
          (by rw [hcs]; exact Option.some_ne_none v₀), ← ENNReal.tsum_mul_left]
        refine tsum_congr fun z => ?_; ring

open Classical in
omit [Fintype Salt] in
/-- **Step-2 trap-side table-defer to the common freshness-confined deferred functional.**  The
freshness-confined index-tagged trap-exact-match mass — the trap event
`forged.msg ∉ signedSet ∧ table(forged) = some forged.dom ∧ idx(forged) = some j` on the
counter-augmented trapdoor-recording run `progGameRunImplCombinedTrapCount` — is bounded by the
inline-fresh-run expectation of the freshness-confined winner-slot deferred-trapdoor functional

  `Wf w := if forged.msg ∉ signedSet_w ∧ idx_w(forged) = some j then
              Pr[= forged.dom | trapdoorSample (cache_w forged)] else 0`.

This is the genuinely-new (answer-irrelevant) content of GPV Step-2: at the freshness-confined
forged key the write-only trapdoor preimage `x ← trapdoorSample (cache forged)` recorded inline into
the
table is *never read* (an unsigned forged key is a random-oracle miss whose preimage enters only the
write-only table, never the adversary view), so it commutes to the end of the adaptive fold and
becomes a post-run independent trapdoor draw against the cached image.  Freshness is exactly what
makes this draw deferrable; a *signed* key returns `(r, x)` to the adversary, so its table draw is
not deferrable, which is why dropping freshness falsifies the bound. -/
lemma trap_freshSig_le_winnerSlot_deferred [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c)) :
    Pr[fun w : (M × (Salt × Domain)) ×
          (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
            (((Salt × M) → Option ℕ) × ℕ)) =>
          (w.1.1 ∉ w.2.1.1.1.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2) ∧
            w.2.2.1 (w.1.2.1, w.1.1) = some j |
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
          (adv.main pk)).run
          (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
            (fun _ => none), 0)]
      ≤ ∑' w : (M × (Salt × Domain)) ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
        Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) (adv.main pk)).run
            ((((∅, 0), fun _ => none), ∅))] *
          (if w.1.1 ∉ w.2.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some j then
              Pr[= w.1.2.2 | psf.trapdoorSample pk sk
                ((w.2.1.1.1 (w.1.2.1, w.1.1)).getD default)]
            else 0) := by
  classical
  -- Abbreviate the trap-state → fresh-sig-state projection (drop the freshness Bool flag and the
  -- write-only trapdoor table; reshape to the fresh-sig `(((cache × counter) × idx) × signedSet)`).
  set projS : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
        × (((Salt × M) → Option ℕ) × ℕ) →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M :=
    fun s => ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2)) with hprojS
  -- **Transport the RHS fresh-sig-run expectation onto the trap-count run.**  By the
  -- distribution-level projection, the fresh-sig run is the trap-count run mapped by
  -- `projS`, so the
  -- RHS expectation of `Wf` over the fresh-sig run equals its expectation over the trap-count run
  -- precomposed with `Prod.map id projS`.
  have hRHS : (∑' w, Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk)
          (adv.main pk)).run ((((∅, 0), fun _ => none), ∅))] *
        (if w.1.1 ∉ w.2.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some j then
            Pr[= w.1.2.2 | psf.trapdoorSample pk sk
              ((w.2.1.1.1 (w.1.2.1, w.1.1)).getD default)]
          else 0)) =
      ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
          (adv.main pk)).run
          (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
            (fun _ => none), 0)] *
        (if z.1.1 ∉ (projS z.2).2 ∧ (projS z.2).1.2 (z.1.2.1, z.1.1) = some j then
            Pr[= z.1.2.2 | psf.trapdoorSample pk sk
              (((projS z.2).1.1.1 (z.1.2.1, z.1.1)).getD default)]
          else 0) := by
    have hmap := map_run_progGameRunImplCombinedTrapCount_freshSig_proj psf M Salt pk sk hNF
      (adv.main pk)
      (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
        (fun _ => none), 0)
    simp only [hprojS] at hmap ⊢
    -- Pointwise: the fresh-sig output probability is the trap-count run mapped by `projS`.
    have hpt : ∀ w, Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk)
          (adv.main pk)).run ((((∅, 0), fun _ => none), ∅))]
        = Pr[= w | Prod.map id
            (fun s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
                ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) =>
              ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2) :
                (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)) <$>
            (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (adv.main pk)).run
              (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
                (fun _ => none), 0)] :=
      fun w => by rw [probOutput, probOutput, hmap]
    simp_rw [hpt]
    rw [tsum_probOutput_map_mul]
    refine tsum_congr fun z => ?_
    simp only [Prod.map, id_eq]
  rw [hRHS]
  -- **The per-run table-defer (the answer-irrelevant content).**  Both sides are
  -- now expectations over the *same* trap-count run; the LHS reads the recorded table at the forged
  -- point (`1_{table(forged) = some forged.dom}`), the RHS the deferred trapdoor draw against the
  -- cached image (`Pr[= forged.dom | trapdoorSample (cache forged)]`).  On the freshness-confined
  -- winner slot the recorded entry is the inline write-only draw `x ← trapdoorSample (cache
  -- forged)` sampled at the forged random-oracle miss and never read; its *expected* indicator over
  -- the run equals the deferred draw probability.
  --
  -- ⚠ This is NOT a per-final-state inequality (it FAILS pointwise: at a state whose table is
  -- already frozen to `some d₀`, the LHS indicator is `1_{d₀ = forged.dom}` while the RHS is
  -- `Pr[= forged.dom | trapdoorSample (cache forged)] < 1`).  It holds only in *expectation*: the
  -- recorded `x` is itself random (drawn at the forged miss), independent of `(output, cache)`
  -- given the run, so `E[1_{table(forged) = forged.dom}] = Pr[= forged.dom | trapdoorSample (cache
  -- forged)]`.  Mechanizing it requires *deferring* the single answer-irrelevant write-only draw
  -- `x` from its inline position at the forged miss to the end of the adaptive `simulateQ` fold (it
  -- commutes past every subsequent step because the continuation never reads `table(forged)` or the
  -- frozen `cache(forged)`), matching it to a post-run draw of `trapdoorSample (cache forged)`.
  -- The projection `map_run_progGameRunImplCombinedTrapCount_freshSig_proj` *drops* every table
  -- draw via `evalSPMF_bind_const_neverFails`; the defer-to-end induction over the trap run that
  -- keeps the deferred draw is `progGameRunImplCombinedTrapCount_table_defer`.  Below the FRESH
  -- conjunct `w.1.1 ∉ w.2.1.1.1.2` is carried throughout.
  rw [probEvent_eq_tsum_ite]
  refine le_of_eq ?_
  classical
  -- Decompose the output-dependent forged-key indicator over a fixed key/value pair `p`, swap the
  -- order of summation, and apply the (fixed-key) table-defer per `p`.  Recombining over `p` gives
  -- the deferred functional with the cache-read trapdoor probability.
  set proj2 : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
        × (((Salt × M) → Option ℕ) × ℕ) →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M :=
    fun st => ((((st.1.1.1.1, st.2.2), st.2.1), st.1.1.1.2)) with hproj2
  -- The per-pair selector functional.
  set Gp : (Salt × M) × Domain → (M × (Salt × Domain)) →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞ :=
    fun p b w => if (b.2.1, b.1) = p.1 ∧ b.2.2 = p.2 ∧ b.1 ∉ w.2 ∧ w.1.2 p.1 = some j
      then 1 else 0 with hGp
  set run := (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (adv.main pk)).run
    ((((∅, ∅), false), fun _ => none), (fun _ => none), 0) with hrun
  -- **LHS = double sum.**  The forged-key indicator collapses to the single pair
  -- `p = (forged, forged.dom)`.
  have hLHSdecomp : (∑' z, if (z.1.1 ∉ z.2.1.1.1.2 ∧ z.2.1.2 (z.1.2.1, z.1.1) = some z.1.2.2) ∧
          z.2.2.1 (z.1.2.1, z.1.1) = some j then Pr[= z | run] else 0)
      = ∑' p : (Salt × M) × Domain, ∑' z,
          Pr[= z | run] * (Gp p z.1 (proj2 z.2) * (if z.2.1.2 p.1 = some p.2 then 1 else 0)) := by
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun z => ?_
    simp only [hGp, hproj2]
    rw [tsum_eq_single ((z.1.2.1, z.1.1), z.1.2.2) (fun p hp => by
      rw [show (if (z.1.2.1, z.1.1) = p.1 ∧ z.1.2.2 = p.2 ∧ z.1.1 ∉ z.2.1.1.1.2 ∧
            z.2.2.1 p.1 = some j then (1 : ℝ≥0∞) else 0) = 0 from by
        refine ite_eq_right ?_
        rintro ⟨h1, h2, -, -⟩; exact hp (by rw [Prod.ext_iff]; exact ⟨h1.symm, h2.symm⟩),
        zero_mul, mul_zero])]
    simp only [true_and]
    by_cases hev : (z.1.1 ∉ z.2.1.1.1.2 ∧ z.2.1.2 (z.1.2.1, z.1.1) = some z.1.2.2) ∧
        z.2.2.1 (z.1.2.1, z.1.1) = some j
    · obtain ⟨⟨hfresh, htbl⟩, hidx⟩ := hev
      rw [ite_eq_left ⟨⟨hfresh, htbl⟩, hidx⟩, ite_eq_left ⟨hfresh, hidx⟩, ite_eq_left htbl]; ring
    · rw [ite_eq_right hev]
      by_cases htbl : z.2.1.2 (z.1.2.1, z.1.1) = some z.1.2.2
      · have hcond : ¬(z.1.1 ∉ z.2.1.1.1.2 ∧ z.2.2.1 (z.1.2.1, z.1.1) = some j) := by
          rintro ⟨hfresh, hidx⟩; exact hev ⟨⟨hfresh, htbl⟩, hidx⟩
        rw [ite_eq_left htbl, mul_one, ite_eq_right hcond, mul_zero]
      · rw [ite_eq_right htbl, mul_zero, mul_zero]
  -- **Per-pair table-defer.**  Apply the fixed-key table-defer lemma at `(k₀, sStar) = p` with the
  -- selector `Gp p` (which vanishes off the freshness event, as required).
  have hbridge : ∀ p : (Salt × M) × Domain,
      (∑' z, Pr[= z | run] * (Gp p z.1 (proj2 z.2) * (if z.2.1.2 p.1 = some p.2 then 1 else 0)))
        = ∑' z, Pr[= z | run] * (Gp p z.1 (proj2 z.2) *
            (match (proj2 z.2).1.1.1 p.1 with
              | some w => Pr[= p.2 | psf.trapdoorSample pk sk w]
              | none => 0)) := by
    intro p
    have hGfreshp : ∀ b w, p.1.2 ∈ w.2 → Gp p b w = 0 := by
      intro b w hmem
      rw [hGp]; refine ite_eq_right ?_
      rintro ⟨hbp, -, hbw, -⟩
      exact hbw (by rw [show b.1 = p.1.2 from by rw [← hbp]]; exact hmem)
    have hdefer := progGameRunImplCombinedTrapCount_table_defer psf M Salt pk sk hNF p.1 p.2
      (adv.main pk) (Gp p) hGfreshp
      (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
        (fun _ => none), 0) (by simp)
    -- the empty start has `cache p.1 = none`, so the deferred outer match reduces to the inner
    -- `match cache_z p.1`.
    simp only [hrun, hproj2] at hdefer ⊢
    refine hdefer.trans (tsum_congr fun z => congrArg _ (congrArg _ ?_))
    rcases (((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2).1.1.1 p.1 with _ | w <;> rfl
  -- **RHS = double sum.**  The deferred functional likewise collapses to the single forged pair.
  have hRHSdecomp : (∑' z, Pr[= z | run] *
          (if z.1.1 ∉ (proj2 z.2).2 ∧ (proj2 z.2).1.2 (z.1.2.1, z.1.1) = some j then
            Pr[= z.1.2.2 | psf.trapdoorSample pk sk
              (((proj2 z.2).1.1.1 (z.1.2.1, z.1.1)).getD default)]
          else 0))
      = ∑' p : (Salt × M) × Domain, ∑' z,
          Pr[= z | run] * (Gp p z.1 (proj2 z.2) *
            (match (proj2 z.2).1.1.1 p.1 with
              | some w => Pr[= p.2 | psf.trapdoorSample pk sk w]
              | none => 0)) := by
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun z => ?_
    simp only [hGp, hproj2]
    rw [tsum_eq_single ((z.1.2.1, z.1.1), z.1.2.2) (fun p hp => by
      rw [show (if (z.1.2.1, z.1.1) = p.1 ∧ z.1.2.2 = p.2 ∧ z.1.1 ∉ z.2.1.1.1.2 ∧
            z.2.2.1 p.1 = some j then (1 : ℝ≥0∞) else 0) = 0 from by
        refine ite_eq_right ?_
        rintro ⟨h1, h2, -, -⟩; exact hp (by rw [Prod.ext_iff]; exact ⟨h1.symm, h2.symm⟩),
        zero_mul, mul_zero])]
    simp only [true_and]
    -- diagonal `p = (forged, dom)`: `Gp = 1_{fresh ∧ idx=j}` and the deferred value reads
    -- `cache_z(forged)`; on the run support `idx = some j` forces `cache ≠ none` (idx/table/cache
    -- lockstep), so it matches the `getD default` form.
    by_cases hz : z ∈ support run
    · by_cases hfi : z.1.1 ∉ z.2.1.1.1.2 ∧ z.2.2.1 (z.1.2.1, z.1.1) = some j
      · obtain ⟨hfresh, hidx⟩ := hfi
        rw [ite_eq_left ⟨hfresh, hidx⟩, ite_eq_left ⟨hfresh, hidx⟩]
        -- recover `cache ≠ none` from `idx = some j` via the lockstep invariants
        have hzrun : z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
            (adv.main pk)).run ((((∅, ∅), false), fun _ => none), (fun _ => none), 0)) := by
          rw [← hrun]; exact hz
        have hidxne : z.2.2.1 (z.1.2.1, z.1.1) ≠ none := by rw [hidx]; exact Option.some_ne_none j
        have htblne : z.2.1.2 (z.1.2.1, z.1.1) ≠ none :=
          (progGameRunImplCombinedTrapCount_idx_iff_table psf M Salt pk sk (adv.main pk)
            ((((∅, ∅), false), fun _ => none), (fun _ => none), 0)
            (fun k => by simp) z hzrun (z.1.2.1, z.1.1)).2 hidxne
        obtain ⟨xv, htbleq⟩ := Option.ne_none_iff_exists'.1 htblne
        obtain ⟨w, hcache, -⟩ := progGameRunImplCombinedTrapCount_table_support psf M Salt pk sk
          (adv.main pk) ((((∅, ∅), false), fun _ => none), (fun _ => none), 0)
          (fun k x hx => by simp at hx) z hzrun (z.1.2.1, z.1.1) xv htbleq
        rw [hcache, Option.getD_some]; ring
      · simp only [ite_eq_right hfi, zero_mul, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hz]; ring
  -- **Combine.**  `LHS = (hLHSdecomp) ∑∑ indicator = (hbridge) ∑∑ deferred = (hRHSdecomp) RHS`.
  rw [hLHSdecomp]
  rw [show (∑' p : (Salt × M) × Domain, ∑' z, Pr[= z | run] *
        (Gp p z.1 (proj2 z.2) * (if z.2.1.2 p.1 = some p.2 then 1 else 0)))
      = ∑' p : (Salt × M) × Domain, ∑' z, Pr[= z | run] *
        (Gp p z.1 (proj2 z.2) *
          (match (proj2 z.2).1.1.1 p.1 with
            | some w => Pr[= p.2 | psf.trapdoorSample pk sk w]
            | none => 0)) from tsum_congr fun p => hbridge p]
  rw [← hRHSdecomp]

end GPVHashAndSign
