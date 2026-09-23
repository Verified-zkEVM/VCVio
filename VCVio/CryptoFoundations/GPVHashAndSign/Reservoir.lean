/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.TrapProjection

/-! # GPV Hash-and-Sign: Reservoir Extraction of the Exact-Match Branch

The exact-match (programmed-preimage) branch of the GPV forgery dichotomy is priced by embedding
the programmed-preimage challenge at a uniformly chosen programmed entry. The commutation lemmas
`reservoir_embed_commute_winner`, `reservoir_embed_commute_residual` and `reservoir_embed_commute`
move that embedding past the adversary's run, and `gpv_perKey_exactMatch_le_reservoir` bounds the
per-key exact-match probability by the reservoir game.
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

open Classical in
omit [Fintype Salt] in
/-- **The per-slot front-loading deferred-sampling coupling (floor-free form).**

The *index-tagged* trap-exact-match mass at slot `j` — the trap event on the counter-augmented run
`progGameRunImplCombinedTrapCount` restricted to the event that the forged point was *programmed at
counter value `j`* — is bounded by the **floor-free** per-target embedding win
`S (some j) = ∑' y, Pr[= y | $ᵗ Range] · Pr[win | embedTrapImpl … j y]`, with **no** budget /
reservoir factor.  This is the genuine deferred-sampling content of GPV Step-2: at the fixed slot
`j` the trap run's inline uniform winner draw `v⋆ ← $ᵗ Range` (drawn *inside* the `simulateQ` fold
at the adaptively-determined `j`-th programming step) must be pushed to the front and re-expressed
as the embedded target `y ← $ᵗ Range` (drawn *outside* the fold), mirroring
`evalSPMF_gpvRealImpl_eq_drawList_gpvRealImplTape`; the embedded slot is then `j` and the win event
couples to the trap run's write-only `table(forged) = trapdoorSample (cache(forged))`.

The budget-scaled form `reservoir_embed_commute_winner` follows from this by the reservoir floor
arithmetic (`probOutput_reservoirWinnerIndex_eq` at `j < qSign + qHash`, the recorded-index budget
`progGameRunImplCombinedTrapCount_idx_lt_budget` clearing the `j ≥ qSign + qHash` tail). -/
lemma reservoir_embed_commute_winner_floorFree [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (_hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (_hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (_hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) (j : ℕ) :
    Pr[fun w : (M × (Salt × Domain)) ×
          (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
            (((Salt × M) → Option ℕ) × ℕ)) =>
          ((decide (w.1.1 ∉ w.2.1.1.1.2) &&
              (decide (psf.eval pk w.1.2.2 =
                  (w.2.1.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                psf.isShort w.1.2.2)) = true ∧
            w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2) ∧
            w.2.2.1 (w.1.2.1, w.1.1) = some j |
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
          (adv.main pk)).run
          (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
            (fun _ => none), 0)]
      ≤ ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
            Pr[= true | (do
              let x ← psf.trapdoorSample pk sk y
              let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
                ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
              pure (decide (r.1.2.2 = x) &&
                decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] := by
  -- **The GPV Step-2 per-slot front-loading joint coupling.**
  --
  -- This is the deferred-sampling content.  The left mass lives on the
  -- counter-augmented trap run `progGameRunImplCombinedTrapCount`: at the *adaptively-determined*
  -- `j`-th programming step, an inline uniform winner image `v⋆ ← $ᵗ Range` is drawn *inside* the
  -- `simulateQ` fold, cached at the forged point, and the write-only trapdoor preimage
  -- `trapdoorSample (pk, sk) v⋆` is recorded.  The right mass averages the embedded target
  -- `y ← $ᵗ Range` *outside* the fold and runs `embedTrapImpl … j y`, which caches `y` at its
  -- count-`j` random-oracle miss and draws fresh uniform images everywhere else.
  --
  -- **Fold the `y`-average into a single front draw.** The right-hand `∑' y`
  -- weighted by `Pr[= y | $ᵗ Range]` is exactly the output probability of the bind that draws
  -- `y ← $ᵗ Range` first and then runs the per-target win game (`probOutput_bind_eq_tsum`).  This
  -- puts the right side in the *front-loaded* form `Pr[= true | y ← $ᵗ Range; …]`, matching the
  -- trap run's inline `v⋆ ← $ᵗ Range` up to the adaptive count-`j` position.
  rw [← probOutput_bind_eq_tsum]
  -- **The adaptive count-`j` front-loading, via the front-draw lift.**
  --
  -- The goal is now `LHS_trap ≤ Pr[= true | y ← $ᵗ Range; x ← trapdoorSample pk sk y;
  --   r ← (simulateQ (embedTrapImpl … j y) (adv.main pk)).run (∅, 0);
  --   pure (decide (r.1.2.2 = x) && decide (r.2.1 (forged) = some y))]`, i.e. both sides now carry
  -- a single `$ᵗ Range` draw: the trap run draws it *inline* at the adaptively-determined `j`-th
  -- programming step, the embed game draws it at the *front* (consumed at its count-`j` miss).
  --
  -- The adaptive PMF×PMF run coupling — pushing the trap run's inline winner draw
  -- `v⋆ ← $ᵗ Range` to the front and re-expressing it as the embedded target `y ← $ᵗ Range` across
  -- the whole adaptive fold — is
  -- `evalSPMF_frontDraw_embedTrapImpl_eq_embedTrapFresh`: averaging the trap-sibling embed run over
  -- the external target draw equals the inline-fresh run `embedTrapFreshImpl` (an all-fresh-uniform
  -- lazy random oracle with counter).  Its winner step substitutes the front `y` for the inline
  -- fresh winner draw and uses post-winner coincidence
  -- (`evalSPMF_run_embedTrapImpl_eq_embedTrapFresh_of_lt`); its off-winner steps commute the front
  -- draw past `y`-independent steps (`embedTrapImpl_run_step_eq_embedTrapFresh`,
  -- `OracleComp.DeferredSampling.evalSPMF_bind_comm`).
  --
  -- **The win-event same-randomness coupling.**
  --
  -- The lift couples the *run* (the cache/counter marginal), but the embed win event still reads
  -- the front target `y` directly — `r.2.1 (forged) = some y` and
  -- `r.1.2.2 = x ← trapdoorSample pk sk y` — so the lift cannot fire while `y` lives in the event.
  -- On the winner-slot support the cache *pins* `y`: at slot `j` the trap-sibling caches exactly
  -- `y`, so `r.2.1 (forged) = some y` forces `y = cache(forged)` and
  -- `x ← trapdoorSample pk sk (cache(forged))`.  Eliminating the explicit `y` via this cache-pin
  -- (a marginal over `y` tied to the cache value) puts the embed win in run-only form, after which
  -- the front-draw lift rewrites the run to `embedTrapFreshImpl` and the
  -- trap-count run is its trapdoor-table/index augmentation (the LHS handler
  -- `progGameRunImplCombinedTrapCount` draws the *same* fresh `v` and records
  -- `table(forged) = trapdoorSample pk sk v` with `idx(forged) = some j`).  Matching the trap event
  -- `table(forged) = trapdoorSample (cache(forged))` to the embed event `output = trapdoorSample
  -- (cache(forged))` is the final N4-style same-randomness coupling
  -- (`evalSPMF_simulateQ_run_congr` after projecting to the common
  -- `embedTrapFreshImpl` cache/counter state) and the trapdoor draw `x`.
  --
  -- **Commute the trapdoor draw `x` past the embed run.**  The trapdoor
  -- preimage `x ← trapdoorSample pk sk y` is drawn from an *independent* `ProbComp` (it does not
  -- feed the embed run `simulateQ (embedTrapImpl … j y)`, which consumes only `y`), so the two
  -- binds exchange at the distribution level (`OracleComp.DeferredSampling.evalSPMF_bind_comm`).
  -- Running the embed first and drawing `x` afterwards leaves the win event — and hence the output
  -- probability `Pr[= true | …]` — unchanged.  This re-expresses the right-hand game in the
  -- *run-first* form, in which the embed run output `r` is already available when the trapdoor draw
  -- `x` and the win predicate `decide (r.1.2.2 = x) && decide (r.2.1 (forged) = some y)` are
  -- evaluated.
  rw [show Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let x ← psf.trapdoorSample pk sk y
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)]
      = Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        let x ← psf.trapdoorSample pk sk y
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] from by
    refine probOutput_congr rfl ?_
    refine evalSPMF_bind_congr' _ (fun y => ?_)
    exact OracleComp.DeferredSampling.evalSPMF_bind_comm (psf.trapdoorSample pk sk y)
      ((simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run (∅, 0))
      (fun x r => pure (decide (r.1.2.2 = x) &&
        decide (r.2.1 (r.1.2.1, r.1.1) = some y)))]
  -- **Pin the trapdoor draw to the cached image at the forged point.**  The
  -- win predicate is `decide (r.1.2.2 = x) && decide (r.2.1 (forged) = some y)`; whenever its
  -- second conjunct holds the cached image at the forged point is exactly the front target,
  -- `r.2.1 (forged) = some y`, so `(r.2.1 (forged)).getD y = y` and the trapdoor preimage
  -- `x ← trapdoorSample pk sk y` equals `x ← trapdoorSample pk sk ((r.2.1 (forged)).getD y)`.
  -- When the second conjunct fails the whole `&&` is `false` regardless of `x`, so the trapdoor
  -- draw is irrelevant and either target yields the same (constant-`false`) win distribution.
  -- This pins the trapdoor draw to a *run-read* cache value — eliminating the free `y` from the
  -- trapdoor draw, leaving it only in the cache-comparison literal `some y`.
  rw [show Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        let x ← psf.trapdoorSample pk sk y
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)]
      = Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        let x ← psf.trapdoorSample pk sk ((r.2.1 (r.1.2.1, r.1.1)).getD y)
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] from by
    refine probOutput_congr rfl (evalSPMF_bind_congr' _ (fun y => ?_))
    refine evalSPMF_bind_congr' _ (fun r => ?_)
    rcases hc : r.2.1 (r.1.2.1, r.1.1) with _ | yv
    · simp only [Option.getD_none]
    · simp only [Option.getD_some]
      by_cases hy : yv = y
      · rw [hy]
      · simp only [Option.some.injEq, hy, decide_false, Bool.and_false]
        rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _
            ((hNF y).probFailure_eq_zero),
          OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _
            ((hNF yv).probFailure_eq_zero)]]
  -- **Index-augment the embed run and restrict the win to the winner slot.**
  -- The win predicate `decide (r.1.2.2 = x) && decide (r.2.1 (forged) = some y)` reads only the
  -- embed run *output* `r.1.2.2` and *cache* `r.2.1`, both of which are recovered from the
  -- index-augmented run `embedTrapIdxImpl … j y` by the passive projection
  -- `map_run_embedTrapIdxImpl_proj` (the inserted insertion-index table is never read).  Hence the
  -- right-hand win mass equals the same win mass on the augmented run, which dominates its
  -- restriction to the further conjunct `idx(forged) = some j` (the run-only winner-slot witness):
  --
  --   `RHS' := ∑'y Pr[=y] · Pr[= true | embedTrapIdxImpl … j y; x ← trapdoorSample (cache forged);
  --              pure (win ∧ idx(forged) = some j)]  ≤  RHS`.
  --
  -- This is the sound monotone reduction (`probOutput` over a conjoined Bool) that re-expresses the
  -- right side on the index-augmented run with the winner-slot restriction made explicit, so that
  -- the front target `y` enters only through run-only predicates (`idx(forged) = some j`) — exactly
  -- the form the trap-count run's `idx(forged) = some j` event couples to.
  refine le_trans ?_ (reservoir_embed_winnerIdx_le psf hr M Salt pk sk j adv)
  -- **The freshness-confined winner-slot coupling.**
  --
  -- Goal here (after the winner-idx monotone step `reservoir_embed_winnerIdx_le`):
  --   ⊢ Pr[fun w => ((fresh w.1.1 ∧ verify ∧ isShort) ∧ table(forged) = some w.1.2.2)
  --        ∧ idx(forged) = some j | (simulateQ progGameRunImplCombinedTrapCount (adv.main pk)).run]
  --     ≤ ∑'y Pr[= y | $ᵗ Range] ·
  --         Pr[= true | r ← (simulateQ (embedTrapIdxImpl … j y) (adv.main pk)).run ((∅, 0), ∅idx);
  --                     x ← trapdoorSample pk sk ((r.2.1.1 (forged)).getD y);
  --                     pure (decide (r.1.2.2 = x) && decide (r.2.1.1 (forged) = some y)
  --                            && decide (r.2.2 (forged) = some j))]
  --
  -- ⚠ The FRESHNESS conjunct `w.1.1 ∉ w.2.1.1.1.2` (`forged.msg ∉ signedSet`) is LOAD-BEARING and
  -- must NOT be dropped.  Dropping it makes the bound FALSE: both the trap run's signing branch
  -- (`progGameRunImplCombinedTrapCount_run_inr`) and the embed run's signing branch
  -- (`embedTrapIdxImpl_run_inr`) increment the counter and write the insertion-index table, but the
  -- embed's signing branch caches a *fresh* `c` (it never tests `j`), not the embedded `y`.  So a
  -- replay adversary making one signing query on `m` at counter `j`, receiving `(r, x =
  -- trapdoorSample c)` and outputting the forgery `(r, m, x)`, gives trap mass
  -- `table(forged) = some x ∧ idx(forged) = some j` with probability `1`, while the embed side
  -- needs the fresh `c = y` — a `1/|Range|` coincidence (witness: the bijective PSF, `j = 0`).
  --
  -- Route (freshness collapses the joint coupling to marginal + deterministic recovery): freshness
  -- ⟹ `forged.msg` was never signed ⟹ `forged` can only have been inserted by a random-oracle miss,
  -- at counter `j` (since `idx(forged) = some j`), where the embed caches exactly `y` — so on that
  -- slot the diagonal `cache(forged) = some y` is recovered from the run state, eliminating the
  -- free `y` from the embed win literal.  The marginal lift
  -- `evalSPMF_frontDraw_embedTrapIdxSigImpl_eq_embedTrapFreshSigImpl` then fires; the trap-count
  -- run is matched to `embedTrapFreshIdxSigImpl` by the freshness recovery
  -- `embedTrapIdxSigImpl_fresh_idx_cache_eq` and the write-only-table support invariant
  -- `progGameRunImplCombinedTrapCount_table_support`.  The omitted embed-side signing-slot mass on
  -- the right is nonnegative, so the bound is an inequality (trap ≤ embed), not an equality.
  --
  -- **The run-marginal half.** The cache/counter/idx/signedSet marginals of
  -- the trap-count run and the inline-fresh signed-set embed run coincide *as distributions*, via
  -- the generic `evalSPMF`-level state-projection transport
  -- `evalSPMF_map_run_simulateQ_eq_of_query_evalSPMF_map_eq` (which tolerates the never-failing
  -- answer-irrelevant trapdoor draw at each RO miss) instantiated as
  -- `map_run_progGameRunImplCombinedTrapCount_freshSig_proj`.  This discharges the *run-marginal*
  -- half of the coupling: it identifies the trap-count cache/idx/signedSet law with the
  -- `embedTrapFreshIdxSigImpl` law that the front-draw lift produces from
  -- `∑'y Pr[=y] · embedTrapIdxSigImpl … j y`.
  --
  -- **The table↔trapdoor-draw joint factorization.** On the
  -- trap run the forged point's write-only table entry `table(forged) = some preimg` was sampled
  -- `x ← trapdoorSample pk sk (cache(forged))` *inline* at the adaptively-determined forged
  -- programming event, and must be front-loaded to the embed side's *post-run* trapdoor draw
  -- `x ← trapdoorSample pk sk (cache(forged))`, matching the recorded `x` to the adversary output
  -- `preimg`.  FRESHNESS is exactly what makes this draw answer-irrelevant (an unsigned forged key
  -- is an RO miss, whose `x` enters only the write-only table — never the adversary view; a
  -- *signed* key returns `(r, x)` to the adversary, so its table draw is *not* deferrable, which is
  -- why dropping FRESH falsifies the bound).  Formalizing this defer-to-end of one
  -- answer-irrelevant write-only draw across the adaptive `simulateQ` fold is the genuine joint
  -- PMF×PMF coupling: a per-final-state induction (à la
  -- `tsum_probOutput_simulateQ_run_mul_of_rel`) showing the table at
  -- an unsigned key is an independent fresh `trapdoorSample (cache key)` conditioned on the final
  -- cache/idx/signedSet state, carried out in `trap_freshSig_le_winnerSlot_deferred`.
  --
  -- **Assembly.** Drop the verify/isShort conjuncts (they only restrict; FRESH stays) by
  -- `probEvent_mono`, then chain the trap-side table-defer
  -- `trap_freshSig_le_winnerSlot_deferred` (`G_trap ≤` the freshness-confined deferred functional
  -- expectation over the inline-fresh run) with the embed-side reduction
  -- `freshSig_winnerSlot_deferred_le_embed` (that expectation `≤` the winner-slot-restricted
  -- per-target embedding win).
  refine le_trans (probEvent_mono ?_)
    (le_trans (trap_freshSig_le_winnerSlot_deferred psf hr M Salt pk sk j adv hNF)
      (freshSig_winnerSlot_deferred_le_embed psf hr M Salt pk sk j adv))
  rintro w - ⟨⟨hflag, htbl⟩, hidx⟩
  refine ⟨⟨?_, htbl⟩, hidx⟩
  -- The flag conjunct `(decide fresh && (decide verify && isShort)) = true` carries the FRESH
  -- literal `forged.msg ∉ signedSet`, which is preserved verbatim.
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hflag
  exact hflag.1

open Classical in
omit [Fintype Salt] in
/-- **The per-slot front-loading deferred-sampling coupling (budget-scaled form).**

For a fixed programmed-entry index `j`, the *index-tagged* trap-exact-match mass — the trap event on
the counter-augmented run `progGameRunImplCombinedTrapCount` further restricted to the event that
the forged random-oracle point was *programmed at counter value `j`* (its recorded insertion index
is `some j`) — is bounded by the budget-scaled reservoir winner mass
`(qSign + qHash) · Pr[= some j | reservoirWinnerIndex (qSign + qHash)] · S (some j)` at slot `j`,
where `S (some j)` is the
winner-slot-restricted per-target embedding win of `embedTrapImpl … j y` averaged over `y ← $ᵗ
Range`.

This is derived from the floor-free form `reservoir_embed_commute_winner_floorFree` by the reservoir
arithmetic: at `j < qSign + qHash` the winner mass is exactly `(qSign + qHash)⁻¹`
(`probOutput_reservoirWinnerIndex_eq`), so `(qSign + qHash) · (qSign + qHash)⁻¹ = 1` absorbs the
budget factor and the floor-free bound passes through; at `j ≥ qSign + qHash` no programmed entry
can have recorded index `j` (`progGameRunImplCombinedTrapCount_idx_lt_budget`), so the left mass is
`0`.  The multi-target factor `qSign + qHash` pays the guessing loss. -/
lemma reservoir_embed_commute_winner [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) (j : ℕ) :
    Pr[fun w : (M × (Salt × Domain)) ×
          (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
            (((Salt × M) → Option ℕ) × ℕ)) =>
          ((decide (w.1.1 ∉ w.2.1.1.1.2) &&
              (decide (psf.eval pk w.1.2.2 =
                  (w.2.1.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                psf.isShort w.1.2.2)) = true ∧
            w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2) ∧
            w.2.2.1 (w.1.2.1, w.1.1) = some j |
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
          (adv.main pk)).run
          (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
            (fun _ => none), 0)]
      ≤ ((qSign + qHash : ℕ) : ENNReal) *
        Pr[= some j | reservoirWinnerIndex (qSign + qHash)] *
          ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
            Pr[= true | (do
              let x ← psf.trapdoorSample pk sk y
              let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
                ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
              pure (decide (r.1.2.2 = x) &&
                decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] := by
  set Q := qSign + qHash with hQdef
  set S : ENNReal := ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
      Pr[= true | (do
        let x ← psf.trapdoorSample pk sk y
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] with hSdef
  set LHS : ENNReal := Pr[fun w : (M × (Salt × Domain)) ×
        (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
          (((Salt × M) → Option ℕ) × ℕ)) =>
        ((decide (w.1.1 ∉ w.2.1.1.1.2) &&
            (decide (psf.eval pk w.1.2.2 =
                (w.2.1.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
              psf.isShort w.1.2.2)) = true ∧
          w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2) ∧
          w.2.2.1 (w.1.2.1, w.1.1) = some j |
      (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
        (adv.main pk)).run
        (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
          (fun _ => none), 0)] with hLHSdef
  -- Floor-free per-slot bound (the genuine front-loading commute).
  have hfloorFree : LHS ≤ S :=
    reservoir_embed_commute_winner_floorFree psf hr M Salt domainSample pk sk qSign qHash adv
      hreg hNF hForge hQ j
  change LHS ≤ (Q : ENNReal) * Pr[= some j | reservoirWinnerIndex Q] * S
  by_cases hj : j < Q
  · -- Slot `j` is within budget: the winner mass is exactly `Q⁻¹`, so `Q · Q⁻¹ = 1` absorbs the
    -- budget factor and the floor-free bound passes through.
    have hres : Pr[= some j | reservoirWinnerIndex Q] = (Q : ℝ≥0∞)⁻¹ :=
      probOutput_reservoirWinnerIndex_eq Q j hj
    rw [hres]
    have hQne : (Q : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; omega
    have hQtop : (Q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top Q
    rw [ENNReal.mul_inv_cancel hQne hQtop, one_mul]
    exact hfloorFree
  · -- Slot `j` is beyond budget: no programmed entry has recorded index `j`, so `LHS = 0`.
    have hLHS0 : LHS = 0 := by
      rw [hLHSdef]
      refine probEvent_eq_zero ?_
      intro w hmem hP
      have hidxlt := progGameRunImplCombinedTrapCount_idx_lt_budget psf M Salt pk sk qSign qHash
        (adv.main pk) hQ hmem hP.2
      omega
    rw [hLHS0]
    exact zero_le

open Classical in
omit [Fintype Salt] in
/-- **M3, index-restricted: the reservoir↔embedding coupling (single fold-commute core).**

This is the deferred-sampling coupling of the GPV Step-2 exact-match close, with the
winner-slot bookkeeping made explicit: the per-target embedding win on the right is *restricted* to
the event that the **forged random-oracle point is the embedded (winner) slot**, read off the embed
final state as `r.2.1 (r.1.2.1, r.1.1) = some y` — at slot `wOpt.getD (qSign + qHash)` the
trap-sibling handler `embedTrapImpl` caches exactly the external target `y` at the winner
random-oracle miss, so the forged point being the winner slot is precisely its cached image being
`y`.

`reservoir_embed_commute` (M3) follows from this restricted form by dropping the winner-slot
restriction (`probOutput` monotonicity over the conjoined Bool): the *full* per-target win is at
least the winner-slot-restricted win, so the M3 bound is implied by the present, tighter bound.
Stating the restriction here lets the reservoir arithmetic (`probOutput_reservoirWinnerIndex_ge`,
the budget `N ≤ qSign + qHash` of `embedAtIndexImpl_run_count_le_budget` /
`combined_run_table_card_le`) be carried at the index-tagged level, while the per-winner-slot
front-loading joint coupling — pushing the trap run's inline winner draw `v⋆ ← $ᵗ Range` to the
front and re-expressing it as the embedded target `y ← $ᵗ Range` (mirroring
`evalSPMF_gpvRealImpl_eq_drawList_gpvRealImplTape`), together with the realized-entry index
partition of the trap mass — is supplied by `reservoir_embed_commute_winner`.

The bound holds for the same reason as M3: after the write-only-table deferral both runs maintain an
all-uniform random-oracle cache, and *averaging* the embedded target `y` over `$ᵗ Range`
reconstitutes the trap run's inline uniform winner draw `v⋆`.  The winner-slot-equals-forged-slot
contribution, summed over the `N ≤ qSign + qHash` realized programmed entries with per-slot
reservoir mass `1 / N ≥ 1 / (qSign + qHash)` and multiplied by `qSign + qHash`, already recovers the
full trap mass.  Trap-side index bookkeeping and the per-slot fold-commute supply the remaining
content. -/
lemma reservoir_embed_commute_residual [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[fun w : (M × (Salt × Domain)) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
          (decide (w.1.1 ∉ w.2.1.1.2) &&
              (decide (psf.eval pk w.1.2.2 =
                  (w.2.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                psf.isShort w.1.2.2)) = true ∧
            w.2.2 (w.1.2.1, w.1.1) = some w.1.2.2 |
        (simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk)
          (adv.main pk)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ ((qSign + qHash : ℕ) : ENNReal) *
        ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
          ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
            Pr[= true | (do
              let x ← psf.trapdoorSample pk sk y
              let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
                  (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
                ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
              pure (decide (r.1.2.2 = x) &&
                decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] := by
  -- Abbreviations: `Q` the multi-target budget, `S wOpt` the per-slot averaged restricted embedding
  -- win, `trap` the LHS trap-exact-match mass.
  set Q := qSign + qHash with hQdef
  set S : Option ℕ → ENNReal := fun wOpt =>
    ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
      Pr[= true | (do
        let x ← psf.trapdoorSample pk sk y
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk (wOpt.getD Q) y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] with hSdef
  set trap : ENNReal := Pr[fun w : (M × (Salt × Domain)) ×
        ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
        (decide (w.1.1 ∉ w.2.1.1.2) &&
            (decide (psf.eval pk w.1.2.2 =
                (w.2.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
              psf.isShort w.1.2.2)) = true ∧
          w.2.2 (w.1.2.1, w.1.1) = some w.1.2.2 |
      (simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk)
        (adv.main pk)).run
        ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
    with htrapdef
  change trap ≤ (Q : ENNReal) * ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex Q] * S wOpt
  -- **Per-slot index partition + commute.**  The per-entry mass function `g : ℕ → ENNReal` is the
  -- index-tagged trap-exact-match mass on the counter-augmented run
  -- `progGameRunImplCombinedTrapCount`, restricted to the event that the forged point was
  -- programmed at counter value `j`.  Summing `g j` over `j` recovers the full trap mass: the
  -- instrument is passive (`map_run_progGameRunImplCombinedTrapCount_proj`), so the augmented
  -- trap-event mass equals `trap`; and on every positive-probability trap outcome the forged
  -- point — being in the preimage table — has a recorded insertion index
  -- (`progGameRunImplCombinedTrapCount_idx_iff_table`), so the deterministic-index partition
  -- (`probEvent_eq_tsum_probEvent_index_aux`) tiles the trap mass over the recorded indices.  The
  -- per-slot domination `g j ≤ Q · Pr[= some j] · S` is the per-slot front-loading commute
  -- (`reservoir_embed_commute_winner`).
  obtain ⟨g, hgsum, hgle⟩ : ∃ g : ℕ → ENNReal,
      (∑' j : ℕ, g j) = trap ∧
      ∀ j : ℕ, g j ≤ (Q : ENNReal) * Pr[= some j | reservoirWinnerIndex Q] * S (some j) := by
    -- The counter-augmented run started from the projected empty state.
    set augRun := (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
        (adv.main pk)).run
        (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
          (fun _ => none), 0) with hAugRun
    -- The trap event lifted to the augmented state (referencing only the trap-state component).
    set Paug : (M × (Salt × Domain)) ×
        (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
          (((Salt × M) → Option ℕ) × ℕ)) → Prop := fun w =>
        (decide (w.1.1 ∉ w.2.1.1.1.2) &&
            (decide (psf.eval pk w.1.2.2 =
                (w.2.1.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
              psf.isShort w.1.2.2)) = true ∧
          w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2 with hPaug
    -- The forged-point recorded insertion index, read off the augmented final state.
    set idx : (M × (Salt × Domain)) ×
        (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
          (((Salt × M) → Option ℕ) × ℕ)) → Option ℕ := fun w =>
        w.2.2.1 (w.1.2.1, w.1.1) with hIdx
    refine ⟨fun j => Pr[fun w => Paug w ∧ idx w = some j | augRun], ?_, ?_⟩
    · -- Partition: `∑' j, g j = trap`.
      -- The augmentation is passive, so the augmented trap-event mass equals `trap`.
      have htrap_eq : trap = Pr[Paug | augRun] := by
        rw [htrapdef, ← map_run_progGameRunImplCombinedTrapCount_proj psf M Salt pk sk
          (adv.main pk) (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
            fun _ => none), (fun _ => none), 0), probEvent_map]
        rfl
      rw [htrap_eq]
      -- Every positive-probability trap outcome has a recorded forged-point index.
      refine (probEvent_eq_tsum_probEvent_index_aux augRun Paug idx ?_).symm
      intro w hw hPw
      have hmem : w ∈ support augRun := by
        by_contra hns
        exact hw (probOutput_eq_zero_of_not_mem_support hns)
      have hinv := progGameRunImplCombinedTrapCount_idx_iff_table psf M Salt pk sk
        (adv.main pk) (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
          fun _ => none), (fun _ => none), 0) (by intro k; simp) w hmem (w.1.2.1, w.1.1)
      rw [hIdx]
      exact (hinv.mp (by rw [hPaug] at hPw; rw [hPw.2]; exact Option.some_ne_none _))
    · -- Per-slot domination: the per-slot front-loading commute.
      intro j
      exact reservoir_embed_commute_winner psf hr M Salt domainSample pk sk qSign qHash
        adv hreg hNF hForge hQ j
  -- **Reservoir arithmetic.**  Push the budget factor `Q` through the winner sum and bound
  -- the trap partition `g` by the `some j` atoms of the reservoir winner average, discarding the
  -- never-firing `none` atom (`tsum_option`, terms nonnegative).
  calc trap = ∑' j : ℕ, g j := hgsum.symm
    _ ≤ ∑' j : ℕ, (Q : ENNReal) * Pr[= some j | reservoirWinnerIndex Q] * S (some j) :=
        ENNReal.tsum_le_tsum hgle
    _ = ∑' j : ℕ, (Q : ENNReal) * (Pr[= some j | reservoirWinnerIndex Q] * S (some j)) := by
        simp_rw [mul_assoc]
    _ ≤ (Q : ENNReal) *
        ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex Q] * S wOpt := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        rw [tsum_option _ ENNReal.summable]
        exact le_add_self

open Classical in
omit [Fintype Salt] in
/-- **M3 — the GPV Step-2 reservoir↔embedding deferred-sampling coupling.**

This is the joint coupling of the GPV Step-2 exact-match close, stated as the
*bound* needed by `gpv_perKey_exactMatch_le_reservoir`.  The left-hand side is the exact-match
winning mass of the trapdoor-recording combined run `progGameRunImplCombinedTrap` — the run obtained
from the combined sign-then-hash game after the write-only-table deferral (Lemma A,
`evalSPMF_run_progGameRunImplCombinedTrap_eq`).  The right-hand side is the multi-target factor
`qSign + qHash` times the full programmed-preimage reduction win, averaged over the reservoir winner
slot `wOpt ← reservoirWinnerIndex (qSign + qHash)` and the uniform target `y ← $ᵗ Range`: for each
slot/target the reduction runs the adversary under the all-uniform-cache trap-sibling embedding
handler `embedTrapImpl … (wOpt.getD (qSign + qHash)) y`, embeds the external challenge `y` at slot
`wOpt`, and wins when its forged preimage `r.1.2.2` equals the challenger's trapdoor preimage
`x ← trapdoorSample pk sk y`.

The bound holds because, after the write-only-table deferral, both runs maintain an all-uniform
random-oracle cache, and *averaging* the embedded target `y` over `$ᵗ Range` reconstitutes the
trap run's inline uniform winner draw `v⋆ ← $ᵗ Range`; the trap run's write-only
`table(forged) = trapdoorSample (cache(forged))` is then an independent fresh preimage that couples
to the reduction's external `x ~ trapdoorSample y` exactly when the winner slot is the forged point
(`cache(forged) = v⋆ ≡ y`).  The winner-slot-equals-forged-slot contribution, summed over the `N`
realized programmed entries with per-slot reservoir mass `1 / N` and multiplied by `qSign + qHash`
(with `N ≤ qSign + qHash`, `combined_run_table_card_le`), already recovers the full trap mass; the
reduction wins on *additional* coincidence paths (the forged slot differs from the embedded slot yet
its cached image coincides with `y`), so the inequality is one-directional (`≤`), not an equality.
The form is correct at `qSign + qHash = 0` (both sides vanish: no programmed entry is recorded, so
the trap mass is zero).

This is the deferred-sampling coupling where the `y`-draw lives *outside* the
`simulateQ` fold while `v⋆` lives *inside* it at an adaptively-determined fold position; the
front-loading joint-coupling is the core content of the GPV Step-2 close. -/
lemma reservoir_embed_commute [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[fun w : (M × (Salt × Domain)) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
          (decide (w.1.1 ∉ w.2.1.1.2) &&
              (decide (psf.eval pk w.1.2.2 =
                  (w.2.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                psf.isShort w.1.2.2)) = true ∧
            w.2.2 (w.1.2.1, w.1.1) = some w.1.2.2 |
        (simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk)
          (adv.main pk)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ ((qSign + qHash : ℕ) : ENNReal) *
        ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
          ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
            Pr[= true | (do
              let x ← psf.trapdoorSample pk sk y
              let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
                  (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
                ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
              pure (decide (r.1.2.2 = x)) : ProbComp Bool)] := by
  -- M3 from the index-restricted form: bound the trap mass by the winner-slot-restricted RHS
  -- (`reservoir_embed_commute_residual`), then drop the winner-slot restriction
  -- `&& decide (… = some y)` from every per-target win (full win ≥ the restricted win).
  refine le_trans (reservoir_embed_commute_residual psf hr M Salt domainSample pk sk qSign qHash
    adv hreg hNF hForge hQ) ?_
  gcongr ((qSign + qHash : ℕ) : ENNReal) *
    ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
      ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] * ?_ with wOpt y
  -- Per-target: dropping the conjunct `decide (r.2.1 (r.1.2.1, r.1.1) = some y)` only increases
  -- the winning mass (`probOutput` monotone over the conjoined Bool body).
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun x => ?_
  gcongr
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun r => ?_
  gcongr
  rw [probOutput_pure, probOutput_pure]
  by_cases hxr : r.1.2.2 = x
  · simp only [hxr, decide_true, Bool.true_and]
    split <;> simp
  · simp [hxr]

open Classical in
omit [Fintype Salt] in
/-- **Exact-match reservoir bound (Step-2 exact-match branch).** The exact-match winning mass on the
combined verify-extended run — a verifying fresh forgery `(msg, (r, s⋆))` whose forged preimage `s⋆`
exactly reproduces the simulator's hidden programmed preimage `sHidden` recorded in the table at the
forged point — is bounded by the multi-target factor `qSign + qHash` times the exact-match
programmed preimage advantage of `programmedPreimageReduction` at `(pk, sk)`.

The programmed-preimage reduction embeds its uniform target `y` at one uniformly chosen programmed
entry (reservoir sampling over the at most `qSign + qHash` programmed random-oracle entries); when
the embedded entry is the forged point and the forgery reproduces the hidden preimage, it wins the
single-target programmed-preimage experiment, paying the explicit `qSign + qHash` guessing loss.

This is the exact-match branch of the GPV Step-2 collision extraction; the
distinct-preimage branch is discharged by `gpv_perKey_distinct_le_collision`. -/
lemma gpv_perKey_exactMatch_le_reservoir [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[fun w : ((M × (Salt × Domain)) × Bool) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
            (decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) = some w.1.1.2.2 |
        (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
          (adv.main pk >>= fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ ((qSign + qHash : ℕ) : ENNReal) *
        Pr[= true | (do
          let y ← ($ᵗ Range : ProbComp Range)
          let x ← psf.trapdoorSample pk sk y
          let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y
          pure (decide (x' = x)) : ProbComp Bool)] := by
  -- **Step A (verify-strip, reduction-agnostic).**  Strip the verify continuation: on the forced
  -- cache hit at the forged point the verification read is table-passive, so the verify-extended
  -- exact-match mass is bounded by the exact-match event on `adv.main pk`'s combined run alone.
  refine le_trans
    (gpv_perKey_exactMatch_verifyStrip_le psf hr M Salt domainSample pk adv hForge) ?_
  -- **Step B (target factorization).**  Expand the reduction's averaged exact-match advantage over
  -- the uniform target draw `y ← $ᵗ Range` and push the `(qSign + qHash)` factor inside the sum, so
  -- the goal becomes the verify-stripped LHS bounded by
  --   `∑' y, (qSign + qHash) * (Pr[= y | $ᵗ Range] * Pr[per-y exact-match win])`.
  rw [programmedPreimage_perKey_eq_tsum psf hr M Salt domainSample pk sk qSign qHash adv,
    ← ENNReal.tsum_mul_left]
  -- **N4 rewrite.**  Inside every per-target factor `P_y`, replace the pre-sampled-index
  -- handler `embedAtIndexImpl` by its trapdoor-uniform sibling `embedTrapImpl` (N4); after this the
  -- embed run has an all-uniform cache (modulo `y` at the winner slot), matching the cache marginal
  -- of the trapdoor-recording combined run.
  have hN4 : ∀ y : Range,
      Pr[= true | (do
        let x ← psf.trapdoorSample pk sk y
        let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y
        pure (decide (x' = x)) : ProbComp Bool)]
      = Pr[= true | (do
          let x ← psf.trapdoorSample pk sk y
          let wOpt ← reservoirWinnerIndex (qSign + qHash)
          let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
              (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
            ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
          pure (decide (r.1.2.2 = x)) : ProbComp Bool)] := by
    intro y
    refine probOutput_congr rfl ?_
    simp only [programmedPreimageReduction_eq_run, bind_assoc, pure_bind]
    refine evalSPMF_bind_congr fun x _ => ?_
    refine evalSPMF_bind_congr fun wOpt _ => ?_
    -- The remaining `run >>= pure ∘ decide` factor is equidistributed under N4.
    rw [evalSPMF_bind, evalSPMF_bind,
      evalSPMF_run_embedAtIndexImpl_eq_embedTrap psf M Salt domainSample pk sk
        (wOpt.getD (qSign + qHash)) y hreg hNF (adv.main pk)
        ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))]
  -- **N4 applied.**  Replace every per-target embed run by its all-uniform-cache trap
  -- sibling `embedTrapImpl`, so the goal RHS is the reservoir/target average of the *trap-sibling*
  -- embedding run, matching the cache marginal of the trapdoor-recording combined run.
  simp only [hN4]
  -- **M1 (Lemma A — write-only-table deferral).**  Push the verify-stripped LHS exact-match mass
  -- off the eval-caching combined run `progGameRunImplCombined` onto its trapdoor-recording sibling
  -- `progGameRunImplCombinedTrap`, an exact equidistribution under `hreg` with the event unchanged.
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalSPMF_run_progGameRunImplCombinedTrap_eq psf M Salt domainSample pk sk hreg (adv.main pk)
      ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none))]
  -- **M4 (assembly).**  Pull the reservoir winner draw `wOpt` to the front of each per-target win,
  -- swap the target/reservoir averages, fold in the multi-target factor, and discharge the result
  -- against the reservoir↔embedding coupling `reservoir_embed_commute` (M3).
  have hpull : ∀ i : Range,
      Pr[= true | (do
        let x ← psf.trapdoorSample pk sk i
        let wOpt ← reservoirWinnerIndex (qSign + qHash)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
            (wOpt.getD (qSign + qHash)) i) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure (decide (r.1.2.2 = x)) : ProbComp Bool)]
      = ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
        Pr[= true | (do
          let x ← psf.trapdoorSample pk sk i
          let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
              (wOpt.getD (qSign + qHash)) i) (adv.main pk)).run
            ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
          pure (decide (r.1.2.2 = x)) : ProbComp Bool)] := by
    intro i
    rw [probOutput_bind_eq_tsum]
    simp_rw [probOutput_bind_eq_tsum (reservoirWinnerIndex (qSign + qHash)),
      probOutput_bind_eq_tsum (psf.trapdoorSample pk sk i), ← ENNReal.tsum_mul_left, ← mul_assoc]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun wOpt => tsum_congr fun x => by ring
  -- Reassociate the per-target sum into the multi-target factor times the reservoir/target average
  -- that `reservoir_embed_commute` equates to the trap exact-match mass.
  have hrhs :
      (∑' i : Range, ((qSign + qHash : ℕ) : ENNReal) *
          (Pr[= i | ($ᵗ Range : ProbComp Range)] *
            ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
              Pr[= true | (do
                let x ← psf.trapdoorSample pk sk i
                let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
                    (wOpt.getD (qSign + qHash)) i) (adv.main pk)).run
                  ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
                pure (decide (r.1.2.2 = x)) : ProbComp Bool)]))
        = ((qSign + qHash : ℕ) : ENNReal) *
          ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
            ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
              Pr[= true | (do
                let x ← psf.trapdoorSample pk sk y
                let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
                    (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
                  ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
                pure (decide (r.1.2.2 = x)) : ProbComp Bool)] := by
    rw [← ENNReal.tsum_mul_left]
    simp_rw [← ENNReal.tsum_mul_left, ← mul_assoc]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun wOpt => tsum_congr fun y => by ring
  simp_rw [hpull]
  rw [hrhs]
  exact reservoir_embed_commute psf hr M Salt domainSample pk sk qSign qHash adv hreg hNF
    hForge hQ

end GPVHashAndSign
