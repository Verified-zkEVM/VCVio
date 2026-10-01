/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import ToMathlib.Data.ENNReal.SumSquares
public import VCVio.OracleComp.QueryTracking.CostModel
public import VCVio.ProgramLogic.Unary.HoareTriple
public import VCVio.OracleComp.QueryTracking.SeededOracle

import VCVio.OracleComp.Coercions.SubSpec.Measure

/-!
# Seed-Based Forking Lemma (Bellare-Neven)

The forking lemma is a key tool in provable security. The *seeded* variant in this file
(`seededFork`) mechanizes the original Bellare-Neven construction (CCS 2006): pre-sample every
oracle response into a `QuerySeed`, run the adversary deterministically against that seed, then
re-run it against a seed that has been modified at the chosen fork point.

`seededFork` returns `OracleComp spec (Option (α × α))` with explicit matching on
success/failure. The seeded replay uses `seededOracle` via `StateT`, and `generateSeed`
produces the initial seed as a `ProbComp` lifted into `spec`.

The companion file `VCVio/CryptoFoundations/ReplayFork.lean` provides the *replay* variant,
which only pre-samples the forked oracle family and answers ambient randomness live; it is the
natural choice for reductions like Fiat-Shamir EUF-CMA whose adversaries make both kinds of
queries.

## Main definitions

* `seededFork`: the forking operation, sampling a seed and a fresh answer at the fork point.
* `seededForkWithSeedValue`: the same operation with the seed and forked answer fixed in advance.

## Main results

* `isPerIndexQueryBound_seededForkWithSeedValue`: the fork respects the per-index query bound.
* `expectedQueryCount_seededForkWithSeedValue_le`: the fork's expected query count is bounded.
* `seededForkExpectedQueryWork_le`: the total expected work of the fork is bounded.
* `le_prEvent_seededFork`: the core lower bound on the success event at a fixed fork point.
* `le_prEvent_isSome_seededFork` and `le_prEvent_isSome_seededFork_sq`: the Bellare-Neven
  forking bound, the latter in its canonical `acc² / q - acc / h` shape.

The bounds are stated with `Pr{…}` events of the output measures. The seed-averaged run has the
distribution of `main`, truncating the seed keeps the joint law of the prefix and the output, and
the squared success probability is bounded by the two-run event through Jensen's inequality over
the truncated seed.

## References

* M. Bellare and G. Neven, *Multi-Signatures in the Plain Public-Key Model and a General
  Forking Lemma*, CCS 2006.
-/

@[expose] public section

open OracleSpec OracleComp OracleComp.ProgramLogic ENNReal Function Finset
open scoped OracleComp.Lower

namespace OracleComp

/-! ## Preliminaries independent of index decidability -/

/-- The standard forking-lemma precondition is itself a valid probability bound. -/
theorem seededFork_precondition_le_one {ι : Type} {spec : OracleSpec ι}
    [OracleSpec.AnswerMeasure spec] {α : Type} (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    [Fintype (spec.Range i)] (cf : α → Option (Fin (qb i + 1))) :
    (let acc : ℝ≥0∞ := ∑ s, Pr{let x ← main}[cf x = some s]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤ 1 :=
  ENNReal.mul_tsub_div_le_one (sum_prEvent_eq_some_le_one main cf) (by simp)

/-- Guessing a seeded answer with a fresh uniform answer succeeds with probability at most
`|spec.Range i|⁻¹`. -/
private lemma prEvent_seedSlot_le_inv {ι : Type} {spec : OracleSpec ι}
    [∀ i, SampleableType (spec.Range i)] [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec]
    [OracleSpec.UniformAnswerMeasure spec] (qb : ι → ℕ) (i : ι) [Fintype (spec.Range i)]
    (s : Fin (qb i + 1)) (seed : QuerySeed spec) :
    Pr{let u ← liftComp ($ᵗ spec.Range i) spec}[(seed i)[s]? = some u] ≤
      (Fintype.card (spec.Range i) : ℝ≥0∞)⁻¹ := by
  rw [(evalDistEq_liftComp_uniform ($ᵗ spec.Range i)).prEvent_eq]
  rcases hslot : (seed i)[s]? with _ | u₀
  · simp
  · rw [prEvent_congr _ _ (· = u₀) fun u => by simp [eq_comm]]
    exact (SampleableType.prEvent_uniformSample_eq_singleton u₀).le

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α β γ : Type}

section forkDef

variable [∀ i, SampleableType (spec.Range i)] [∀ i, DecidableEq (spec.Range i)]
  [unifSpec ⊂ₒ spec]

/-- The forking operation: run `main` with a random seed, then re-run it with the seed modified
at the `s`-th query to oracle `i` (where `s = cf x₁`), checking that both runs agree on `cf`.

Returns `none` (failure) when:
- `cf x₁ = none` (adversary did not choose a fork point)
- the re-sampled oracle response equals the original (no useful fork)
- `cf x₂ ≠ cf x₁` (the second run chose a different fork point) -/
def seededFork (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) : OracleComp spec (Option (α × α)) := do
  let seed ← liftComp (generateSeed spec qb js) spec
  let x₁ ← (simulateQ seededOracle main).run' seed
  match cf x₁ with
  | none => return none
  | some s =>
    let u ← liftComp ($ᵗ spec.Range i) spec
    -- `seed' := take s ++ [u]` replaces the value at index `s` (0-based) when present.
    -- The collision guard must compare against that same index.
    if (seed i)[↑s]? = some u then
      return none
    else
      let seed' := (seed.takeAtIndex i ↑s).addValue i u
      let x₂ ← (simulateQ seededOracle main).run' seed'
      if cf x₂ = some s then
        return some (x₁, x₂)
      else
        return none

/-- The deterministic core of `seededFork` with the random seed and replacement value already fixed.

Runs `main` once against `seed`, checks whether the fork-index selector `cf` fires, and if so
replays `main` against a modified seed where the `(cf x₁)`-th answer to oracle `i` is replaced
by `u`. Returns the pair `(x₁, x₂)` when both runs agree on the fork index.

The only remaining randomness comes from `main`'s own oracle queries that fall outside the
seed (i.e. queries beyond the budget `qb`). -/
def seededForkWithSeedValue (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (seed : QuerySeed spec) (u : spec.Range i) :
    OracleComp spec (Option (α × α)) := do
  let x₁ ← (simulateQ seededOracle main).run' seed
  match cf x₁ with
  | none => return none
  | some s =>
    if (seed i)[↑s]? = some u then
      return none
    else
      let seed' := (seed.takeAtIndex i ↑s).addValue i u
      let x₂ ← (simulateQ seededOracle main).run' seed'
      if cf x₂ = some s then
        return some (x₁, x₂)
      else
        return none

end forkDef

/-- When the seed has at least `qb t` pre-generated answers for each oracle `t`, running `main`
against the seed makes zero live oracle queries (every query is answered from the seed). -/
theorem isPerIndexQueryBound_seededOracle_run'_zero (main : OracleComp spec α) (qb : ι → ℕ)
    {seed : QuerySeed spec} (hmain : IsPerIndexQueryBound main qb)
    (hseed : ∀ t, qb t ≤ (seed t).length) :
    IsPerIndexQueryBound ((simulateQ seededOracle main).run' seed) 0 :=
  seededOracle.isPerIndexQueryBound_run'_zero hmain hseed

/-- After truncating the seed at query index `s` for oracle `i` and inserting a fresh answer `u`,
the replayed run can make at most `qb i - (s + 1)` live queries, all to oracle `i`.
All other oracle families remain fully covered by the seed. -/
theorem isPerIndexQueryBound_seededOracle_run'_takeAtIndex_addValue
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    {seed : QuerySeed spec} {u : spec.Range i} (hmain : IsPerIndexQueryBound main qb)
    (hseed : ∀ t, qb t ≤ (seed t).length) (s : Fin (qb i + 1)) :
    IsPerIndexQueryBound
      ((simulateQ seededOracle main).run' ((seed.takeAtIndex i ↑s).addValue i u))
      (Function.update 0 i (qb i - (↑s + 1))) :=
  seededOracle.isPerIndexQueryBound_run'_takeAtIndex_addValue hmain hseed s u

private lemma isPerIndexQueryBound_if_pure {p : Prop} [Decidable p] {oa : OracleComp spec α}
    {qb : ι → ℕ} {x : α} (h : IsPerIndexQueryBound oa qb) :
    IsPerIndexQueryBound (if p then pure x else oa) qb := by
  split <;> simp [h]

private lemma isPerIndexQueryBound_seededForkWithSeedValue_replayGuard
    [∀ i, DecidableEq (spec.Range i)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    {seed : QuerySeed spec} {u : spec.Range i} (hmain : IsPerIndexQueryBound main qb)
    (hseed : ∀ t, qb t ≤ (seed t).length) (x₁ : α) (s : Fin (qb i + 1)) :
    IsPerIndexQueryBound
      (if (seed i)[↑s]? = some u then
          (pure none : OracleComp spec (Option (α × α)))
        else
          (((simulateQ seededOracle main).run' ((seed.takeAtIndex i ↑s).addValue i u)) >>=
            fun x₂ => if cf x₂ = some s then pure (some (x₁, x₂)) else pure none))
      (Function.update 0 i (qb i)) := by
  have hreplay :
      IsPerIndexQueryBound
        ((simulateQ seededOracle main).run' ((seed.takeAtIndex i ↑s).addValue i u))
        (Function.update 0 i (qb i)) :=
    (isPerIndexQueryBound_seededOracle_run'_takeAtIndex_addValue (main := main) (qb := qb) (i := i)
        (seed := seed) (u := u) hmain hseed s).mono fun j => by
      by_cases hj : j = i <;> simp [Function.update, hj]
  have hpost : ∀ x₂ : α,
      IsPerIndexQueryBound
        (if cf x₂ = some s then (pure (some (x₁, x₂)) : OracleComp spec (Option (α × α)))
          else pure none) 0 :=
    fun x₂ => by by_cases hx₂ : cf x₂ = some s <;> simp [hx₂]
  exact isPerIndexQueryBound_if_pure (x := (none : Option (α × α)))
    (isPerIndexQueryBound_bind hreplay hpost)

/-- `seededForkWithSeedValue` makes at most `qb i` live queries, all to oracle `i`.

The first seeded run is query-free (covered by the seed); the replay after the fork point uses
at most the remaining `i`-budget. The bound holds regardless of which fork index `cf` returns. -/
theorem isPerIndexQueryBound_seededForkWithSeedValue
    [∀ i, DecidableEq (spec.Range i)] (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) {seed : QuerySeed spec} {u : spec.Range i}
    (hmain : IsPerIndexQueryBound main qb) (hseed : ∀ t, qb t ≤ (seed t).length) :
    IsPerIndexQueryBound (seededForkWithSeedValue main qb i cf seed u)
      (Function.update 0 i (qb i)) := by
  have hfirst :
      IsPerIndexQueryBound ((simulateQ seededOracle main).run' seed) 0 :=
    isPerIndexQueryBound_seededOracle_run'_zero (main := main) (qb := qb) hmain hseed
  rw [seededForkWithSeedValue, ← zero_add (Function.update (0 : QueryCount ι) i (qb i))]
  refine isPerIndexQueryBound_bind hfirst fun x₁ => ?_
  cases hcf : cf x₁ with
  | none => exact isPerIndexQueryBound_pure _ _
  | some s =>
      exact isPerIndexQueryBound_seededForkWithSeedValue_replayGuard
        (main := main) (qb := qb) (i := i) (cf := cf) (seed := seed) (u := u) hmain hseed x₁ s

section generateSeedCoverage

variable [∀ i, SampleableType (spec.Range i)]
variable [OracleSpec.AnswerMeasure spec]

private lemma expectedQueryCount_seededForkWithSeedValue_le_aux
    [∀ i, DecidableEq (spec.Range i)] [Finite ι]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) {seed : QuerySeed spec}
    (hmain : IsPerIndexQueryBound main qb) (hseed : ∀ t, qb t ≤ (seed t).length) :
    wp⟦$ᵗ spec.Range i⟧ (fun u => expectedCost (seededForkWithSeedValue main qb i cf seed u)
      CostModel.unit (fun n : ℕ => (n : ENNReal))) ≤ qb i := by
  let : Fintype ι := Fintype.ofFinite ι
  rw [← ExpectationWP.wp_const_of_oracle ($ᵗ spec.Range i) (qb i : ENNReal)]
  refine wp_mono _ fun u => ?_
  have hbound := isPerIndexQueryBound_seededForkWithSeedValue
    (main := main) (qb := qb) (i := i) (cf := cf) (u := u) hmain hseed
  simpa [ExpectedCostBound, Finset.sum_update_of_mem (Finset.mem_univ i)] using
    (WorstCaseCostBound.toExpectedCostBound
      (IsPerIndexQueryBound.toWorstCaseCostBound_unit_sum hbound)
      (val := fun n : ℕ ↦ (n : ENNReal)) Nat.mono_cast Measurable.of_discrete)

/-- The expected unit-cost query count of `seededForkWithSeedValue`, averaged over the randomly
sampled seed and replacement value, is at most `qb i`. -/
theorem expectedQueryCount_seededForkWithSeedValue_le
    [∀ i, DecidableEq (spec.Range i)] [Finite ι]
    (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (hmain : IsPerIndexQueryBound main qb) (hjs : SeedListCovers qb js) :
    wp⟦generateSeed spec qb js⟧ (fun seed => wp⟦$ᵗ spec.Range i⟧
      (fun u => expectedCost (seededForkWithSeedValue main qb i cf seed u) CostModel.unit
        (fun n : ℕ => (n : ENNReal)))) ≤ qb i := by
  calc
    _ ≤ wp⟦generateSeed spec qb js⟧ (fun _ => (qb i : ENNReal)) := by
      apply wp_mono_of_support
      intro seed hseed
      exact expectedQueryCount_seededForkWithSeedValue_le_aux main qb i cf hmain
        (generateSeed_covers_queryBound (spec := spec) qb js hjs hseed)
    _ = _ := ExpectationWP.wp_const_of_oracle _ _

section forkRuntime

variable [∀ i, DecidableEq (spec.Range i)]
variable [Finite ι]

/-- Total expected query work of one fork attempt. The LHS decomposes as three terms:

1. **Seed generation**: `∑ j in js, qb j * sampleCost j` uniform-oracle calls to build the seed.
2. **Replacement sample**: `sampleCost i` calls to sample one fresh value at the forked oracle `i`.
3. **Replay queries**: at most `qb i` live queries during the replayed execution.

The RHS is their sum: `(∑ j in js, qb j * sampleCost j) + sampleCost i + qb i`. -/
theorem seededForkExpectedQueryWork_le
    (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (sampleCost : ι → ℕ)
    (hSample :
      ∀ j, AddWriterT.QueryCostExactly
        (probCompUnitQueryRun ($ᵗ spec.Range j : ProbComp (spec.Range j)))
        (sampleCost j))
    (hmain : IsPerIndexQueryBound main qb)
    (hjs : SeedListCovers qb js) :
    AddWriterT.expectedCostNat (probCompUnitQueryRun (generateSeed spec qb js)) +
      AddWriterT.expectedCostNat
        (probCompUnitQueryRun ($ᵗ spec.Range i : ProbComp (spec.Range i))) +
      wp⟦generateSeed spec qb js⟧
        (fun seed =>
          wp⟦$ᵗ spec.Range i⟧
            (fun u =>
              expectedCost
                (seededForkWithSeedValue main qb i cf seed u)
                CostModel.unit
                (fun n : ℕ => (n : ENNReal)))) ≤
      ((js.map fun j => qb j * sampleCost j).sum + sampleCost i + qb i : ENNReal) :=
  add_le_add
    (add_le_add
      (AddWriterT.expectedCost_eq_of_pathwiseCostEqOnSupport _ _ Measurable.of_discrete
        (generateSeed_queryCostExactly (spec := spec) qb js sampleCost hSample)).le
      (AddWriterT.expectedCost_eq_of_pathwiseCostEqOnSupport _ _
        Measurable.of_discrete (hSample i)).le)
    (expectedQueryCount_seededForkWithSeedValue_le
      (main := main) (qb := qb) (js := js) (i := i) (cf := cf) hmain hjs)

end forkRuntime

end generateSeedCoverage

/-! ## The forking bound -/

variable (main : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    [∀ i, SampleableType (spec.Range i)] [unifSpec ⊂ₒ spec]

/-- If `seededFork` succeeds (returns `some`), both runs agree on the fork index. -/
theorem cf_eq_of_mem_support_seededFork [∀ i, DecidableEq (spec.Range i)] (x₁ x₂ : α)
    (h : some (x₁, x₂) ∈ support (seededFork main qb js i cf)) :
    ∃ s, cf x₁ = some s ∧ cf x₂ = some s := by
  simp only [seededFork, mem_support_bind_iff] at h
  grind

/-- The two-run success event without the collision guard is bounded by the fork's success plus
the collision event. -/
private lemma prEvent_noGuard_le_fork_add_collision
    [OracleSpec.AnswerMeasure spec] [∀ i, DecidableEq (spec.Range i)]
    (s : Fin (qb i + 1)) :
    Pr{let r ← (do
        let σ ← liftComp (generateSeed spec qb js) spec
        let a ← (simulateQ seededOracle main).run' σ
        let u ← liftComp ($ᵗ spec.Range i) spec
        let b ← (simulateQ seededOracle main).run' ((σ.takeAtIndex i s).addValue i u)
        return (a, b))}[cf r.1 = some s ∧ cf r.2 = some s] ≤
      Pr{let r ← seededFork main qb js i cf}[r.map (Prod.map cf cf) = some (some s, some s)] +
        Pr{let r ← (do
          let σ ← liftComp (generateSeed spec qb js) spec
          let a ← (simulateQ seededOracle main).run' σ
          let u ← liftComp ($ᵗ spec.Range i) spec
          return (a, (σ i)[s]?, u))}[cf r.1 = some s ∧ r.2.1 = some r.2.2] := by
  unfold seededFork
  simp only [expect_norm]
  rw [← ExpectationWP.wp_add]
  refine ExpectationWP.wp_mono _ fun σ => ?_
  rw [← ExpectationWP.wp_add]
  refine ExpectationWP.wp_mono _ fun a => ?_
  by_cases hcf : cf a = some s
  · simp only [hcf]
    rw [prEvent_bind, ← ExpectationWP.wp_add]
    refine ExpectationWP.wp_mono _ fun u => ?_
    by_cases hu : (σ i)[s]? = some u
    · simp only [hu, predInd_apply, true_and, propInd_true]
      exact (prEvent_le_one _).trans le_add_self
    · simp only [hu, ↓reduceIte, predInd_apply, and_false, propInd_false, add_zero,
        prEvent_bind]
      refine ExpectationWP.wp_mono _ fun b => ?_
      by_cases hb : cf b = some s <;> simp [hb, hcf]
  · refine (le_of_eq ?_).trans zero_le
    simp [hcf]

section forkingBound

variable [unifSpec ˡ⊂ₒ spec]
  [OracleSpec.UniformAnswerMeasure spec]

/-- The seeded run averaged over a uniformly generated seed, with the seed truncated after the
`s`-th answer at `i`, has the fork-index marginal of `main`. -/
private lemma prEvent_main_eq_takeAtIndex (s : Fin (qb i + 1)) :
    Pr{let x ← main}[cf x = some s] =
      Pr{let x ← (liftComp (generateSeed spec qb js) spec >>= fun σ =>
        (simulateQ seededOracle main).run' (σ.takeAtIndex i s))}[cf x = some s] := by
  let : MeasurableSpace α := ⊤
  rw [(EvalDistEq.of_evalDist_eq
      (seededOracle.evalDist_liftComp_generateSeed_bind_simulateQ_run' qb js main).symm).prEvent_eq]
  have h := (EvalDistEq.of_evalDist_eq
      (seededOracle.evalDistEq_liftComp_generateSeed_takeAtIndex_run' qb js i s main)).prEvent_eq
    (fun w => cf w.2 = some s)
  simpa only [expect_norm] using h

/-- Two runs on a shared seed, the second truncated after the `s`-th answer at `i`, have the
distribution of two runs on the truncated seed. -/
private lemma prEvent_pair_eq_takeAtIndex_pair (s : Fin (qb i + 1)) :
    Pr{let r ← (do
        let σ ← liftComp (generateSeed spec qb js) spec
        let a ← (simulateQ seededOracle main).run' σ
        let b ← (simulateQ seededOracle main).run' (σ.takeAtIndex i s)
        return (a, b))}[cf r.1 = some s ∧ cf r.2 = some s] =
      Pr{let r ← (do
        let σ ← liftComp (generateSeed spec qb js) spec
        let a ← (simulateQ seededOracle main).run' (σ.takeAtIndex i s)
        let b ← (simulateQ seededOracle main).run' (σ.takeAtIndex i s)
        return (a, b))}[cf r.1 = some s ∧ cf r.2 = some s] := by
  let : MeasurableSpace (α × α) := ⊤
  have h := ((EvalDistEq.of_evalDist_eq
      (seededOracle.evalDistEq_liftComp_generateSeed_takeAtIndex_run' qb js i s main)).bind_left
    (fun w => (simulateQ seededOracle main).run' w.1 >>= fun b => pure (w.2, b))).evalDist_eq
  simp only [bind_assoc, pure_bind] at h
  simpa only [expect_norm] using (EvalDistEq.of_evalDist_eq h).prEvent_eq
    (fun r : α × α => cf r.1 = some s ∧ cf r.2 = some s)

/-- Resampling the forked answer after truncation leaves the second run distributed as a run on
the truncated seed. -/
private lemma prEvent_noGuard_eq_pair (s : Fin (qb i + 1)) :
    Pr{let r ← (do
        let σ ← liftComp (generateSeed spec qb js) spec
        let a ← (simulateQ seededOracle main).run' σ
        let u ← liftComp ($ᵗ spec.Range i) spec
        let b ← (simulateQ seededOracle main).run' ((σ.takeAtIndex i s).addValue i u)
        return (a, b))}[cf r.1 = some s ∧ cf r.2 = some s] =
      Pr{let r ← (do
        let σ ← liftComp (generateSeed spec qb js) spec
        let a ← (simulateQ seededOracle main).run' σ
        let b ← (simulateQ seededOracle main).run' (σ.takeAtIndex i s)
        return (a, b))}[cf r.1 = some s ∧ cf r.2 = some s] := by
  simp only [expect_norm]
  refine ExpectationWP.wp_congr _ fun σ => ExpectationWP.wp_congr _ fun a => ?_
  let : MeasurableSpace α := ⊤
  rw [← prEvent_bind]
  exact (EvalDistEq.of_evalDist_eq
    (seededOracle.evalDist_liftComp_uniformSample_bind_simulateQ_run'_addValue
      (σ.takeAtIndex i s) i main)).prEvent_eq _

/-- The collision between the resampled answer and the seeded one is rare: it has probability at
most the fork-index probability divided by `|spec.Range i|`. -/
private lemma prEvent_collision_le [Fintype (spec.Range i)] (s : Fin (qb i + 1)) :
    Pr{let r ← (do
        let σ ← liftComp (generateSeed spec qb js) spec
        let a ← (simulateQ seededOracle main).run' σ
        let u ← liftComp ($ᵗ spec.Range i) spec
        return (a, (σ i)[s]?, u))}[cf r.1 = some s ∧ r.2.1 = some r.2.2] ≤
      Pr{let x ← main}[cf x = some s] / (Fintype.card (spec.Range i) : ℝ≥0∞) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace (QuerySeed spec) := ⊤
  rw [(EvalDistEq.of_evalDist_eq
      (seededOracle.evalDist_liftComp_generateSeed_bind_simulateQ_run' qb js main).symm).prEvent_eq]
  simp only [expect_norm]
  rw [ExpectationWP.wp_eq_lintegral (liftComp (generateSeed spec qb js) spec) _
      Measurable.of_discrete,
    ExpectationWP.wp_eq_lintegral (liftComp (generateSeed spec qb js) spec) _
      Measurable.of_discrete,
    div_eq_mul_inv, ← MeasureTheory.lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (by simp))]
  refine MeasureTheory.lintegral_mono fun σ => ?_
  rw [prEvent_bind_bind_and]
  exact mul_le_mul' le_rfl (prEvent_seedSlot_le_inv qb i s σ)

/-- Key bound of the forking lemma: the probability that both runs succeed with fork point `s`
is at least `Pr{cf main = some s}² - Pr{cf main = some s} / |Range i|`. -/
theorem le_prEvent_seededFork [∀ i, DecidableEq (spec.Range i)] [Fintype (spec.Range i)]
    (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr{let x ← main}[cf x = some s] ^ 2 - Pr{let x ← main}[cf x = some s] / h ≤
      Pr{let r ← seededFork main qb js i cf}[r.map (cf ∘ Prod.fst) = some (some s)] := by
  intro h
  have hsq : Pr{let x ← main}[cf x = some s] ^ 2 ≤
      Pr{let r ← (do
        let σ ← liftComp (generateSeed spec qb js) spec
        let a ← (simulateQ seededOracle main).run' σ
        let u ← liftComp ($ᵗ spec.Range i) spec
        let b ← (simulateQ seededOracle main).run' ((σ.takeAtIndex i s).addValue i u)
        return (a, b))}[cf r.1 = some s ∧ cf r.2 = some s] := by
    rw [prEvent_noGuard_eq_pair, prEvent_pair_eq_takeAtIndex_pair,
      prEvent_main_eq_takeAtIndex main qb js i cf s]
    have hjensen := prEvent_bind_sq_le_bind_pair (liftComp (generateSeed spec qb js) spec)
      (fun σ => (simulateQ seededOracle main).run' (σ.takeAtIndex i s)) (fun x => cf x = some s)
    simpa only [expect_norm] using hjensen
  refine le_trans (tsub_le_tsub
    (hsq.trans (prEvent_noGuard_le_fork_add_collision main qb js i cf s))
    (prEvent_collision_le main qb js i cf s)) ?_
  refine tsub_le_iff_right.2 (add_le_add ?_ le_rfl)
  exact prEvent_mono _ _ _ fun r hr => by
    rcases r with _ | ⟨x₁, x₂⟩ <;> simp_all

/-- Forking-lemma lower bound, packaged directly as the success-event probability. -/
theorem le_prEvent_isSome_seededFork [∀ i, DecidableEq (spec.Range i)] [Fintype (spec.Range i)] :
    (let acc : ℝ≥0∞ := ∑ s, Pr{let x ← main}[cf x = some s]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤
      Pr{let r ← seededFork main qb js i cf}[r.isSome] := by
  dsimp only
  set acc : ℝ≥0∞ := ∑ s, Pr{let x ← main}[cf x = some s]
  set h : ℝ≥0∞ := (Fintype.card (spec.Range i) : ℝ≥0∞)
  have hsum : acc ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (sum_prEvent_eq_some_le_one main cf)
  calc acc * (acc / ((qb i + 1 : ℕ) : ℝ≥0∞) - h⁻¹)
      ≤ ∑ s, (Pr{let x ← main}[cf x = some s] ^ 2 - Pr{let x ← main}[cf x = some s] / h) := by
        have hcard : ((Finset.univ : Finset (Fin (qb i + 1))).card : ℝ≥0∞) =
            ((qb i + 1 : ℕ) : ℝ≥0∞) := by simp
        have hbound := ENNReal.mul_tsub_inv_le_sum_sq_sub_div
          (Finset.univ : Finset (Fin (qb i + 1))) (fun s => Pr{let x ← main}[cf x = some s]) h hsum
        rwa [hcard] at hbound
    _ ≤ ∑ s, Pr{let r ← seededFork main qb js i cf}[r.map (cf ∘ Prod.fst) = some (some s)] :=
        Finset.sum_le_sum fun s _ => le_prEvent_seededFork main qb js i cf s
    _ ≤ _ := sum_prEvent_option_map_eq_some_le_isSome _ _

/-- Bellare-Neven seeded forking bound in its canonical `acc² / q − acc / h` shape, where
`acc = ∑ₛ Pr{cf main = some s}`, `q = qb i + 1`, and `h = |spec.Range i|`.

This is the aggregated bound that appears as Lemma 1 of Bellare-Neven (CCS'06): summing the
per-index lower bound over all fork points and applying Cauchy-Schwarz reshapes the product
form delivered by `le_prEvent_isSome_seededFork` into the familiar ratio form. -/
theorem le_prEvent_isSome_seededFork_sq [∀ i, DecidableEq (spec.Range i)]
    [Fintype (spec.Range i)] :
    ((∑ s, Pr{let x ← main}[cf x = some s]) ^ 2 / ((qb i + 1 : ℕ) : ℝ≥0∞)
        - (∑ s, Pr{let x ← main}[cf x = some s]) /
            ((Fintype.card (spec.Range i) : ℕ) : ℝ≥0∞))
      ≤ Pr{let r ← seededFork main qb js i cf}[r.isSome] := by
  set acc : ℝ≥0∞ := ∑ s, Pr{let x ← main}[cf x = some s]
  set h : ℝ≥0∞ := ((Fintype.card (spec.Range i) : ℕ) : ℝ≥0∞)
  have hacc_ne_top : acc ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (sum_prEvent_eq_some_le_one main cf)
  calc acc ^ 2 / ((qb i + 1 : ℕ) : ℝ≥0∞) - acc / h
    _ = acc * (acc / ((qb i + 1 : ℕ) : ℝ≥0∞) - h⁻¹) := by
        grind [ENNReal.mul_sub, sq, mul_div_assoc, div_eq_mul_inv]
    _ ≤ _ := le_prEvent_isSome_seededFork main qb js i cf

end forkingBound

end OracleComp
