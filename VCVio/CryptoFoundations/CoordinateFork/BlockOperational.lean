/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ToCslib.Probability.UniformOn
public import VCVio.CryptoFoundations.CoordinateFork
public import VCVio.EvalDist.IndepProduct
public import VCVio.EvalDist.IndepProductMeasure
public import VCVio.OracleComp.Constructions.WithoutReplacement

/-!
# The coordinate-wise extractor with an alphabet and a threshold per coordinate

`blockForkOp` is the coordinate-wise resampling loop of `coordForkOp` for a challenge
`(j : ι) → S j` with an alphabet `S j` and a threshold `k j` at every coordinate `j`, against a
fixed acceptance table `ρ`. It samples a challenge `c₀` and aborts if `ρ` rejects it. Otherwise it
draws the neighbours of `c₀` at every coordinate without replacement (`neighbourPool`) until
`k j - 1` of them are accepted or they run out. It reports how many table entries it looked at.

A run succeeds exactly on the *good* challenges, those accepted with every column holding at least
`k j` accepted challenges (`prEvent_isSome_blockForkOp`). A successful run returns a block star of
accepted challenges (`blockForkOp_success`), and the expected number of lookups is at most
`1 + ∑ j, (k j - 1)` (`lintegral_cost_blockForkOp_le`). With one alphabet and one threshold the loop
is `coordForkOp` (`blockForkOpAt_const` in `CoordinateFork/Operational.lean`).

The loop draws lists of whole challenges, one list per coordinate: the neighbours of `c₀` at
different coordinates all have type `(i : ι) → S i`, so `Fintype.mPi` sequences them.

## References

* [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
    Asymptotic and Concrete Efficiency*](https://eprint.iacr.org/2023/846)
-/

public section

open Finset CoordinateWise OracleComp ProbComp MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace OracleComp

/-! ## The pool of alternatives -/

/-- The values a coordinate can be resampled to: everything except the one already in use.
Coordinate `i` may range over its own alphabet `S i`. -/
@[expose] noncomputable def altPool {ι : Type} {S : ι → Type} [∀ i, DecidableEq (S i)]
    [∀ i, Fintype (S i)] (c₀ : (i : ι) → S i) (j : ι) : List (S j) :=
  (Finset.univ.erase (c₀ j)).toList

/-- The coordinate-`j` neighbours of `c₀`: the challenges that replace `c₀ j` by another value. -/
@[expose] noncomputable def neighbourPool {ι : Type} [DecidableEq ι] {S : ι → Type}
    [∀ i, DecidableEq (S i)] [∀ i, Fintype (S i)] (c₀ : (i : ι) → S i) (j : ι) :
    List ((i : ι) → S i) :=
  (altPool c₀ j).map (Function.update c₀ j)

section Pools

variable {ι : Type} {T : ι → Type} [∀ i, DecidableEq (T i)] [∀ i, Fintype (T i)]
  {c : (i : ι) → T i}

theorem nodup_altPool (c : (i : ι) → T i) (j : ι) : (altPool c j).Nodup :=
  Finset.nodup_toList _

theorem mem_altPool {j : ι} {x : T j} : x ∈ altPool c j ↔ x ≠ c j := by
  simp [altPool]

theorem length_altPool (c : (i : ι) → T i) (j : ι) :
    (altPool c j).length = Fintype.card (T j) - 1 := by
  rw [altPool, Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

variable [DecidableEq ι]

/-- The pool's accepting values are exactly the replacements the deterministic core sees. -/
theorem countP_altPool (ρ : ((i : ι) → T i) → Bool) (c : (i : ι) → T i) (j : ι) :
    (altPool c j).countP (fun x => ρ (Function.update c j x)) = (hitSet ρ c j).card := by
  rw [altPool, Finset.countP_toList, hitSet]

theorem nodup_neighbourPool (c : (i : ι) → T i) (j : ι) : (neighbourPool c j).Nodup :=
  (nodup_altPool c j).map (Function.update_injective c j)

theorem length_neighbourPool (c : (i : ι) → T i) (j : ι) :
    (neighbourPool c j).length = Fintype.card (T j) - 1 := by
  rw [neighbourPool, List.length_map, length_altPool]

/-- The members of the pool differ from `c` at `j` and nowhere else. -/
theorem differsOnlyAt_of_mem_neighbourPool {j : ι} {y : (i : ι) → T i}
    (hy : y ∈ neighbourPool c j) : Function.DiffersOnlyAt j c y := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact Function.differsOnlyAt_update fun h => (mem_altPool.mp hx) h.symm

/-- The accepted neighbours are exactly the replacements the deterministic core sees. -/
theorem countP_neighbourPool (ρ : ((i : ι) → T i) → Bool) (c : (i : ι) → T i) (j : ι) :
    (neighbourPool c j).countP ρ = (hitSet ρ c j).card := by
  rw [neighbourPool, List.countP_map]
  exact countP_altPool ρ c j

/-- No challenge is a neighbour of the centre at two coordinates. -/
theorem eq_of_mem_neighbourPool {y : (i : ι) → T i} {j j' : ι} (h : y ∈ neighbourPool c j)
    (h' : y ∈ neighbourPool c j') : j = j' :=
  (differsOnlyAt_of_mem_neighbourPool h).coord_eq (differsOnlyAt_of_mem_neighbourPool h')

/-- The centre is not its own neighbour. -/
theorem centre_notMem_neighbourPool (c : (i : ι) → T i) (j : ι) : c ∉ neighbourPool c j :=
  fun h => (differsOnlyAt_of_mem_neighbourPool h).ne rfl

end Pools

/-! ## Per-coordinate costs -/

/-- One coordinate's experiment costs at most `(k - 1) * |S j|` divided by that coordinate's column
count, which is the weight the counting lemma is stated for. Coordinate `i` may range over its own
alphabet `S i`. -/
theorem expectedDraws_hitSet_le {ι : Type} [DecidableEq ι] {S : ι → Type}
    [∀ i, DecidableEq (S i)] [∀ i, Fintype (S i)] {k : ℕ} {ρ : ((i : ι) → S i) → Bool}
    {c₀ : (i : ι) → S i} (hacc : ρ c₀) (j : ι) :
    NegHypergeom.expectedDraws (Fintype.card (S j) - 1) ((hitSet ρ c₀ j).card) (k - 1)
      ≤ ((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card (S j) : ℝ≥0∞)
          / ((columnCount (fun c => ρ c = true) j c₀ : ℕ) : ℝ≥0∞) := by
  classical
  have hpos : 0 < columnCount (fun c => ρ c = true) j c₀ :=
    Finset.card_pos.mpr ⟨c₀ j, mem_filter_coord_self (accept := fun c => ρ c = true) hacc j⟩
  have hle : columnCount (fun c => ρ c = true) j c₀ ≤ Fintype.card (S j) := by
    simpa [columnCount, Finset.card_univ] using
      Finset.card_le_card (Finset.filter_subset _ (Finset.univ : Finset (S j)))
  have hcard : (hitSet ρ c₀ j).card = columnCount (fun c => ρ c = true) j c₀ - 1 := by
    have := card_hitSet_succ hacc j
    omega
  rw [hcard]
  exact NegHypergeom.expectedDraws_resample_le hpos hle

/-- **The counting step.** Averaged over the sampled challenge, one coordinate's resampling costs
at most `k - 1` lookups. Coordinate `i` may range over its own alphabet `S i`. -/
theorem sum_expectedDraws_le {ι : Type} [DecidableEq ι] [Fintype ι] {S : ι → Type}
    [∀ i, DecidableEq (S i)] [∀ i, Fintype (S i)] (k : ℕ) (ρ : ((i : ι) → S i) → Bool) (j : ι)
    [Nonempty (S j)] :
    ∑ c₀ : (i : ι) → S i, (if ρ c₀ then
        NegHypergeom.expectedDraws (Fintype.card (S j) - 1) ((hitSet ρ c₀ j).card) (k - 1)
      else 0)
      ≤ (k - 1 : ℕ) * Fintype.card ((i : ι) → S i) := by
  classical
  have hNne : (Fintype.card (S j) : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hNtop : (Fintype.card (S j) : ℝ≥0∞) ≠ ⊤ := by finiteness
  refine (ENNReal.mul_le_mul_iff_right hNne hNtop).mp ?_
  calc (Fintype.card (S j) : ℝ≥0∞) * ∑ c₀ : (i : ι) → S i, (if ρ c₀ then
          NegHypergeom.expectedDraws (Fintype.card (S j) - 1) ((hitSet ρ c₀ j).card) (k - 1)
        else 0)
      ≤ (Fintype.card (S j) : ℝ≥0∞) * ∑ c₀ : (i : ι) → S i, (if ρ c₀ then
          ((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card (S j) : ℝ≥0∞)
            / ((columnCount (fun c => ρ c = true) j c₀ : ℕ) : ℝ≥0∞) else 0) := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun c₀ _ => ?_)
        by_cases hacc : ρ c₀
        · rw [ite_eq_left hacc, ite_eq_left hacc]
          exact expectedDraws_hitSet_le hacc j
        · rw [ite_eq_right hacc, ite_eq_right hacc]
    _ ≤ ((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card (S j) : ℝ≥0∞) *
          (Fintype.card ((i : ι) → S i) : ℝ≥0∞) :=
        CoordinateWise.card_mul_sum_div_columnCount_le_card j _
    _ = (Fintype.card (S j) : ℝ≥0∞) *
          (((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card ((i : ι) → S i) : ℝ≥0∞)) := by
        ring

variable {ι : Type} [DecidableEq ι] [Fintype ι] {S : ι → Type} [∀ j, DecidableEq (S j)]
  [∀ j, Fintype (S j)]
variable {k : ι → ℕ} {ρ : ((i : ι) → S i) → Bool} {c₀ : (i : ι) → S i}
  {d : ι → List ((i : ι) → S i)}

/-! ## The loop -/

/-- The resampling loop at one coordinate: draw neighbours of `c₀` without replacement until
`k j - 1` of them are accepted or the pool runs out. -/
@[expose] noncomputable def blockDraws (k : ι → ℕ) (ρ : ((i : ι) → S i) → Bool)
    (c₀ : (i : ι) → S i) (j : ι) : ProbComp (List ((i : ι) → S i)) :=
  drawUntil ρ (k j - 1) (neighbourPool c₀ j)

/-- The accepted neighbours a run collected at coordinate `j`. -/
@[expose] def blockCollected (ρ : ((i : ι) → S i) → Bool) (d : ι → List ((i : ι) → S i))
    (j : ι) : Finset ((i : ι) → S i) :=
  ((d j).filter ρ).toFinset

/-- The loop once the challenge has been drawn: abort on a rejected challenge, and otherwise
resample every coordinate and report what was collected together with the number of table entries
examined. -/
@[expose] noncomputable def blockForkOpAt (k : ι → ℕ) (ρ : ((i : ι) → S i) → Bool)
    (c₀ : (i : ι) → S i) : ProbComp (Option (Finset ((i : ι) → S i)) × ℕ) :=
  if ρ c₀ then do
    let d ← Fintype.mPi (blockDraws k ρ c₀)
    let cost : ℕ := 1 + ∑ j, (d j).length
    if ∀ j, ((d j).filter ρ).length = k j - 1 then
      return (some (neighbourFamily c₀ (blockCollected ρ d)), cost)
    else return (none, cost)
  else return (none, 1)

/-- The block extractor against a fixed acceptance table. -/
@[expose] noncomputable def blockForkOp [SampleableType ((i : ι) → S i)] (k : ι → ℕ)
    (ρ : ((i : ι) → S i) → Bool) : ProbComp (Option (Finset ((i : ι) → S i)) × ℕ) :=
  ($ᵗ ((i : ι) → S i)) >>= blockForkOpAt k ρ

/-! ## What a run collects -/

theorem mem_support_blockDraws (hd : d ∈ support (Fintype.mPi (blockDraws k ρ c₀))) (j : ι) :
    d j ∈ support (blockDraws k ρ c₀ j) :=
  mem_support_mPi _ d hd j

/-- The loop collects as many accepted neighbours as it was asked for, or as many as the
coordinate had. -/
theorem card_blockCollected (hd : d ∈ support (Fintype.mPi (blockDraws k ρ c₀))) (j : ι) :
    (blockCollected ρ d j).card = min (k j - 1) ((hitSet ρ c₀ j).card) := by
  classical
  have hj := mem_support_blockDraws hd j
  have hnodup : (d j).Nodup :=
    nodup_of_mem_support_drawUntil _ _ _ _ rfl (nodup_neighbourPool c₀ j) _ hj
  have hcount := countP_of_mem_support_drawUntil ρ (neighbourPool c₀ j).length (k j - 1) _ rfl _ hj
  rw [blockCollected, List.toFinset_card_of_nodup (hnodup.filter _), ← List.countP_eq_length_filter,
    hcount, countP_neighbourPool]

/-- The number of accepted neighbours a run drew at coordinate `j`. -/
theorem length_filter_of_mem_support_blockDraws
    (hd : d ∈ support (Fintype.mPi (blockDraws k ρ c₀))) (j : ι) :
    ((d j).filter ρ).length = min (k j - 1) ((hitSet ρ c₀ j).card) := by
  rw [← List.countP_eq_length_filter, ← countP_neighbourPool]
  exact countP_of_mem_support_drawUntil ρ (neighbourPool c₀ j).length (k j - 1) _ rfl _
    (mem_support_blockDraws hd j)

theorem mem_neighbourPool_of_mem_blockCollected (hd : d ∈ support (Fintype.mPi (blockDraws k ρ c₀)))
    {j : ι} {y : (i : ι) → S i} (hy : y ∈ blockCollected ρ d j) : y ∈ neighbourPool c₀ j := by
  classical
  rw [blockCollected, List.mem_toFinset, List.mem_filter] at hy
  exact mem_of_mem_support_drawUntil _ (neighbourPool c₀ j).length (k j - 1) _ rfl _
    (mem_support_blockDraws hd j) y hy.1

omit [DecidableEq ι] [∀ j, Fintype (S j)] in
theorem accept_of_mem_blockCollected {j : ι} {y : (i : ι) → S i}
    (hy : y ∈ blockCollected ρ d j) : ρ y = true := by
  classical
  rw [blockCollected, List.mem_toFinset, List.mem_filter] at hy
  simpa using hy.2

/-! ## Success and output -/

/-- The challenges on which the loop succeeds: accepted, with every column holding at least `k j`
accepted challenges. -/
@[expose] def blockGoodSet (k : ι → ℕ) (ρ : ((i : ι) → S i) → Bool) :
    Finset ((i : ι) → S i) :=
  Finset.univ.filter fun c =>
    ρ c = true ∧ ∀ j, k j ≤ columnCount (fun c => ρ c = true) j c

omit [∀ j, DecidableEq (S j)] in
theorem mem_blockGoodSet {c : (i : ι) → S i} :
    c ∈ blockGoodSet k ρ ↔ ρ c = true ∧ ∀ j, k j ≤ columnCount (fun c => ρ c = true) j c := by
  simp [blockGoodSet]

/-- On an accepted centre the loop succeeds exactly when the centre is good. The order the
coordinates were resampled in cannot matter, because the loop stops only on success or on
exhaustion. -/
theorem forall_length_filter_blockDraws_iff (hacc : ρ c₀ = true)
    (hd : d ∈ support (Fintype.mPi (blockDraws k ρ c₀))) :
    (∀ j, ((d j).filter ρ).length = k j - 1) ↔ c₀ ∈ blockGoodSet k ρ := by
  rw [mem_blockGoodSet]
  refine ⟨fun h => ⟨hacc, fun j => ?_⟩, fun h j => ?_⟩
  · have h1 := h j
    rw [length_filter_of_mem_support_blockDraws hd j] at h1
    have h2 := card_hitSet_succ hacc j
    omega
  · have h1 := h.2 j
    rw [length_filter_of_mem_support_blockDraws hd j]
    have h2 := card_hitSet_succ hacc j
    omega

/-- **The output guarantee.** A successful run returns a block star of challenges the table
accepts. -/
theorem blockForkOpAt_success {X : Finset ((i : ι) → S i)} {cost : ℕ}
    (h : (some X, cost) ∈ support (blockForkOpAt k ρ c₀)) :
    IsBlockSpecialSound k X ∧ ∀ c ∈ X, ρ c = true := by
  classical
  rw [blockForkOpAt] at h
  by_cases hacc : ρ c₀ = true
  · rw [ite_eq_left hacc, mem_support_bind_iff] at h
    obtain ⟨d, hd, h⟩ := h
    by_cases hcond : ∀ j, ((d j).filter ρ).length = k j - 1
    · rw [ite_eq_left hcond] at h
      obtain rfl : X = neighbourFamily c₀ (blockCollected ρ d) := by
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at h
        exact h.1
      have hcard : ∀ j, (blockCollected ρ d j).card = k j - 1 := fun j => by
        rw [card_blockCollected hd j, ← length_filter_of_mem_support_blockDraws hd j, hcond j]
      refine ⟨isBlockSpecialSound_neighbourFamily ?_ hcard, ?_⟩
      · intro j y hy
        exact differsOnlyAt_of_mem_neighbourPool (mem_neighbourPool_of_mem_blockCollected hd hy)
      · intro c hc
        rcases mem_neighbourFamily.mp hc with rfl | ⟨j, hj⟩
        · exact hacc
        · exact accept_of_mem_blockCollected hj
    · rw [ite_eq_right hcond] at h
      simp at h
  · rw [ite_eq_right hacc] at h
    simp at h

theorem blockForkOp_success [SampleableType ((i : ι) → S i)] {X : Finset ((i : ι) → S i)}
    {cost : ℕ} (h : (some X, cost) ∈ support (blockForkOp k ρ)) :
    IsBlockSpecialSound k X ∧ ∀ c ∈ X, ρ c = true := by
  rw [blockForkOp, mem_support_bind_iff] at h
  obtain ⟨c₀, -, hAt⟩ := h
  exact blockForkOpAt_success hAt

/-! ## The success probability -/

/-- On a fixed challenge the loop succeeds with certainty or not at all, according to whether that
challenge is good. Which neighbours the resampling happened to draw does not matter. -/
theorem prEvent_isSome_blockForkOpAt (k : ι → ℕ) (ρ : ((i : ι) → S i) → Bool)
    (c₀ : (i : ι) → S i) :
    Pr{let r ← blockForkOpAt k ρ c₀}[r.1.isSome] = if c₀ ∈ blockGoodSet k ρ then 1 else 0 := by
  classical
  by_cases hacc : ρ c₀ = true
  · rw [blockForkOpAt, ite_eq_left hacc]
    by_cases hgood : c₀ ∈ blockGoodSet k ρ
    · refine (prEvent_eq_one_of_forall_mem_support _ _ fun r hr => ?_).trans
        (ite_eq_left hgood).symm
      rw [mem_support_bind_iff] at hr
      obtain ⟨d, hd, hr⟩ := hr
      rw [ite_eq_left ((forall_length_filter_blockDraws_iff hacc hd).mpr hgood)] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
    · refine (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr => ?_).trans
        (ite_eq_right hgood).symm
      rw [mem_support_bind_iff] at hr
      obtain ⟨d, hd, hr⟩ := hr
      rw [ite_eq_right fun hc => hgood ((forall_length_filter_blockDraws_iff hacc hd).mp hc)] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
  · have hgood : c₀ ∉ blockGoodSet k ρ := by simp [mem_blockGoodSet, hacc]
    rw [blockForkOpAt, ite_eq_right hacc, ite_eq_right hgood]
    simp

/-- **The success probability.** The loop succeeds exactly as often as the challenge is good. -/
theorem prEvent_isSome_blockForkOp [SampleableType ((i : ι) → S i)] (k : ι → ℕ)
    (ρ : ((i : ι) → S i) → Bool) :
    Pr{let r ← blockForkOp k ρ}[r.1.isSome]
      = ((blockGoodSet k ρ).card : ℝ≥0∞) / Fintype.card ((i : ι) → S i) := by
  classical
  let _ : MeasurableSpace ((i : ι) → S i) := ⊤
  let _ : MeasurableSingletonClass ((i : ι) → S i) := ⟨fun _ => trivial⟩
  rw [blockForkOp, prEvent_bind_eq_lintegral_of_discrete,
    SampleableType.evalDist_uniformSample, lintegral_uniformOn_univ]
  simp only [prEvent_isSome_blockForkOpAt]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ## The expected number of lookups -/

/-- The loop's expected cost at a fixed challenge: one lookup for the challenge itself, and then
one negative hypergeometric experiment per coordinate. -/
theorem lintegral_cost_blockForkOpAt (k : ι → ℕ) (ρ : ((i : ι) → S i) → Bool)
    (c₀ : (i : ι) → S i) :
    ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$> blockForkOpAt k ρ c₀]
      = if ρ c₀ = true then
          1 + ∑ j, NegHypergeom.expectedDraws (Fintype.card (S j) - 1) ((hitSet ρ c₀ j).card)
            (k j - 1)
        else 1 := by
  classical
  -- The statement observes only the counter; the draws are integrated with discrete lists.
  let _ : MeasurableSpace (List ((i : ι) → S i)) := ⊤
  have _ : DiscreteMeasurableSpace (List ((i : ι) → S i)) := ⟨fun _ => trivial⟩
  rw [blockForkOpAt]
  by_cases hacc : ρ c₀ = true
  · rw [ite_eq_left hacc, ite_eq_left hacc, map_bind,
      lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete]
    have hinner : ∀ d : ι → List ((i : ι) → S i),
        ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$>
            (if ∀ j, ((d j).filter ρ).length = k j - 1 then
                (pure (some (neighbourFamily c₀ (blockCollected ρ d)),
                    1 + ∑ j, (d j).length) :
                  ProbComp (Option (Finset ((i : ι) → S i)) × ℕ))
              else pure (none, 1 + ∑ j, (d j).length))]
          = 1 + ∑ j, ((d j).length : ℝ≥0∞) := by
      intro d
      rw [apply_ite (fun x => Prod.snd <$> x), map_pure, map_pure, ite_self, evalDist_pure,
        lintegral_dirac]
      push_cast
      rfl
    simp only [hinner]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_finsetSum _ fun _ _ => Measurable.of_discrete]
    refine congrArg (1 + ·) (Finset.sum_congr rfl fun j _ => ?_)
    rw [lintegral_evalDist_mPi_coord (blockDraws k ρ c₀)
        (fun i => (isProbabilityMeasure_evalDist_drawUntil _ _ _ _ rfl).measure_univ) j
        (fun d => (d.length : ℝ≥0∞)) Measurable.of_discrete,
      ← lintegral_evalDist_map (blockDraws k ρ c₀ j) (f := List.length)
        (g := fun n : ℕ => (n : ℝ≥0∞)) Measurable.of_discrete Measurable.of_discrete,
      blockDraws, lintegral_evalDist_length_drawUntil _ (neighbourPool c₀ j).length _ _ rfl,
      length_neighbourPool, countP_neighbourPool]
  · rw [ite_eq_right hacc, ite_eq_right hacc]
    rw [map_pure, evalDist_pure, lintegral_dirac]
    push_cast
    ring

/-- **The expected-query clause.** The loop looks at one table entry for the sampled challenge and,
on average, at most `k j - 1` further entries at coordinate `j`. -/
theorem lintegral_cost_blockForkOp_le [SampleableType ((i : ι) → S i)]
    (k : ι → ℕ) (ρ : ((i : ι) → S i) → Bool) :
    ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$> blockForkOp k ρ]
      ≤ 1 + ∑ j, ((k j - 1 : ℕ) : ℝ≥0∞) := by
  have : ∀ j, Nonempty (S j) := fun j => ⟨(Classical.arbitrary ((i : ι) → S i)) j⟩
  classical
  let _ : MeasurableSpace ((i : ι) → S i) := ⊤
  let _ : MeasurableSingletonClass ((i : ι) → S i) := ⟨fun _ => trivial⟩
  have hCne : (Fintype.card ((i : ι) → S i) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hCtop : (Fintype.card ((i : ι) → S i) : ℝ≥0∞) ≠ ⊤ := by finiteness
  have hsplit : ∀ c₀ : (i : ι) → S i,
      (if ρ c₀ = true then
          1 + ∑ j, NegHypergeom.expectedDraws (Fintype.card (S j) - 1) ((hitSet ρ c₀ j).card)
            (k j - 1)
        else 1)
        = 1 + ∑ j, (if ρ c₀ = true then
            NegHypergeom.expectedDraws (Fintype.card (S j) - 1) ((hitSet ρ c₀ j).card) (k j - 1)
          else 0) := by
    intro c₀
    by_cases hacc : ρ c₀ = true <;> simp [hacc]
  rw [blockForkOp, map_bind, lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete,
    SampleableType.evalDist_uniformSample, lintegral_uniformOn_univ]
  simp only [lintegral_cost_blockForkOpAt, hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Finset.sum_comm, div_eq_mul_inv, mul_comm]
  calc (Fintype.card ((i : ι) → S i) : ℝ≥0∞)⁻¹ *
        ((Fintype.card ((i : ι) → S i) : ℝ≥0∞) + ∑ j : ι, ∑ c₀ : (i : ι) → S i,
          (if ρ c₀ = true then NegHypergeom.expectedDraws (Fintype.card (S j) - 1)
            ((hitSet ρ c₀ j).card) (k j - 1) else 0))
      ≤ (Fintype.card ((i : ι) → S i) : ℝ≥0∞)⁻¹ *
          ((Fintype.card ((i : ι) → S i) : ℝ≥0∞)
            + ∑ j : ι, (((k j - 1 : ℕ) : ℝ≥0∞) *
              (Fintype.card ((i : ι) → S i) : ℝ≥0∞))) :=
        mul_le_mul' le_rfl
          (add_le_add le_rfl (Finset.sum_le_sum fun j _ => sum_expectedDraws_le (k j) ρ j))
    _ = 1 + ∑ j, ((k j - 1 : ℕ) : ℝ≥0∞) := by
        rw [← Finset.sum_mul, mul_add, ENNReal.inv_mul_cancel hCne hCtop, ← mul_assoc,
          mul_comm _ (∑ j, ((k j - 1 : ℕ) : ℝ≥0∞)), mul_assoc,
          ENNReal.inv_mul_cancel hCne hCtop, mul_one]

end OracleComp
