/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.UniformOn
public import VCVio.CryptoFoundations.CoordinateFork
public import VCVio.EvalDist.IndepProduct
public import VCVio.EvalDist.IndepProductMeasure
public import VCVio.OracleComp.Constructions.WithoutReplacement

/-!
# The coordinate-wise rewinding extractor as a resampling loop

`coordForkOp` is Figure 11 of Fenzi–Moghaddas–Nguyen against a fixed acceptance table: sample a
challenge `c₀`, abort if it is rejected, and otherwise resample each coordinate *without
replacement* until `k - 1` further accepting values have been found there, or that coordinate is
exhausted. It reports how many table entries it looked at, so the query count is part of its
output rather than an external accounting.

`VCVio/CryptoFoundations/CoordinateFork.lean` has the same success condition as a total lookup:
`coordForkCore` reads the whole column and keeps the first `k - 1` accepting values in enumeration
order. The two agree on what matters. `prEvent_isSome_coordForkOp` shows the loop succeeds with
exactly the core's probability — the sampled column order is irrelevant, because the loop stops
only on success or exhaustion — and `coordForkOp_success` shows a successful run returns a
coordinate-wise `k`-special sound set of accepting challenges, via the shared
`coordFamily_success`.

So the success and output clauses of Lemma 7.1 hold for the paper's actual algorithm and not only
for the table model. This is against a *fixed* acceptance table, which is the setting §7.1 needs:
its own analysis treats the adversary as a function of the challenge. See
`CoordinateFork/Realizability.lean` for where such a table comes from.

The expected-query clause is still open. The count is returned (`coordForkOp` pairs its result with
the number of lookups) and `ProbComp.expectedLength_drawUntil` computes each coordinate's
contribution, but nothing here assembles those into the paper's `1 + ℓ(k - 1)` bound.
-/

public section

open Finset CoordinateWise OracleComp ProbComp MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace OracleComp

variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]
variable {k : ℕ} {ρ : (ι → S) → Bool} {c₀ : ι → S} {d : ι → List S}

/-! ## The pool of alternatives -/

/-- The values a coordinate can be resampled to: everything except the one already in use. -/
@[expose] noncomputable def altPool (c₀ : ι → S) (j : ι) : List S :=
  (Finset.univ.erase (c₀ j)).toList

omit [DecidableEq ι] [Fintype ι] in
theorem nodup_altPool (c₀ : ι → S) (j : ι) : (altPool c₀ j).Nodup := Finset.nodup_toList _

omit [DecidableEq ι] [Fintype ι] in
theorem mem_altPool {x : S} {j : ι} : x ∈ altPool c₀ j ↔ x ≠ c₀ j := by
  simp [altPool]

omit [DecidableEq ι] [Fintype ι] in
theorem length_altPool (c₀ : ι → S) (j : ι) : (altPool c₀ j).length = Fintype.card S - 1 := by
  rw [altPool, Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

omit [Fintype ι] in
/-- The pool's accepting values are exactly the replacements the deterministic core sees. -/
theorem countP_altPool (ρ : (ι → S) → Bool) (c₀ : ι → S) (j : ι) :
    (altPool c₀ j).countP (fun x => ρ (Function.update c₀ j x)) = (hitSet ρ c₀ j).card := by
  rw [altPool, Finset.countP_toList, hitSet]

/-! ## The loop -/

/-- The resampling loop at one coordinate. -/
@[expose] noncomputable def coordDraws (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) (j : ι) :
    ProbComp (List S) :=
  drawUntil (fun x => ρ (Function.update c₀ j x)) (k - 1) (altPool c₀ j)

/-- The accepting values a run collected at coordinate `j`. -/
@[expose] noncomputable def collected (ρ : (ι → S) → Bool) (c₀ : ι → S) (d : ι → List S) (j : ι) :
    Finset S :=
  ((d j).filter fun x => ρ (Function.update c₀ j x)).toFinset

/-- The loop once the challenge has been drawn: abort on a rejecting challenge, and otherwise
resample every coordinate and report what was collected together with the number of table entries
examined. -/
@[expose] noncomputable def coordForkOpAt (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) :
    ProbComp (Option (Finset (ι → S)) × ℕ) :=
  if ρ c₀ then do
    let d ← Fintype.mPi (coordDraws k ρ c₀)
    let cost : ℕ := 1 + ∑ j, (d j).length
    if ∀ j, (collected ρ c₀ d j).card = k - 1 then
      return (some (coordFamily c₀ (collected ρ c₀ d)), cost)
    else return (none, cost)
  else return (none, 1)

/-- **Figure 11 of Fenzi–Moghaddas–Nguyen**, against a fixed acceptance table. -/
@[expose] noncomputable def coordForkOp [SampleableType (ι → S)] (k : ℕ) (ρ : (ι → S) → Bool) :
    ProbComp (Option (Finset (ι → S)) × ℕ) :=
  ($ᵗ (ι → S)) >>= coordForkOpAt k ρ

/-! ## What a run collects -/

theorem mem_support_coordDraws (hd : d ∈ support (Fintype.mPi (coordDraws k ρ c₀))) (j : ι) :
    d j ∈ support (coordDraws k ρ c₀ j) :=
  mem_support_mPi _ d hd j

/-- The loop collects as many accepting values as it was asked for, or as many as the coordinate
had. This is the only fact about the loop the success analysis uses. -/
theorem card_collected (hd : d ∈ support (Fintype.mPi (coordDraws k ρ c₀))) (j : ι) :
    (collected ρ c₀ d j).card = min (k - 1) ((hitSet ρ c₀ j).card) := by
  classical
  have hj := mem_support_coordDraws hd j
  have hnodup : (d j).Nodup :=
    nodup_of_mem_support_drawUntil _ _ _ _ rfl (nodup_altPool c₀ j) _ hj
  have hcount := countP_of_mem_support_drawUntil
    (fun x => ρ (Function.update c₀ j x)) (altPool c₀ j).length (k - 1) _ rfl _ hj
  rw [collected, List.toFinset_card_of_nodup (hnodup.filter _), ← List.countP_eq_length_filter,
    hcount, countP_altPool]

theorem mem_altPool_of_mem_collected (hd : d ∈ support (Fintype.mPi (coordDraws k ρ c₀)))
    {j : ι} {x : S} (hx : x ∈ collected ρ c₀ d j) : x ∈ altPool c₀ j := by
  classical
  rw [collected, List.mem_toFinset, List.mem_filter] at hx
  exact mem_of_mem_support_drawUntil _ (altPool c₀ j).length (k - 1) _ rfl _
    (mem_support_coordDraws hd j) x hx.1

theorem notMem_collected (hd : d ∈ support (Fintype.mPi (coordDraws k ρ c₀))) (j : ι) :
    c₀ j ∉ collected ρ c₀ d j := fun hx =>
  (mem_altPool.mp (mem_altPool_of_mem_collected hd hx)) rfl

omit [Fintype ι] [Fintype S] in
theorem accept_of_mem_collected {j : ι} {x : S} (hx : x ∈ collected ρ c₀ d j) :
    ρ (Function.update c₀ j x) := by
  classical
  rw [collected, List.mem_toFinset, List.mem_filter] at hx
  exact hx.2

/-! ## Success and output -/

section Op

variable [SampleableType (ι → S)]

omit [SampleableType (ι → S)] in
/-- On an accepting centre the loop succeeds exactly when the centre is good — that is, exactly
when the deterministic core succeeds. The order the coordinate was resampled in cannot matter,
because the loop stops only on success or on exhaustion. -/
theorem forall_card_collected_iff (hacc : ρ c₀)
    (hd : d ∈ support (Fintype.mPi (coordDraws k ρ c₀))) :
    (∀ j, (collected ρ c₀ d j).card = k - 1) ↔ c₀ ∈ goodSet k ρ := by
  rw [mem_goodSet_iff_of_accept hacc]
  refine forall_congr' fun j => ?_
  rw [card_collected hd j]
  omega

omit [SampleableType (ι → S)] in
/-- **The output guarantee.** A successful run returns a coordinate-wise `k`-special sound set of
challenges the table accepts. -/
theorem coordForkOpAt_success {X : Finset (ι → S)} {cost : ℕ}
    (h : (some X, cost) ∈ support (coordForkOpAt k ρ c₀)) :
    IsCoordSpecialSound k X ∧ ∀ c ∈ X, ρ c := by
  classical
  rw [coordForkOpAt] at h
  by_cases hacc : ρ c₀
  · rw [ite_eq_left hacc, mem_support_bind_iff] at h
    obtain ⟨d, hd, h⟩ := h
    by_cases hcond : ∀ j, (collected ρ c₀ d j).card = k - 1
    · rw [ite_eq_left hcond] at h
      obtain rfl : X = coordFamily c₀ (collected ρ c₀ d) := by
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at h
        exact h.1
      exact coordFamily_success hacc (notMem_collected hd) hcond
        fun _ _ hx => accept_of_mem_collected hx
    · rw [ite_eq_right hcond] at h
      simp at h
  · rw [ite_eq_right hacc] at h
    simp at h

theorem coordForkOp_success {X : Finset (ι → S)} {cost : ℕ}
    (h : (some X, cost) ∈ support (coordForkOp k ρ)) :
    IsCoordSpecialSound k X ∧ ∀ c ∈ X, ρ c := by
  rw [coordForkOp, mem_support_bind_iff] at h
  obtain ⟨c₀, hc₀, hAt⟩ := h
  exact coordForkOpAt_success hAt

/-- **The two-transcript reading of a successful run.** In every coordinate the returned set holds
two accepting challenges differing there and nowhere else.

This is the form a reduction built on a pair of openings consumes — one pair per coordinate — and
`k = 2`, the only case Fenzi–Moghaddas–Nguyen treat, is exactly where the returned set holds
nothing more. -/
theorem coordForkOp_exists_pair {X : Finset (ι → S)} {cost : ℕ} (hk : 2 ≤ k)
    (h : (some X, cost) ∈ support (coordForkOp k ρ)) (j : ι) :
    ∃ c ∈ X, ∃ c' ∈ X, Function.DiffersOnlyAt j c c' ∧ ρ c ∧ ρ c' := by
  obtain ⟨hss, hacc⟩ := coordForkOp_success h
  obtain ⟨c, hc, c', hc', hdiff⟩ := hss.exists_pair_differsOnlyAt hk j
  exact ⟨c, hc, c', hc', hdiff, hacc c hc, hacc c' hc'⟩

/-! ## The success probability -/

omit [SampleableType (ι → S)] in
/-- On a fixed challenge the loop succeeds with certainty or not at all, according to whether that
challenge is good. Which values the coordinate resampling happened to draw does not matter. -/
theorem prEvent_isSome_coordForkOpAt (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) :
    Pr{let r ← coordForkOpAt k ρ c₀}[r.1.isSome] = if c₀ ∈ goodSet k ρ then 1 else 0 := by
  classical
  by_cases hacc : ρ c₀
  · rw [coordForkOpAt, ite_eq_left hacc]
    by_cases hgood : c₀ ∈ goodSet k ρ
    · refine (prEvent_eq_one_of_forall_mem_support _ _ fun r hr => ?_).trans
        (ite_eq_left hgood).symm
      rw [mem_support_bind_iff] at hr
      obtain ⟨d, hd, hr⟩ := hr
      rw [ite_eq_left ((forall_card_collected_iff hacc hd).mpr hgood)] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
    · refine (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr => ?_).trans
        (ite_eq_right hgood).symm
      rw [mem_support_bind_iff] at hr
      obtain ⟨d, hd, hr⟩ := hr
      rw [ite_eq_right fun hc => hgood ((forall_card_collected_iff hacc hd).mp hc)] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
  · have hgood : c₀ ∉ goodSet k ρ := by simp [goodSet, hacc]
    rw [coordForkOpAt, ite_eq_right hacc, ite_eq_right hgood]
    simp

/-- **The success probability of Figure 11.** The loop succeeds exactly as often as the
deterministic table core: on `goodSet k ρ`, the challenges whose every column holds at least `k`
accepting values. -/
theorem prEvent_isSome_coordForkOp (k : ℕ) (ρ : (ι → S) → Bool) :
    Pr{let r ← coordForkOp k ρ}[r.1.isSome]
      = ((goodSet k ρ).card : ℝ≥0∞) / Fintype.card (ι → S) := by
  classical
  let _ : MeasurableSpace (ι → S) := ⊤
  let _ : MeasurableSingletonClass (ι → S) := ⟨fun _ => trivial⟩
  rw [coordForkOp, prEvent_bind_eq_lintegral_of_discrete,
    SampleableType.evalDist_uniformSample, lintegral_uniformOn_univ]
  simp only [prEvent_isSome_coordForkOpAt]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Lemma 7.1 for the paper's algorithm**, at a fixed acceptance table: the resampling loop
returns a coordinate-wise `k`-special sound set of accepting challenges with probability at least
`ε - ℓ(k-1)/N`, where `ε` is the table's accepting ratio.

The output is guaranteed by `coordForkOp_success` and the lookup count by
`lintegral_cost_coordForkOp_le`. -/
theorem sub_div_le_prEvent_isSome_coordForkOp [Nonempty S] (k : ℕ) (ρ : (ι → S) → Bool) :
    ((Finset.univ.filter fun c : ι → S => ρ c).card : ℝ≥0∞) / Fintype.card (ι → S)
        - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ Pr{let r ← coordForkOp k ρ}[r.1.isSome] := by
  rw [prEvent_isSome_coordForkOp]
  exact CoordinateWise.sub_div_le_div_card_filter (accept := fun c => ρ c = true) k

/-! ## The expected number of lookups -/

omit [SampleableType (ι → S)] in
/-- The loop's expected cost at a fixed challenge: one lookup for the challenge itself, and then
one negative hypergeometric experiment per coordinate. -/
theorem lintegral_cost_coordForkOpAt (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) :
    ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$> coordForkOpAt k ρ c₀]
      = if ρ c₀ then
          1 + ∑ j, NegHypergeom.expectedDraws (Fintype.card S - 1) ((hitSet ρ c₀ j).card) (k - 1)
        else 1 := by
  classical
  rw [coordForkOpAt]
  by_cases hacc : ρ c₀
  · rw [ite_eq_left hacc, ite_eq_left hacc, map_bind,
      lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete]
    have hinner : ∀ d : ι → List S,
        ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$>
            (if ∀ j, (collected ρ c₀ d j).card = k - 1 then
                (pure (some (coordFamily c₀ (collected ρ c₀ d)), 1 + ∑ j, (d j).length) :
                  ProbComp (Option (Finset (ι → S)) × ℕ))
              else pure (none, 1 + ∑ j, (d j).length))]
          = 1 + ∑ j, ((d j).length : ℝ≥0∞) := by
      intro d
      rw [show (Prod.snd <$>
            (if ∀ j, (collected ρ c₀ d j).card = k - 1 then
                (pure (some (coordFamily c₀ (collected ρ c₀ d)), 1 + ∑ j, (d j).length) :
                  ProbComp (Option (Finset (ι → S)) × ℕ))
              else pure (none, 1 + ∑ j, (d j).length)))
          = (pure (1 + ∑ j, (d j).length) : ProbComp ℕ) from by split <;> rfl,
        evalDist_pure, lintegral_dirac]
      push_cast
      rfl
    simp only [hinner]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_finsetSum _ fun _ _ => Measurable.of_discrete]
    refine congrArg (1 + ·) (Finset.sum_congr rfl fun j _ => ?_)
    rw [lintegral_evalDist_mPi_coord (coordDraws k ρ c₀)
        (fun i => (isProbabilityMeasure_evalDist_drawUntil _ _ _ _ rfl).measure_univ) j
        (fun d => (d.length : ℝ≥0∞)) Measurable.of_discrete,
      ← lintegral_evalDist_map (coordDraws k ρ c₀ j) (f := List.length)
        (g := fun n : ℕ => (n : ℝ≥0∞)) Measurable.of_discrete Measurable.of_discrete,
      coordDraws, lintegral_evalDist_length_drawUntil _ (altPool c₀ j).length _ _ rfl,
      length_altPool, countP_altPool]
  · rw [ite_eq_right hacc, ite_eq_right hacc]
    rw [show (Prod.snd <$> (pure (none, 1) : ProbComp (Option (Finset (ι → S)) × ℕ)))
        = (pure 1 : ProbComp ℕ) from rfl, evalDist_pure, lintegral_dirac]
    push_cast
    ring

omit [Fintype ι] [SampleableType (ι → S)] in
/-- One coordinate's experiment costs at most `(k - 1) * |S|` divided by that coordinate's column
count, which is the weight the counting lemma is stated for. -/
theorem expectedDraws_hitSet_le (hacc : ρ c₀) (j : ι) :
    NegHypergeom.expectedDraws (Fintype.card S - 1) ((hitSet ρ c₀ j).card) (k - 1)
      ≤ ((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card S : ℝ≥0∞)
          / ((columnCount (fun c => ρ c = true) j c₀ : ℕ) : ℝ≥0∞) := by
  classical
  have hpos : 0 < columnCount (fun c => ρ c = true) j c₀ :=
    Finset.card_pos.mpr ⟨c₀ j, mem_filter_coord_self (accept := fun c => ρ c = true) hacc j⟩
  have hle : columnCount (fun c => ρ c = true) j c₀ ≤ Fintype.card S := by
    simpa [columnCount, Finset.card_univ] using
      Finset.card_le_card (Finset.filter_subset _ (Finset.univ : Finset S))
  have hcard : (hitSet ρ c₀ j).card = columnCount (fun c => ρ c = true) j c₀ - 1 := by
    have := card_hitSet_succ hacc j
    omega
  rw [hcard]
  exact NegHypergeom.expectedDraws_resample_le hpos hle

omit [SampleableType (ι → S)] in
/-- **The counting step.** Averaged over the sampled challenge, one coordinate's resampling costs
at most `k - 1` lookups. -/
theorem sum_expectedDraws_le [Nonempty S] (k : ℕ) (ρ : (ι → S) → Bool) (j : ι) :
    ∑ c₀ : ι → S, (if ρ c₀ then
        NegHypergeom.expectedDraws (Fintype.card S - 1) ((hitSet ρ c₀ j).card) (k - 1) else 0)
      ≤ (k - 1 : ℕ) * Fintype.card (ι → S) := by
  classical
  have hNne : (Fintype.card S : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hNtop : (Fintype.card S : ℝ≥0∞) ≠ ⊤ := by finiteness
  refine (ENNReal.mul_le_mul_iff_right hNne hNtop).mp ?_
  calc (Fintype.card S : ℝ≥0∞) * ∑ c₀ : ι → S, (if ρ c₀ then
          NegHypergeom.expectedDraws (Fintype.card S - 1) ((hitSet ρ c₀ j).card) (k - 1) else 0)
      ≤ (Fintype.card S : ℝ≥0∞) * ∑ c₀ : ι → S, (if ρ c₀ then
          ((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card S : ℝ≥0∞)
            / ((columnCount (fun c => ρ c = true) j c₀ : ℕ) : ℝ≥0∞) else 0) := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun c₀ _ => ?_)
        by_cases hacc : ρ c₀
        · rw [ite_eq_left hacc, ite_eq_left hacc]
          exact expectedDraws_hitSet_le hacc j
        · rw [ite_eq_right hacc, ite_eq_right hacc]
    _ ≤ ((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card S : ℝ≥0∞) * (Fintype.card (ι → S) : ℝ≥0∞) :=
        CoordinateWise.card_mul_sum_div_columnCount_le_card j _
    _ = (Fintype.card S : ℝ≥0∞) * (((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card (ι → S) : ℝ≥0∞)) := by
        ring

/-- **The expected-query clause of Lemma 7.1.** The resampling loop looks at one table entry for
the sampled challenge and, on average, at most `k - 1` further entries per coordinate. Together
with `sub_div_le_prEvent_isSome_coordForkOp` and `coordForkOp_success` this is all three clauses
of Lemma 7.1, for the paper's algorithm, at a fixed acceptance table. -/
theorem lintegral_cost_coordForkOp_le [Nonempty S] (k : ℕ) (ρ : (ι → S) → Bool) :
    ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$> coordForkOp k ρ]
      ≤ 1 + Fintype.card ι * (k - 1 : ℕ) := by
  classical
  let _ : MeasurableSpace (ι → S) := ⊤
  let _ : MeasurableSingletonClass (ι → S) := ⟨fun _ => trivial⟩
  have hCne : (Fintype.card (ι → S) : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hCtop : (Fintype.card (ι → S) : ℝ≥0∞) ≠ ⊤ := by finiteness
  have hfin : ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹ *
      ((Fintype.card (ι → S) : ℝ≥0∞)
        + (Fintype.card ι : ℝ≥0∞) * (((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card (ι → S) : ℝ≥0∞)))
      = 1 + (Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞) := by
    rw [mul_add, ENNReal.inv_mul_cancel hCne hCtop]
    refine congrArg (1 + ·) ?_
    rw [show (Fintype.card ι : ℝ≥0∞) * (((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card (ι → S) : ℝ≥0∞))
        = ((Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞)) * (Fintype.card (ι → S) : ℝ≥0∞)
        from by ring,
      ← mul_assoc, mul_right_comm, ENNReal.inv_mul_cancel hCne hCtop, one_mul]
  have hsplit : ∀ c₀ : ι → S,
      (if ρ c₀ then
          1 + ∑ j, NegHypergeom.expectedDraws (Fintype.card S - 1) ((hitSet ρ c₀ j).card) (k - 1)
        else 1)
        = 1 + ∑ j, (if ρ c₀ then
            NegHypergeom.expectedDraws (Fintype.card S - 1) ((hitSet ρ c₀ j).card) (k - 1)
          else 0) := by
    intro c₀
    by_cases hacc : ρ c₀ <;> simp [hacc]
  rw [coordForkOp, map_bind, lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete,
    SampleableType.evalDist_uniformSample, lintegral_uniformOn_univ]
  simp only [lintegral_cost_coordForkOpAt, hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Finset.sum_comm, div_eq_mul_inv, mul_comm]
  calc (Fintype.card (ι → S) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (ι → S) : ℝ≥0∞) + ∑ j : ι, ∑ c₀ : ι → S, (if ρ c₀ then
          NegHypergeom.expectedDraws (Fintype.card S - 1) ((hitSet ρ c₀ j).card) (k - 1) else 0))
      ≤ (Fintype.card (ι → S) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (ι → S) : ℝ≥0∞)
            + ∑ _j : ι, (((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card (ι → S) : ℝ≥0∞))) :=
        mul_le_mul' le_rfl
          (add_le_add le_rfl (Finset.sum_le_sum fun j _ => sum_expectedDraws_le k ρ j))
    _ = (Fintype.card (ι → S) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (ι → S) : ℝ≥0∞)
            + (Fintype.card ι : ℝ≥0∞) * (((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card (ι → S) : ℝ≥0∞)))
          := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 1 + Fintype.card ι * (k - 1 : ℕ) := hfin

/-! ## The weighted cost

`lintegral_cost_coordForkOp_le` counts table lookups. When the entries are not all equally
expensive — as in the multi-round recursion, where looking one up means running a sub-extractor —
what is wanted instead is a *charge* `Γ` per entry. `coordForkOpW` is Figure 11 with that
accounting, and `lintegral_weight_coordForkOpW_le` bounds its expected charge by
`(1 + ℓ(k-1))` times the average charge of a single entry, which is the count bound with `Γ = 1`.

The counting step is `ProbComp.sum_lintegral_sum_map_erase_le`, applied one column at a time:
across a column's accepting centres no entry is charged more than `k - 1` times over. -/

section Weighted

variable [Nonempty S]

omit [Nonempty S] [SampleableType (ι → S)] in
/-- Summing over all challenges is summing over columns and then along each column. -/
private theorem sum_eq_sum_column (j : ι) (F : (ι → S) → ℝ≥0∞) (d : S) :
    ∑ c : ι → S, F c
      = ∑ r ∈ (Finset.univ : Finset (ι → S)).image (fun c => Function.update c j d),
          ∑ x : S, F (Function.update r j x) := by
  classical
  set reps := (Finset.univ : Finset (ι → S)).image (fun c => Function.update c j d) with hreps
  have hmaps : ∀ c ∈ (Finset.univ : Finset (ι → S)), Function.update c j d ∈ reps :=
    fun c _ => Finset.mem_image_of_mem _ (Finset.mem_univ c)
  have hrj : ∀ r ∈ reps, r j = d := by
    rintro r hr
    obtain ⟨c₀, -, rfl⟩ := Finset.mem_image.mp hr
    simp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps F]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [CoordinateWise.filter_update_eq_image (hrj r hr),
    Finset.sum_image fun x _ y _ h => Function.update_injective r j h]

omit [SampleableType (ι → S)] in
/-- **The weighted counting step.** Averaged over the sampled challenge, one coordinate's
resampling charges at most `k - 1` entries' worth. -/
theorem sum_lintegral_weight_le (k : ℕ) (ρ : (ι → S) → Bool) (Γ : (ι → S) → ℝ≥0∞) (j : ι) :
    ∑ c₀ : ι → S, (if ρ c₀ then
        ∫⁻ dd, (dd.map (fun x => Γ (Function.update c₀ j x))).sum ∂𝒟[coordDraws k ρ c₀ j]
      else 0)
      ≤ ((k - 1 : ℕ) : ℝ≥0∞) * ∑ c : ι → S, Γ c := by
  classical
  obtain ⟨d⟩ := (inferInstance : Nonempty S)
  rw [sum_eq_sum_column j _ d, sum_eq_sum_column j Γ d, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  set a : S → Bool := fun x => ρ (Function.update r j x) with ha
  set g : S → ℝ≥0∞ := fun x => Γ (Function.update r j x) with hg
  have hstep : ∀ v : S,
      (if ρ (Function.update r j v) then
          ∫⁻ dd, (dd.map
              (fun x => Γ (Function.update (Function.update r j v) j x))).sum
            ∂𝒟[coordDraws k ρ (Function.update r j v) j]
        else 0)
        = if a v then
            ∫⁻ dd, (dd.map g).sum ∂𝒟[drawUntil a (k - 1) ((Finset.univ.erase v).toList)]
          else 0 := by
    intro v
    have hupd : ∀ x : S, Function.update (Function.update r j v) j x = Function.update r j x :=
      fun x => Function.update_idem ..
    have hpool : altPool (Function.update r j v) j = (Finset.univ.erase v).toList := by
      rw [altPool, Function.update_self]
    have hdraws : coordDraws k ρ (Function.update r j v) j
        = drawUntil a (k - 1) ((Finset.univ.erase v).toList) := by
      rw [coordDraws, hpool, ha]
      exact congrArg (fun p => drawUntil p (k - 1) ((Finset.univ.erase v).toList))
        (funext fun x => by rw [hupd x])
    rw [hdraws, ha, hg]
    simp only [hupd]
  rw [Finset.sum_congr rfl fun v _ => hstep v, ← Finset.sum_filter]
  exact ProbComp.sum_lintegral_sum_map_erase_le a (k - 1) g

/-- Figure 11 with each entry examined charged `Γ` instead of counted. -/
@[expose] noncomputable def coordForkOpWAt (k : ℕ) (ρ : (ι → S) → Bool) (Γ : (ι → S) → ℝ≥0∞)
    (c₀ : ι → S) : ProbComp (Option (Finset (ι → S)) × ℝ≥0∞) :=
  if ρ c₀ then do
    let d ← Fintype.mPi (coordDraws k ρ c₀)
    let w : ℝ≥0∞ := Γ c₀ + ∑ j, ((d j).map (fun x => Γ (Function.update c₀ j x))).sum
    if ∀ j, (collected ρ c₀ d j).card = k - 1 then
      return (some (coordFamily c₀ (collected ρ c₀ d)), w)
    else return (none, w)
  else return (none, Γ c₀)

/-- The weighted fork. -/
@[expose] noncomputable def coordForkOpW (k : ℕ) (ρ : (ι → S) → Bool)
    (Γ : (ι → S) → ℝ≥0∞) : ProbComp (Option (Finset (ι → S)) × ℝ≥0∞) :=
  ($ᵗ (ι → S)) >>= coordForkOpWAt k ρ Γ

omit [Nonempty S] [SampleableType (ι → S)] in
/-- At a fixed challenge, the charge is the challenge's own plus one resampling experiment per
coordinate. -/
theorem lintegral_weight_coordForkOpWAt (k : ℕ) (ρ : (ι → S) → Bool) (Γ : (ι → S) → ℝ≥0∞)
    (c₀ : ι → S) :
    ∫⁻ w, w ∂𝒟[Prod.snd <$> coordForkOpWAt k ρ Γ c₀]
      = Γ c₀ + (if ρ c₀ then ∑ j,
          ∫⁻ dd, (dd.map (fun x => Γ (Function.update c₀ j x))).sum ∂𝒟[coordDraws k ρ c₀ j]
        else 0) := by
  classical
  rw [coordForkOpWAt]
  by_cases hacc : ρ c₀
  · rw [ite_eq_left hacc, ite_eq_left hacc, map_bind,
      lintegral_evalDist_bind_of_discrete _ _ (g := fun w : ℝ≥0∞ => w) measurable_id']
    have hinner : ∀ d : ι → List S,
        ∫⁻ w, w ∂𝒟[Prod.snd <$>
            (if ∀ j, (collected ρ c₀ d j).card = k - 1 then
                (pure (some (coordFamily c₀ (collected ρ c₀ d)),
                  Γ c₀ + ∑ j, ((d j).map (fun x => Γ (Function.update c₀ j x))).sum) :
                  ProbComp (Option (Finset (ι → S)) × ℝ≥0∞))
              else pure (none, Γ c₀ + ∑ j, ((d j).map (fun x => Γ (Function.update c₀ j x))).sum))]
          = Γ c₀ + ∑ j, ((d j).map (fun x => Γ (Function.update c₀ j x))).sum := by
      intro d
      rw [show (Prod.snd <$>
            (if ∀ j, (collected ρ c₀ d j).card = k - 1 then
                (pure (some (coordFamily c₀ (collected ρ c₀ d)),
                  Γ c₀ + ∑ j, ((d j).map (fun x => Γ (Function.update c₀ j x))).sum) :
                  ProbComp (Option (Finset (ι → S)) × ℝ≥0∞))
              else pure (none,
                Γ c₀ + ∑ j, ((d j).map (fun x => Γ (Function.update c₀ j x))).sum)))
          = (pure (Γ c₀ + ∑ j, ((d j).map (fun x => Γ (Function.update c₀ j x))).sum) :
              ProbComp ℝ≥0∞) from by split <;> rfl,
        evalDist_pure, lintegral_dirac]
    simp only [hinner]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_finsetSum _ fun _ _ => Measurable.of_discrete]
    refine congrArg (Γ c₀ + ·) (Finset.sum_congr rfl fun j _ => ?_)
    exact lintegral_evalDist_mPi_coord (coordDraws k ρ c₀)
      (fun i => (isProbabilityMeasure_evalDist_drawUntil _ _ _ _ rfl).measure_univ) j
      (fun dd => (dd.map (fun x => Γ (Function.update c₀ j x))).sum) Measurable.of_discrete
  · rw [ite_eq_right hacc, ite_eq_right hacc, add_zero,
      show (Prod.snd <$> (pure (none, Γ c₀) : ProbComp (Option (Finset (ι → S)) × ℝ≥0∞)))
        = (pure (Γ c₀) : ProbComp ℝ≥0∞) from rfl, evalDist_pure, lintegral_dirac]

/-- **The weighted cost bound.** The fork's expected charge is at most `1 + ℓ(k-1)` times the
average charge of a single entry. Taking `Γ = 1` recovers `lintegral_cost_coordForkOp_le`;
taking `Γ` to be a sub-extractor's expected cost is what multiplies the levels of the multi-round
recursion. -/
theorem lintegral_weight_coordForkOpW_le (k : ℕ)
    (ρ : (ι → S) → Bool) (Γ : (ι → S) → ℝ≥0∞) :
    ∫⁻ w, w ∂𝒟[Prod.snd <$> coordForkOpW k ρ Γ]
      ≤ (1 + Fintype.card ι * ((k - 1 : ℕ) : ℝ≥0∞))
          * ((∑ c : ι → S, Γ c) / Fintype.card (ι → S)) := by
  classical
  have hCne : (Fintype.card (ι → S) : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hCtop : (Fintype.card (ι → S) : ℝ≥0∞) ≠ ⊤ := by finiteness
  let _ : MeasurableSpace (ι → S) := ⊤
  let _ : MeasurableSingletonClass (ι → S) := ⟨fun _ => trivial⟩
  have hsplit : ∀ c₀ : ι → S,
      (if ρ c₀ then ∑ j : ι,
          ∫⁻ dd, (dd.map (fun x => Γ (Function.update c₀ j x))).sum ∂𝒟[coordDraws k ρ c₀ j]
        else 0)
        = ∑ j : ι, (if ρ c₀ then
            ∫⁻ dd, (dd.map (fun x => Γ (Function.update c₀ j x))).sum ∂𝒟[coordDraws k ρ c₀ j]
          else 0) := by
    intro c₀
    by_cases hacc : ρ c₀ <;> simp [hacc]
  rw [coordForkOpW, map_bind,
    lintegral_evalDist_bind_of_discrete _ _ (g := fun w : ℝ≥0∞ => w) measurable_id',
    SampleableType.evalDist_uniformSample, lintegral_uniformOn_univ]
  simp only [lintegral_weight_coordForkOpWAt, hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_comm, div_eq_mul_inv, mul_comm]
  calc (Fintype.card (ι → S) : ℝ≥0∞)⁻¹ *
        ((∑ c : ι → S, Γ c) + ∑ j : ι, ∑ c₀ : ι → S, (if ρ c₀ then
          ∫⁻ dd, (dd.map (fun x => Γ (Function.update c₀ j x))).sum ∂𝒟[coordDraws k ρ c₀ j]
        else 0))
      ≤ (Fintype.card (ι → S) : ℝ≥0∞)⁻¹ *
          ((∑ c : ι → S, Γ c)
            + ∑ _j : ι, ((k - 1 : ℕ) : ℝ≥0∞) * ∑ c : ι → S, Γ c) :=
        mul_le_mul' le_rfl
          (add_le_add le_rfl (Finset.sum_le_sum fun j _ => sum_lintegral_weight_le k ρ Γ j))
    _ = (1 + Fintype.card ι * ((k - 1 : ℕ) : ℝ≥0∞))
          * ((∑ c : ι → S, Γ c) / Fintype.card (ι → S)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]
        ring

/-- The form a recursion consumes: if no entry costs more than `B`, the fork costs at most
`(1 + ℓ(k-1)) · B`. Iterating this `μ` times is the paper's `(ℓ(k-1)+1)^μ`; what it still needs is
a `μ`-round extractor that runs its sub-extractor at the entries it examines rather than eagerly
at all of them. -/
theorem lintegral_weight_coordForkOpW_le_of_le (k : ℕ) (ρ : (ι → S) → Bool)
    (Γ : (ι → S) → ℝ≥0∞) {B : ℝ≥0∞} (hΓ : ∀ c, Γ c ≤ B) :
    ∫⁻ w, w ∂𝒟[Prod.snd <$> coordForkOpW k ρ Γ]
      ≤ (1 + Fintype.card ι * ((k - 1 : ℕ) : ℝ≥0∞)) * B := by
  refine (lintegral_weight_coordForkOpW_le k ρ Γ).trans (mul_le_mul' le_rfl ?_)
  have hCne : (Fintype.card (ι → S) : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hCtop : (Fintype.card (ι → S) : ℝ≥0∞) ≠ ⊤ := by finiteness
  refine ENNReal.div_le_of_le_mul ?_
  calc ∑ c : ι → S, Γ c
      ≤ ∑ _c : ι → S, B := Finset.sum_le_sum fun c _ => hΓ c
    _ = B * Fintype.card (ι → S) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

omit [Nonempty S] [SampleableType (ι → S)] in
/-- Charging instead of counting does not change what the fork *returns*. -/
theorem map_fst_coordForkOpWAt (k : ℕ) (ρ : (ι → S) → Bool) (Γ : (ι → S) → ℝ≥0∞)
    (c₀ : ι → S) :
    (·.1) <$> coordForkOpWAt k ρ Γ c₀ = (·.1) <$> coordForkOpAt k ρ c₀ := by
  classical
  rw [coordForkOpWAt, coordForkOpAt]
  by_cases hacc : ρ c₀
  · rw [ite_eq_left hacc, ite_eq_left hacc, map_bind, map_bind]
    refine bind_congr fun d => ?_
    by_cases hcond : ∀ j, (collected ρ c₀ d j).card = k - 1 <;> simp [hcond]
  · rw [ite_eq_right hacc, ite_eq_right hacc]
    simp

omit [Nonempty S] in
/-- The same, for the whole fork. -/
theorem map_fst_coordForkOpW (k : ℕ) (ρ : (ι → S) → Bool) (Γ : (ι → S) → ℝ≥0∞) :
    (·.1) <$> coordForkOpW k ρ Γ = (·.1) <$> coordForkOp k ρ := by
  rw [coordForkOpW, coordForkOp, map_bind, map_bind]
  exact bind_congr fun c₀ => map_fst_coordForkOpWAt k ρ Γ c₀

end Weighted

end Op

end OracleComp
