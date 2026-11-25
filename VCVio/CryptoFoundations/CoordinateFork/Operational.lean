/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToCslib.Probability.UniformOn
public import VCVio.CryptoFoundations.CoordinateFork
public import VCVio.CryptoFoundations.CoordinateFork.BlockOperational
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

The expected-query clause holds too. `coordForkOp` pairs its result with the number of lookups,
and `lintegral_cost_coordForkOp_le` bounds that number's expectation by the paper's
`1 + ℓ(k - 1)`. `isFinder_coordFinder` in `CoordinateFork/Finder.lean` states the same bound as the
cost clause of a black-box finder. Only the total-table core in `CoordinateFork.lean` leaves cost
out.
-/

public section

open Finset CoordinateWise OracleComp ProbComp MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace OracleComp

variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]
variable {k : ℕ} {ρ : (ι → S) → Bool} {c₀ : ι → S} {d : ι → List S}

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
    if ∀ j, ((d j).filter fun x => ρ (Function.update c₀ j x)).length = k - 1 then
      return (some (coordFamily c₀ (collected ρ c₀ d)), cost)
    else return (none, cost)
  else return (none, 1)

/-- **Figure 11 of Fenzi–Moghaddas–Nguyen**, against a fixed acceptance table. -/
@[expose] noncomputable def coordForkOp [SampleableType (ι → S)] (k : ℕ) (ρ : (ι → S) → Bool) :
    ProbComp (Option (Finset (ι → S)) × ℕ) :=
  ($ᵗ (ι → S)) >>= coordForkOpAt k ρ

/-! ## One alphabet and one threshold -/

/-- With one alphabet and one threshold, the block loop is the coordinate-wise loop
`coordForkOpAt`: the neighbours it draws are the values `coordForkOpAt` draws, written into the
centre. -/
theorem blockForkOpAt_const (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) :
    blockForkOpAt (S := fun _ => S) (fun _ => k) ρ c₀ = coordForkOpAt k ρ c₀ := by
  classical
  have hdraws : ∀ j, blockDraws (S := fun _ => S) (fun _ => k) ρ c₀ j =
      List.map (Function.update c₀ j) <$> coordDraws k ρ c₀ j := by
    intro j
    rw [blockDraws, neighbourPool, coordDraws]
    exact ProbComp.drawUntil_map _ _ _ _ _ rfl
  have hcol : ∀ (d : ι → List S) (j : ι),
      blockCollected ρ (fun j => (d j).map (Function.update c₀ j)) j =
        (collected ρ c₀ d j).image (Function.update c₀ j) := by
    intro d j
    ext x
    simp [blockCollected, collected, List.filter_map, Function.comp_def]
  unfold blockForkOpAt coordForkOpAt
  by_cases hacc : ρ c₀ = true
  · rw [ite_eq_left hacc, ite_eq_left hacc]
    have hd' : blockDraws (S := fun _ => S) (fun _ => k) ρ c₀ =
        fun j => List.map (Function.update c₀ j) <$> coordDraws k ρ c₀ j := funext hdraws
    rw [hd', ← Fintype.mPi_map, bind_map_left]
    refine bind_congr fun d => ?_
    have hfam : blockCollected ρ (fun j => (d j).map (Function.update c₀ j)) =
        fun j => (collected ρ c₀ d j).image (Function.update c₀ j) := funext (hcol d)
    simp only [hfam, List.filter_map, List.length_map, Function.comp_def,
      coordFamily_eq_neighbourFamily]
  · rw [ite_eq_right hacc, ite_eq_right hacc]

/-! ## Success and output -/

section Op

variable [SampleableType (ι → S)]

/-- With one alphabet and one threshold, the block loop is the coordinate-wise loop. -/
theorem blockForkOp_const (k : ℕ) (ρ : (ι → S) → Bool) :
    blockForkOp (S := fun _ => S) (fun _ => k) ρ = coordForkOp k ρ := by
  unfold blockForkOp coordForkOp
  exact bind_congr fun c₀ => blockForkOpAt_const k ρ c₀

omit [SampleableType (ι → S)] in
/-- **The output guarantee.** A successful run returns a coordinate-wise `k`-special sound set of
challenges the table accepts. -/
theorem coordForkOpAt_success {X : Finset (ι → S)} {cost : ℕ}
    (h : (some X, cost) ∈ support (coordForkOpAt k ρ c₀)) :
    IsCoordSpecialSound k X ∧ ∀ c ∈ X, ρ c := by
  rw [← blockForkOpAt_const] at h
  obtain ⟨hX, hacc⟩ := blockForkOpAt_success h
  exact ⟨isCoordSpecialSound_iff_isBlockSpecialSound.2 hX, hacc⟩

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
  rw [← blockForkOpAt_const]
  exact prEvent_isSome_blockForkOpAt _ ρ c₀

/-- **The success probability of Figure 11.** The loop succeeds exactly as often as the
deterministic table core: on `goodSet k ρ`, the challenges whose every column holds at least `k`
accepting values. -/
theorem prEvent_isSome_coordForkOp (k : ℕ) (ρ : (ι → S) → Bool) :
    Pr{let r ← coordForkOp k ρ}[r.1.isSome]
      = ((goodSet k ρ).card : ℝ≥0∞) / Fintype.card (ι → S) := by
  rw [← blockForkOp_const]
  exact prEvent_isSome_blockForkOp _ ρ

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
  rw [← blockForkOpAt_const]
  exact lintegral_cost_blockForkOpAt _ ρ c₀

/-- **The expected-query clause of Lemma 7.1.** The resampling loop looks at one table entry for
the sampled challenge and, on average, at most `k - 1` further entries per coordinate. Together
with `sub_div_le_prEvent_isSome_coordForkOp` and `coordForkOp_success` this is all three clauses
of Lemma 7.1, for the paper's algorithm, at a fixed acceptance table. -/
theorem lintegral_cost_coordForkOp_le (k : ℕ) (ρ : (ι → S) → Bool) :
    ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$> coordForkOp k ρ]
      ≤ 1 + Fintype.card ι * (k - 1 : ℕ) := by
  rw [← blockForkOp_const]
  refine (lintegral_cost_blockForkOp_le _ ρ).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## The weighted cost

`lintegral_cost_coordForkOp_le` counts table lookups. When the entries are not all equally
expensive — as in the multi-round recursion, where looking one up means running a sub-extractor —
what is wanted instead is a *charge* `Γ` per entry. `coordForkOpW` is Figure 11 with that
accounting, and `lintegral_weight_coordForkOpW_le` bounds its expected charge by
`(1 + ℓ(k-1))` times the average charge of a single entry, which is the count bound with `Γ = 1`.

The counting step is `ProbComp.sum_lintegral_sum_map_erase_le`, applied one column at a time:
across a column's accepting centres no entry is charged more than `k - 1` times over. -/

section Weighted

variable [Nonempty S] [MeasurableSpace (List S)] [DiscreteMeasurableSpace (List S)]

omit [Nonempty S] [SampleableType (ι → S)] [MeasurableSpace (List S)]
  [DiscreteMeasurableSpace (List S)] in
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
    if ∀ j, ((d j).filter fun x => ρ (Function.update c₀ j x)).length = k - 1 then
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
            (if ∀ j, ((d j).filter fun x => ρ (Function.update c₀ j x)).length = k - 1 then
                (pure (some (coordFamily c₀ (collected ρ c₀ d)),
                  Γ c₀ + ∑ j, ((d j).map (fun x => Γ (Function.update c₀ j x))).sum) :
                  ProbComp (Option (Finset (ι → S)) × ℝ≥0∞))
              else pure (none, Γ c₀ + ∑ j, ((d j).map (fun x => Γ (Function.update c₀ j x))).sum))]
          = Γ c₀ + ∑ j, ((d j).map (fun x => Γ (Function.update c₀ j x))).sum := by
      intro d
      rw [show (Prod.snd <$>
            (if ∀ j, ((d j).filter fun x => ρ (Function.update c₀ j x)).length = k - 1 then
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

omit [MeasurableSpace (List S)] [DiscreteMeasurableSpace (List S)] in
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
  -- The statement observes only the total charge; the draws are integrated with discrete lists.
  let _ : MeasurableSpace (List S) := ⊤
  have _ : DiscreteMeasurableSpace (List S) := ⟨fun _ => trivial⟩
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

omit [MeasurableSpace (List S)] [DiscreteMeasurableSpace (List S)] in
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

omit [Nonempty S] [SampleableType (ι → S)] [MeasurableSpace (List S)]
  [DiscreteMeasurableSpace (List S)] in
/-- Charging instead of counting does not change what the fork *returns*. -/
theorem map_fst_coordForkOpWAt (k : ℕ) (ρ : (ι → S) → Bool) (Γ : (ι → S) → ℝ≥0∞)
    (c₀ : ι → S) :
    (·.1) <$> coordForkOpWAt k ρ Γ c₀ = (·.1) <$> coordForkOpAt k ρ c₀ := by
  classical
  rw [coordForkOpWAt, coordForkOpAt]
  by_cases hacc : ρ c₀
  · rw [ite_eq_left hacc, ite_eq_left hacc, map_bind, map_bind]
    refine bind_congr fun d => ?_
    by_cases hcond : ∀ j, ((d j).filter fun x => ρ (Function.update c₀ j x)).length = k - 1 <;>
      simp [hcond]
  · rw [ite_eq_right hacc, ite_eq_right hacc]
    simp

omit [Nonempty S] [MeasurableSpace (List S)] [DiscreteMeasurableSpace (List S)] in
/-- The same, for the whole fork. -/
theorem map_fst_coordForkOpW (k : ℕ) (ρ : (ι → S) → Bool) (Γ : (ι → S) → ℝ≥0∞) :
    (·.1) <$> coordForkOpW k ρ Γ = (·.1) <$> coordForkOp k ρ := by
  rw [coordForkOpW, coordForkOp, map_bind, map_bind]
  exact bind_congr fun c₀ => map_fst_coordForkOpWAt k ρ Γ c₀

end Weighted

/-! ## Carrying the prover's responses

`coordForkOp` reports which challenges it found; Lemma 7.1 asks for the accepting *transcripts*.
`coordForkOpT` is the same loop run against the acceptance table a response table induces,
returning that table alongside the challenge set — exactly what `coordForkT` is to `coordFork`,
and the object `CoordinateFork/Extraction.lean` names as the extractor. All three clauses
transport: the output is `ℓ(k-1)+1` verifier-accepting transcripts whose challenges are
`SS(S, ℓ, k)`, the success probability is unchanged, and so is the lookup count.

The response type carries no measurable structure, so the proofs introduce the discrete one where
the averaging step needs it rather than the statements carrying it. -/

section Transcripts

variable {Y : Type} [DecidableEq Y]

/-- Figure 11 with the prover's responses carried alongside. -/
@[expose] noncomputable def coordForkOpT (V : (ι → S) → Y → Bool) (k : ℕ)
    (D : ProbComp ((ι → S) → Y)) :
    ProbComp (Option (((ι → S) → Y) × Finset (ι → S)) × ℕ) := do
  let τ ← D
  let r ← coordForkOp k fun c => V c (τ c)
  return (r.1.map fun X => (τ, X), r.2)

/-- **The output clause of Lemma 7.1 with responses.** A successful run returns `ℓ(k-1)+1`
transcripts that the verifier accepts, whose challenges form an `SS(S, ℓ, k)` set. -/
theorem coordForkOpT_success (V : (ι → S) → Y → Bool) (k : ℕ) (D : ProbComp ((ι → S) → Y))
    {p : ((ι → S) → Y) × Finset (ι → S)} {cost : ℕ}
    (h : (some p, cost) ∈ support (coordForkOpT V k D)) :
    GoodTranscripts V k (some p) := by
  rw [coordForkOpT, mem_support_bind_iff] at h
  obtain ⟨τ, -, h⟩ := h
  rw [mem_support_bind_iff] at h
  obtain ⟨⟨r₁, r₂⟩, hr, h⟩ := h
  rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
  obtain ⟨hopt, -⟩ := h
  rcases r₁ with _ | X
  · simp at hopt
  · obtain rfl : p = (τ, X) := by simpa [eq_comm] using hopt
    rw [goodTranscripts_some_iff]
    exact coordForkOp_success hr

omit [DecidableEq Y] in
/-- **The success clause with responses.** The loop's first component is `some` exactly as often
as the acceptance-table loop's is, averaged over the response table. -/
theorem prEvent_isSome_coordForkOpT (V : (ι → S) → Y → Bool) (k : ℕ)
    (D : ProbComp ((ι → S) → Y)) :
    Pr{let r ← coordForkOpT V k D}[r.1.isSome] = forkSuccOf k (acceptTable V D) := by
  classical
  let _ : MeasurableSpace ((ι → S) → Y) := ⊤
  let _ : DiscreteMeasurableSpace ((ι → S) → Y) := ⟨fun _ => trivial⟩
  have hinner : ∀ τ : (ι → S) → Y,
      Pr{let r ← (coordForkOp k (fun c => V c (τ c)) >>= fun r =>
          pure (r.1.map fun X => (τ, X), r.2))}[r.1.isSome]
        = ((goodSet k (fun c => V c (τ c))).card : ℝ≥0∞) / Fintype.card (ι → S) := by
    intro τ
    rw [← prEvent_isSome_coordForkOp k (fun c => V c (τ c)),
      show (coordForkOp k (fun c => V c (τ c)) >>= fun r =>
          pure (r.1.map fun X => (τ, X), r.2))
        = (fun r : Option (Finset (ι → S)) × ℕ => (r.1.map fun X => (τ, X), r.2)) <$>
            coordForkOp k (fun c => V c (τ c)) from by rw [map_eq_bind_pure_comp]; rfl,
      prEvent_map]
    exact prEvent_congr _ _ _ fun r => by cases r.1 <;> simp
  rw [coordForkOpT, prEvent_bind_eq_lintegral_of_discrete]
  simp only [hinner]
  rw [forkSuccOf, acceptTable,
    lintegral_evalDist_map_of_discrete D (f := fun (τ : (ι → S) → Y) c => V c (τ c))
      (g := fun ρ => ((goodSet k ρ).card : ℝ≥0∞) / Fintype.card (ι → S))]

/-- Succeeding and returning good transcripts are the same event. -/
theorem prEvent_goodTranscripts_coordForkOpT (V : (ι → S) → Y → Bool) (k : ℕ)
    (D : ProbComp ((ι → S) → Y)) :
    Pr{let r ← coordForkOpT V k D}[GoodTranscripts V k r.1]
      = Pr{let r ← coordForkOpT V k D}[r.1.isSome] := by
  refine le_antisymm (prEvent_mono_of_support _ _ _ fun r _ hr => ?_)
    (prEvent_mono_of_support _ _ _ fun r hr hs => ?_)
  · obtain ⟨τ, X, hEq, -, -⟩ := hr
    rw [hEq]; rfl
  · obtain ⟨⟨o, n⟩, rfl⟩ : ∃ q : Option (((ι → S) → Y) × Finset (ι → S)) × ℕ, q = r := ⟨r, rfl⟩
    rcases o with _ | p
    · simp at hs
    · exact coordForkOpT_success V k D hr

/-- **Lemma 7.1 for the paper's algorithm, with responses.** The resampling loop returns
`ℓ(k-1)+1` verifier-accepting transcripts whose challenges form an `SS(S, ℓ, k)` set, with
probability at least `ε - ℓ(k-1)/N`. -/
theorem sub_div_le_prEvent_goodTranscripts_coordForkOpT [Nonempty S] (V : (ι → S) → Y → Bool)
    (k : ℕ) (D : ProbComp ((ι → S) → Y)) :
    acceptRatio (acceptTable V D) - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ Pr{let r ← coordForkOpT V k D}[GoodTranscripts V k r.1] := by
  rw [prEvent_goodTranscripts_coordForkOpT, prEvent_isSome_coordForkOpT]
  exact sub_div_le_lintegral_card_goodSet (acceptTable V D) k

omit [DecidableEq Y] in
/-- **The expected-lookup clause with responses**, unchanged by carrying the table. -/
theorem lintegral_cost_coordForkOpT_le (V : (ι → S) → Y → Bool) (k : ℕ)
    (D : ProbComp ((ι → S) → Y)) :
    ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$> coordForkOpT V k D]
      ≤ 1 + Fintype.card ι * (k - 1 : ℕ) := by
  classical
  let _ : MeasurableSpace ((ι → S) → Y) := ⊤
  let _ : DiscreteMeasurableSpace ((ι → S) → Y) := ⟨fun _ => trivial⟩
  rw [coordForkOpT, map_bind, lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete]
  refine (lintegral_mono fun τ => ?_).trans (by rw [lintegral_const, measure_univ, mul_one])
  have hmap : (Prod.snd <$> (coordForkOp k (fun c => V c (τ c)) >>= fun r =>
      pure (r.1.map fun X => (τ, X), r.2)))
      = Prod.snd <$> coordForkOp k (fun c => V c (τ c)) := by
    rw [map_bind, map_eq_bind_pure_comp]
    exact bind_congr fun r => rfl
  rw [hmap]
  exact lintegral_cost_coordForkOp_le k fun c => V c (τ c)

end Transcripts

end Op

end OracleComp
