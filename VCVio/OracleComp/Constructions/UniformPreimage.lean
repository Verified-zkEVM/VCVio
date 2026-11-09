/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.EvalDist.DiscreteTVDistFintype

/-!
# Uniform sampling from finite preimages

Sampling a fresh uniform preimage after observing a deterministic image preserves the original
uniform law. The same fiber decomposition identifies the total-variation loss when the target
is drawn uniformly instead of from the image distribution.

Samplers are `ProbComp`s; laws are output measures `𝒟[·]`, and distances are `discreteTVDist`.

## References

* A. Chiesa, M. Orrù, *A Fiat–Shamir Transformation From Duplex Sponges*, ePrint 2025/536,
  version of March 27, 2026, Claim 7.9 (pp. 56–57): the uniform-resampling law
  `bind_sampleUniformPreimage_eq_uniform`.
-/

public section

open OracleComp MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OracleComp.UniformPreimage

section UniformPreimage

variable {A B : Type}

/-- The fiber of `ψ` over `a`. -/
abbrev Preimage (ψ : B → A) (a : A) := { b : B // ψ b = a }

/-- Surjectivity provides a canonical nonempty witness for each fiber. -/
theorem preimage_nonempty (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) :
    Nonempty (Preimage ψ a) := by
  rcases hψ a with ⟨b, rfl⟩
  exact ⟨⟨b, rfl⟩⟩

variable [DecidableEq A] [Fintype B]

/-- Sample a uniformly random preimage of `a` under `ψ`. The fiber is sampled by enumeration
(`SampleableType.ofFintype`). -/
@[expose] noncomputable def sampleUniformPreimage (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) :
    ProbComp B :=
  letI := preimage_nonempty ψ hψ a
  letI : SampleableType (Preimage ψ a) := SampleableType.ofFintype _
  Subtype.val <$> ($ᵗ (Preimage ψ a))

/-- Pointwise description of `sampleUniformPreimage`.
Probability of sampling `b` from the fiber of `a` = `1/|fiber_{a}|` or `0` -/
theorem sampleUniformPreimage_apply [MeasurableSpace B] [MeasurableSingletonClass B]
    (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) (b : B) :
    𝒟[sampleUniformPreimage ψ hψ a] {b} =
      if ψ b = a then (Fintype.card (Preimage ψ a) : ℝ≥0∞)⁻¹ else 0 := by
  let _ := preimage_nonempty ψ hψ a
  let _ : SampleableType (Preimage ψ a) := SampleableType.ofFintype _
  let _ : MeasurableSpace (Preimage ψ a) := ⊤
  rw [sampleUniformPreimage, evalDist_map_of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton b)]
  split_ifs with h
  · have hpre : (Subtype.val ⁻¹' {b} : Set (Preimage ψ a)) = {⟨b, h⟩} := by
      ext x
      simp [Subtype.ext_iff]
    rw [hpre, SampleableType.evalDist_uniformSample_singleton]
  · have hpre : (Subtype.val ⁻¹' {b} : Set (Preimage ψ a)) = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact h (hx ▸ x.2)
    rw [hpre, measure_empty]

/-- The uniform preimage sampler never fails. -/
instance (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) [MeasurableSpace B] :
    IsProbabilityMeasure 𝒟[sampleUniformPreimage ψ hψ a] := by
  unfold sampleUniformPreimage
  infer_instance

/-- Observing the image of a uniform sample and resampling a uniform preimage of it preserves the
uniform law. -/
theorem bind_sampleUniformPreimage_eq_uniform [SampleableType B] [MeasurableSpace B]
    [MeasurableSingletonClass B]
    (ψ : B → A) (hψ : Function.Surjective ψ) :
    𝒟[do
      let b' ← $ᵗ B
      sampleUniformPreimage ψ hψ (ψ b')] = 𝒟[$ᵗ B] := by
  classical
  apply Measure.ext_of_singleton
  intro b
  let c : ℝ≥0∞ := (Fintype.card (Preimage ψ (ψ b)) : ℝ≥0∞)⁻¹
  have hcard : (Fintype.card (Preimage ψ (ψ b)) : ℝ≥0∞) ≠ 0 := by
    let _ := preimage_nonempty ψ hψ (ψ b)
    exact_mod_cast Fintype.card_ne_zero
  let s : Finset B := Finset.univ.filter fun b' => ψ b' = ψ b
  have hs_card : s.card = Fintype.card (Preimage ψ (ψ b)) := by
    simpa [s, Preimage] using (Fintype.card_subtype (fun b' : B => ψ b' = ψ b)).symm
  rw [evalDist_bind_of_discrete, Measure.bind_apply (measurableSet_singleton b)
    Measurable.of_discrete.aemeasurable, lintegral_fintype,
    SampleableType.evalDist_uniformSample_singleton]
  simp only [SampleableType.evalDist_uniformSample_singleton, sampleUniformPreimage_apply]
  have hterm (x : B) :
      (if ψ b = ψ x then (Fintype.card (Preimage ψ (ψ x)) : ℝ≥0∞)⁻¹ else 0) *
          (Fintype.card B : ℝ≥0∞)⁻¹ =
        if ψ x = ψ b then c * (Fintype.card B : ℝ≥0∞)⁻¹ else 0 := by
    by_cases hx : ψ x = ψ b
    · simp [hx, c]
    · simp [hx, Ne.symm hx]
  simp_rw [hterm]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hs_card,
    ← mul_assoc, ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top _), one_mul]

end UniformPreimage

/-! ## The fiber-grouping identity -/

section FiberGrouping

variable {A B : Type} [DecidableEq A] [Fintype B]

/-- Pointwise value of resampling a fiber of a uniform output of `A`:
each `b` receives mass `1 / (|A| · |ψ⁻¹(ψ b)|)`. -/
lemma bind_sampleUniformPreimage_uniform_apply [Fintype A] [SampleableType A]
    (ψ : B → A) (hψ : Function.Surjective ψ) (b : B) :
    Pr{let x ← ($ᵗ A >>= sampleUniformPreimage ψ hψ)}[x = b]
      = (Fintype.card A : ℝ≥0∞)⁻¹ * (Fintype.card (Preimage ψ (ψ b)) : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace A := ⊤
  let : MeasurableSpace B := ⊤
  rw [prEvent_eq_evalDist_singleton, evalDist_bind_of_discrete,
    Measure.bind_apply (measurableSet_singleton _) Measurable.of_discrete.aemeasurable,
    lintegral_fintype]
  simp only [SampleableType.evalDist_uniformSample_singleton, sampleUniformPreimage_apply]
  rw [Finset.sum_eq_single (ψ b) (fun a _ ha => by simp [Ne.symm ha])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp only [↓reduceIte]
  rw [mul_comm]

/-- Pointwise value of the pushforward of the uniform law on `B`: each `a` receives mass
`|ψ⁻¹(a)| / |B|`. -/
lemma map_uniform_apply_fiber [SampleableType B] (ψ : B → A) (a : A) :
    Pr{let x ← ψ <$> ($ᵗ B)}[x = a]
      = (Fintype.card (Preimage ψ a) : ℝ≥0∞) * (Fintype.card B : ℝ≥0∞)⁻¹ := by
  classical
  rw [prEvent_map, SampleableType.prEvent_uniformSample, div_eq_mul_inv]
  congr 2
  rw [Fintype.card_subtype]

/-- **Fiber-grouping identity.** Resampling a uniform fiber of a uniformly chosen output is exactly
as far from uniform as the pushforward of the uniform distribution is. Grouping the `L¹` sum over
`B` by the fibers of `ψ` matches the terms of the `L¹` sum over `A` one for one. -/
theorem discreteTVDist_bind_sampleUniformPreimage_uniform_eq_discreteTVDist_map
    [SampleableType A] [SampleableType B] (ψ : B → A) (hψ : Function.Surjective ψ) :
    discreteTVDist ($ᵗ A >>= sampleUniformPreimage ψ hψ) ($ᵗ B)
      = discreteTVDist (ψ <$> ($ᵗ B)) ($ᵗ A) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  rw [discreteTVDist.eq_half_sum_abs, discreteTVDist.eq_half_sum_abs]
  congr 1
  simp only [bind_sampleUniformPreimage_uniform_apply, map_uniform_apply_fiber,
    SampleableType.prEvent_uniformSample_eq_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  -- Group the `B`-sum along the fibers of `ψ`.
  rw [← Finset.sum_fiberwise_of_maps_to (g := ψ) (fun b _ => Finset.mem_univ (ψ b))
    (fun b => |(Fintype.card A : ℝ)⁻¹ * (Fintype.card (Preimage ψ (ψ b)) : ℝ)⁻¹
      - (Fintype.card B : ℝ)⁻¹|)]
  refine Finset.sum_congr rfl fun a _ => ?_
  -- On the fiber over `a`, every term is the same; there are `|ψ⁻¹(a)|` of them.
  have hfib : ∀ b ∈ Finset.univ.filter (fun b => ψ b = a),
      |(Fintype.card A : ℝ)⁻¹ * (Fintype.card (Preimage ψ (ψ b)) : ℝ)⁻¹
          - (Fintype.card B : ℝ)⁻¹|
        = |(Fintype.card A : ℝ)⁻¹ * (Fintype.card (Preimage ψ a) : ℝ)⁻¹
            - (Fintype.card B : ℝ)⁻¹| := by
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [hb.2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype]
  have hc_pos : (0 : ℝ) < (Fintype.card (Preimage ψ a) : ℝ) := by
    have : Nonempty (Preimage ψ a) := preimage_nonempty ψ hψ a
    exact_mod_cast Fintype.card_pos
  rw [← abs_of_pos hc_pos, ← abs_mul, mul_sub, abs_of_pos hc_pos]
  rw [mul_left_comm _ (Fintype.card A : ℝ)⁻¹,
    mul_inv_cancel₀ (ne_of_gt hc_pos), mul_one, abs_sub_comm]

end FiberGrouping

/-- A sampled preimage still decodes to its target when the target is retained in the output
pair. -/
theorem map_sampleUniformPreimage_decode_pair
    {A B : Type} [DecidableEq A] [Fintype B]
    (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) :
    (fun b => (ψ b, b)) <$> sampleUniformPreimage ψ hψ a =
      (fun b => (a, b)) <$> sampleUniformPreimage ψ hψ a := by
  simp only [sampleUniformPreimage, Functor.map_map]
  congr 1
  funext b
  rw [b.property]

/-- Every supported preimage decodes to the target whose fiber was sampled. -/
theorem mem_support_sampleUniformPreimage {A B : Type} [DecidableEq A] [Fintype B]
    (f : B → A) (hf : Function.Surjective f) (a : A) {b : B}
    (hb : b ∈ support (sampleUniformPreimage f hf a)) : f b = a := by
  unfold sampleUniformPreimage at hb
  rw [support_map] at hb
  obtain ⟨p, -, rfl⟩ := hb
  exact p.2

/-- Resampling the uniform fiber preserves the joint law of image and preimage. -/
theorem bind_uniform_fiber_observe
    {A B C : Type} [DecidableEq A] [Fintype B] [SampleableType B] [MeasurableSpace C]
    (f : B → A) (hf : Function.Surjective f) (k : A → B → ProbComp C) :
    𝒟[($ᵗ B) >>= fun b =>
      sampleUniformPreimage f hf (f b) >>= k (f b)] =
    𝒟[($ᵗ B) >>= fun b => k (f b) b] := by
  calc
    _ = 𝒟[($ᵗ B) >>= fun b =>
        sampleUniformPreimage f hf (f b) >>= fun b' => k (f b') b'] := by
      refine evalDist_bind_congr _ _ _ fun b => ?_
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun b' hb' => ?_
      rw [mem_support_sampleUniformPreimage f hf (f b) hb']
    _ = _ := by
      let : MeasurableSpace B := ⊤
      rw [← bind_assoc]
      exact ((evalDistEq_iff_evalDist_eq.mpr
        (bind_sampleUniformPreimage_eq_uniform f hf)).bind_left _).evalDist_eq

end OracleComp.UniformPreimage
