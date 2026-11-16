/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.Falcon.PackedFFT
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.OracleComp.EvalDist.Measure
public import ToMathlib.Probability.Divergence.RenyiTotalVariation
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Min-entropy of the fast Fourier sampler

`Primitives.ffSampling` is a Klein-style sampler: every leaf draws four integers from the
one-dimensional sampler `samplerZ` and every node merges the two half-size outputs, an injective
operation (`Primitives.mergeFFT_injective`). Hence the largest pointwise mass of its output is at
most the product of the largest pointwise masses of the `4 · 2^κ` leaf draws
(`Primitives.ffSampling_pointMass_le`). The sampler envelope `Primitives.SamplerEnvelope δ`
also gives the bound `(1 / (σ_min √(2π) - 1) + δ) ^ (4 · 2^κ)` and its half-power corollary.
These are bounds on the FFT-domain sample before reduction modulo `q`.

The hypotheses concern point masses of the actual finite-support `ProbComp` leaf sampler.
An exact discrete-Gaussian law has infinite support and cannot hold for such a computation
(`LatticeCrypto.evalDist_ne_discreteGaussianMeasure`). `Primitives.SamplerQuality` is the
satisfiable replacement, a forward Rényi bound of order `a > 1`, and it implies the envelope
(`Primitives.samplerEnvelope_of_samplerQuality`). Neither law is established for the concrete
sampler; the arithmetic facts about Falcon's parameter sets do not establish them. Likewise,
shortness of a modular output does not make its unreduced preimage unique; no point-mass bound
for the modular PSF output follows here.
-/

public section

open OracleComp OracleSpec LatticeCrypto InformationTheory
open MeasureTheory
open scoped ENNReal

namespace Falcon

/-! ## A bind whose continuation can produce the output from at most one input -/

/-- If the first computation has pointwise mass at most `M`, every continuation has pointwise
mass at most `B` at `y`, and at most one input to the continuation can produce `y`, then the
bind has pointwise mass at most `M * B` at `y`. -/
theorem pointMass_bind_le_mul {α β : Type} (mx : ProbComp α) (my : α → ProbComp β) (y : β)
    {M B : ℝ≥0∞} (hM : ∀ x, Pr{let a ← mx}[a = x] ≤ M)
    (hB : ∀ x, Pr{let b ← my x}[b = y] ≤ B)
    (huniq : ∀ x₁ x₂, Pr{let b ← my x₁}[b = y] ≠ 0 →
      Pr{let b ← my x₂}[b = y] ≠ 0 → x₁ = x₂) :
    Pr{let b ← mx >>= my}[b = y] ≤ M * B := by
  classical
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete]
  rcases Classical.em (∀ x, Pr{let b ← my x}[b = y] = 0) with h | h
  · simp only [h, lintegral_const, zero_mul, zero_le]
  · obtain ⟨x₀, hx₀⟩ := not_forall.mp h
    calc
      _ ≤ ∫⁻ x, ({x₀} : Set α).indicator (fun _ => B) x ∂𝒟[mx] := by
        apply lintegral_mono
        intro x
        change Pr{let b ← my x}[b = y] ≤ ({x₀} : Set α).indicator (fun _ => B) x
        rcases Classical.em (x = x₀) with hx | hx
        · subst x
          simpa only [Set.indicator_of_mem (Set.mem_singleton x₀)] using hB x₀
        · have hz : Pr{let b ← my x}[b = y] = 0 := by
            by_contra hy
            exact hx (huniq x x₀ hy hx₀)
          rw [hz, Set.indicator_of_notMem
            (show x ∉ ({x₀} : Set α) from hx)]
      _ = B * Pr{let x ← mx}[x = x₀] := by
        rw [lintegral_indicator_const (measurableSet_singleton x₀),
          prEvent_eq_evalDist_singleton]
      _ ≤ M * B := by
        rw [mul_comm B]
        exact mul_le_mul (hM x₀) le_rfl zero_le zero_le

private theorem pointMass_eq_zero_iff {α : Type} (mx : ProbComp α) (x : α) :
    Pr{let a ← mx}[a = x] = 0 ↔ x ∉ support mx := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_singleton]
  simpa only [not_lt, nonpos_iff_eq_zero] using
    (not_congr (mem_support_iff_evalDist_singleton_pos mx x)).symm

/-! ## No finite-support sampler meets the exact law -/

/-- No `ProbComp` has the discrete Gaussian as its output law: a `ProbComp` has finite support,
while for `σ > 0` the discrete Gaussian gives positive mass to every integer
(`discreteGaussianPMF_pos`). -/
theorem _root_.LatticeCrypto.evalDist_ne_discreteGaussianMeasure (mx : ProbComp ℤ) {σ : ℝ}
    (hσ : 0 < σ) (μ : ℝ) :
    (𝒟[mx] : Measure ℤ) ≠ discreteGaussianMeasure σ μ := by
  intro h
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (finSupport mx)
  have h0 := (pointMass_eq_zero_iff mx z).2
    fun hs => hz ((mem_finSupport_iff_mem_support _ _).2 hs)
  rw [prEvent_eq_evalDist_singleton, h] at h0
  exact (discreteGaussianMeasure_singleton_pos σ μ hσ z).ne' h0

/-! ## Sampler laws -/

/-- **Sampler envelope** with additive slack `δ`: at every center and every standard deviation
`σ' ∈ [σ_min, σ_max]` (the range Falcon v1.2 Section 3.9.3 guarantees for `ffSampling` leaves),
every integer has mass at most `1 / (σ'√(2π) - 1) + δ`. The bound is meaningful when
`1 < σ_min √(2π)`, as for both Falcon parameter sets; the ideal discrete Gaussian then meets it
with `δ = 0` (`discreteGaussianMeasure_singleton_le`).

The envelope bounds min-entropy only, not closeness to the Gaussian: a sampler that ignores `μ`
and `σ'` can meet it, and a uniform draw from `{0, 1, 2, 3}` meets `SamplerEnvelope 0` at
Falcon-512. Closeness to the Gaussian is `Primitives.SamplerQuality`. -/
structure Primitives.SamplerEnvelope {p : Params} (prims : Primitives p) (δ : ℝ≥0∞) : Prop where
  /-- Every point mass of `samplerZ μ σ'` is within `δ` of the ideal guessing bound. -/
  pointMass_le : ∀ (μ σ' : ℝ), p.sigmaMin ≤ σ' → σ' ≤ p.sigmaMax → ∀ v : ℤ,
    Pr{let outcome ← prims.samplerZ μ σ'}[outcome = v] ≤
      ENNReal.ofReal (1 / (σ' * Real.sqrt (2 * Real.pi) - 1)) + δ

/-- **Sampler quality**: for an order `a > 1`, the forward Rényi divergence of order `a` from the
output law of `samplerZ μ σ'` to `D_{ℤ,σ',μ}` is at most `1 + ε` for every center and every
`σ' ∈ [σ_min, σ_max]`. The forward direction is finite for a finite-support sampler; the bound
`1 < a` is part of the law, since `renyiDiv a` is `1` for `a ≤ 1`. -/
structure Primitives.SamplerQuality {p : Params} (prims : Primitives p) (a : ℝ) (ε : ℝ≥0∞) :
    Prop where
  /-- The order exceeds one. -/
  one_lt : 1 < a
  /-- The forward Rényi divergence to the ideal discrete Gaussian is at most `1 + ε`. -/
  renyiDiv_le : ∀ (μ σ' : ℝ), p.sigmaMin ≤ σ' → σ' ≤ p.sigmaMax →
    renyiDiv a 𝒟[prims.samplerZ μ σ'] (discreteGaussianMeasure σ' μ) ≤ 1 + ε

/-- Exact sampler quality (`ε = 0`) is impossible once the standard-deviation range is
nonempty and positive (`evalDist_ne_discreteGaussianMeasure`). -/
theorem Primitives.not_samplerQuality_zero {p : Params} (prims : Primitives p) (a : ℝ)
    (h0 : 0 < p.sigmaMin) (hle : p.sigmaMin ≤ p.sigmaMax) : ¬ prims.SamplerQuality a 0 := by
  intro hq
  have := isProbabilityMeasure_discreteGaussianMeasure p.sigmaMin 0 h0
  have hR := hq.renyiDiv_le 0 p.sigmaMin le_rfl hle
  rw [add_zero] at hR
  have htv := etvDist_rpow_two_le_one_sub_inv_renyiDiv hq.one_lt
    (𝒟[prims.samplerZ 0 p.sigmaMin] : Measure ℤ) (discreteGaussianMeasure p.sigmaMin 0)
  rw [tsub_eq_zero_of_le (ENNReal.one_le_inv.2 hR), nonpos_iff_eq_zero,
    ENNReal.rpow_eq_zero_iff_of_pos two_pos] at htv
  exact evalDist_ne_discreteGaussianMeasure _ h0 0 (Measure.etvDist_eq_zero_iff.1 htv)

/-- **Sampler quality gives the envelope**: total variation is at most
`(1 - (1 + ε)⁻¹)^(1/2)` (`etvDist_rpow_two_le_one_sub_inv_renyiDiv`), and the ideal Gaussian
meets the envelope with no slack. -/
theorem Primitives.samplerEnvelope_of_samplerQuality {p : Params} (prims : Primitives p)
    {a : ℝ} {ε : ℝ≥0∞} (hq : prims.SamplerQuality a ε)
    (hσmin : 1 < p.sigmaMin * Real.sqrt (2 * Real.pi)) :
    prims.SamplerEnvelope ((1 - (1 + ε)⁻¹) ^ (1 / 2 : ℝ)) := by
  refine ⟨fun μ σ' hσ' hσ'' v => ?_⟩
  have h1 : 1 < σ' * Real.sqrt (2 * Real.pi) :=
    hσmin.trans_le (mul_le_mul_of_nonneg_right hσ' (Real.sqrt_nonneg _))
  have hσ0 : 0 < σ' := pos_of_mul_pos_left (one_pos.trans h1) (Real.sqrt_nonneg _)
  have := isProbabilityMeasure_discreteGaussianMeasure σ' μ hσ0
  set P : Measure ℤ := 𝒟[prims.samplerZ μ σ']
  set Q := discreteGaussianMeasure σ' μ
  have htv : P.etvDist Q ≤ (1 - (1 + ε)⁻¹) ^ (1 / 2 : ℝ) := by
    have h2 := (etvDist_rpow_two_le_one_sub_inv_renyiDiv hq.one_lt P Q).trans
      (tsub_le_tsub_left (ENNReal.inv_le_inv.2 (hq.renyiDiv_le μ σ' hσ' hσ'')) 1)
    calc P.etvDist Q = (P.etvDist Q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_mul]; norm_num
      _ ≤ _ := ENNReal.rpow_le_rpow h2 (by norm_num)
  rw [prEvent_eq_evalDist_singleton]
  calc P {v} ≤ Q {v} + P.etvDist Q :=
        (ENNReal.absDiff_le_iff.1
          (Measure.absDiff_apply_le_etvDist P Q (measurableSet_singleton v))).1
    _ ≤ _ := add_le_add (discreteGaussianMeasure_singleton_le σ' μ hσ0 h1 v) htv

/-! ## Injectivity of the merge step and of the leaf packing -/

theorem Primitives.mergeFFT_injective {k : ℕ} :
    Function.Injective fun p : RealFFTPoly k × RealFFTPoly k => Primitives.mergeFFT p.1 p.2 := by
  intro p q h
  have := congrArg Primitives.splitFFT h
  simp only [RealFFTPoly.splitFFT_mergeFFT] at this
  exact this

/-- The packed leaf polynomial with real part `a` and imaginary part `b`. -/
@[expose] noncomputable def leafPack (a b : ℤ) : RealFFTPoly 0 :=
  RealFFTPoly.pack (Vector.ofFn fun _ => (a : ℝ)) (Vector.ofFn fun _ => (b : ℝ))

theorem leafPack_re (a b : ℤ) : (leafPack a b).re ⟨0, by norm_num⟩ = a := by
  simp [leafPack]

theorem leafPack_im (a b : ℤ) : (leafPack a b).im ⟨0, by norm_num⟩ = b := by
  simp [leafPack]

theorem leafPack_inj {a b a' b' : ℤ} (h : leafPack a b = leafPack a' b') : a = a' ∧ b = b' := by
  refine ⟨?_, ?_⟩
  · have := congrArg (fun v : RealFFTPoly 0 => v.re ⟨0, by norm_num⟩) h
    rw [leafPack_re, leafPack_re] at this
    exact_mod_cast this
  · have := congrArg (fun v : RealFFTPoly 0 => v.im ⟨0, by norm_num⟩) h
    rw [leafPack_im, leafPack_im] at this
    exact_mod_cast this

/-! ## Leaf standard deviations -/

/-- Every leaf of the Falcon tree carries a standard deviation in `[σmin, σmax]`. -/
def FalconTree.LeavesIn : {κ : ℕ} → FalconTree κ → ℝ → ℝ → Prop
  | _, .leaf σ, σmin, σmax => σmin ≤ σ ∧ σ ≤ σmax
  | _, .node _ left right, σmin, σmax => left.LeavesIn σmin σmax ∧ right.LeavesIn σmin σmax

/-! ## The product bound -/

theorem Primitives.ffSampling_leaf {p : Params} (prims : Primitives p) (t₀ t₁ : RealFFTPoly 0)
    (σ : ℝ) :
    prims.ffSampling 0 (t₀, t₁) (.leaf σ) =
      (prims.samplerZ (t₀.re ⟨0, by norm_num⟩) σ >>= fun a =>
        prims.samplerZ (t₀.im ⟨0, by norm_num⟩) σ >>= fun b =>
          prims.samplerZ (t₁.re ⟨0, by norm_num⟩) σ >>= fun c =>
            prims.samplerZ (t₁.im ⟨0, by norm_num⟩) σ >>= fun d =>
              pure (leafPack a b, leafPack c d)) := rfl

theorem Primitives.ffSampling_node {p : Params} (prims : Primitives p) {k : ℕ}
    (t₀ t₁ : RealFFTPoly (k + 1)) (ℓ : RealFFTPoly (k + 1)) (left right : FalconTree k) :
    prims.ffSampling (k + 1) (t₀, t₁) (.node ℓ left right) =
      (prims.ffSampling k (Primitives.splitFFT t₁) right >>= fun s₁ =>
        prims.ffSampling k
          (Primitives.splitFFT (t₀ + Primitives.adjustTarget ℓ t₁ (Primitives.mergeFFT s₁.1 s₁.2)))
          left >>= fun s₀ =>
          pure (Primitives.mergeFFT s₀.1 s₀.2, Primitives.mergeFFT s₁.1 s₁.2)) := rfl

/-- **Min-entropy of `ffSampling` from the min-entropy of `samplerZ`.** If every call of the
one-dimensional sampler at a standard deviation in `[σmin, σmax]` has pointwise mass at most
`M`, then every output of `ffSampling` on a tree whose leaves lie in `[σmin, σmax]` has pointwise
mass at most `M ^ (4 · 2^κ)`: each leaf draws four integers, and the merges are injective. -/
theorem Primitives.ffSampling_pointMass_le {p : Params} (prims : Primitives p) {M : ℝ≥0∞}
    {σmin σmax : ℝ} (hZ : ∀ (μ σ' : ℝ), σmin ≤ σ' → σ' ≤ σmax → ∀ v : ℤ,
      Pr{let outcome ← prims.samplerZ μ σ'}[outcome = v] ≤ M) :
    ∀ (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ), tree.LeavesIn σmin σmax →
      ∀ z : FFTPair κ, Pr{let outcome ← prims.ffSampling κ t tree}[outcome = z] ≤ M ^ (4 * 2 ^ κ)
  | 0, (t₀, t₁), .leaf σ, hl, z => by
    rw [Primitives.ffSampling_leaf]
    have hM' : ∀ (μ : ℝ) (v : ℤ),
        Pr{let outcome ← prims.samplerZ μ σ}[outcome = v] ≤ M := fun μ v => hZ μ σ hl.1 hl.2 v
    have hmem : ∀ {a b c d : ℤ} {w : FFTPair 0},
        w ∈ support (pure (leafPack a b, leafPack c d) : ProbComp (FFTPair 0)) →
          w = (leafPack a b, leafPack c d) := by
      intro a b c d w hw
      simpa using hw
    have h4 : ∀ a b c : ℤ,
        Pr{let outcome ← (prims.samplerZ (t₁.im ⟨0, by norm_num⟩) σ >>= fun d =>
          pure (leafPack a b, leafPack c d) : ProbComp (FFTPair 0))}[outcome = z] ≤ M * 1 := by
      intro a b c
      refine pointMass_bind_le_mul _ _ z (hM' _) (fun _ => measure_le_one _ _) ?_
      intro d₁ d₂ h₁ h₂
      rw [ne_eq, pointMass_eq_zero_iff, not_not] at h₁ h₂
      have e := (hmem h₁).symm.trans (hmem h₂)
      exact (leafPack_inj (Prod.mk.inj e).2).2
    have h3 : ∀ a b : ℤ,
        Pr{let outcome ← (prims.samplerZ (t₁.re ⟨0, by norm_num⟩) σ >>= fun c =>
          prims.samplerZ (t₁.im ⟨0, by norm_num⟩) σ >>= fun d =>
            pure (leafPack a b, leafPack c d) : ProbComp (FFTPair 0))}[outcome = z] ≤
          M * (M * 1) := by
      intro a b
      refine pointMass_bind_le_mul _ _ z (hM' _) (fun c => h4 a b c) ?_
      intro c₁ c₂ h₁ h₂
      rw [ne_eq, pointMass_eq_zero_iff, not_not, mem_support_bind_iff] at h₁ h₂
      obtain ⟨d₁, -, h₁⟩ := h₁
      obtain ⟨d₂, -, h₂⟩ := h₂
      have e := (hmem h₁).symm.trans (hmem h₂)
      exact (leafPack_inj (Prod.mk.inj e).2).1
    have h2 : ∀ a : ℤ,
        Pr{let outcome ← (prims.samplerZ (t₀.im ⟨0, by norm_num⟩) σ >>= fun b =>
          prims.samplerZ (t₁.re ⟨0, by norm_num⟩) σ >>= fun c =>
            prims.samplerZ (t₁.im ⟨0, by norm_num⟩) σ >>= fun d =>
              pure (leafPack a b, leafPack c d) : ProbComp (FFTPair 0))}[outcome = z] ≤
          M * (M * (M * 1)) := by
      intro a
      refine pointMass_bind_le_mul _ _ z (hM' _) (fun b => h3 a b) ?_
      intro b₁ b₂ h₁ h₂
      rw [ne_eq, pointMass_eq_zero_iff, not_not, mem_support_bind_iff] at h₁ h₂
      obtain ⟨c₁, -, h₁⟩ := h₁
      obtain ⟨c₂, -, h₂⟩ := h₂
      rw [mem_support_bind_iff] at h₁ h₂
      obtain ⟨d₁, -, h₁⟩ := h₁
      obtain ⟨d₂, -, h₂⟩ := h₂
      have e := (hmem h₁).symm.trans (hmem h₂)
      exact (leafPack_inj (Prod.mk.inj e).1).2
    have h1 : Pr{let outcome ← (prims.samplerZ (t₀.re ⟨0, by norm_num⟩) σ >>= fun a =>
        prims.samplerZ (t₀.im ⟨0, by norm_num⟩) σ >>= fun b =>
          prims.samplerZ (t₁.re ⟨0, by norm_num⟩) σ >>= fun c =>
            prims.samplerZ (t₁.im ⟨0, by norm_num⟩) σ >>= fun d =>
              pure (leafPack a b, leafPack c d) : ProbComp (FFTPair 0))}[outcome = z] ≤
          M * (M * (M * (M * 1))) := by
      refine pointMass_bind_le_mul _ _ z (hM' _) (fun a => h2 a) ?_
      intro a₁ a₂ h₁ h₂
      rw [ne_eq, pointMass_eq_zero_iff, not_not, mem_support_bind_iff] at h₁ h₂
      obtain ⟨b₁, -, h₁⟩ := h₁
      obtain ⟨b₂, -, h₂⟩ := h₂
      rw [mem_support_bind_iff] at h₁ h₂
      obtain ⟨c₁, -, h₁⟩ := h₁
      obtain ⟨c₂, -, h₂⟩ := h₂
      rw [mem_support_bind_iff] at h₁ h₂
      obtain ⟨d₁, -, h₁⟩ := h₁
      obtain ⟨d₂, -, h₂⟩ := h₂
      have e := (hmem h₁).symm.trans (hmem h₂)
      exact (leafPack_inj (Prod.mk.inj e).1).1
    calc Pr{let outcome ← _}[outcome = z] ≤ M * (M * (M * (M * 1))) := h1
      _ = M ^ (4 * 2 ^ 0) := by ring
  | k + 1, (t₀, t₁), .node ℓ left right, hl, z => by
    rw [Primitives.ffSampling_node]
    obtain ⟨hlL, hlR⟩ := hl
    have ihR := fun t => Primitives.ffSampling_pointMass_le prims hZ k t right hlR
    have ihL := fun t => Primitives.ffSampling_pointMass_le prims hZ k t left hlL
    have hinner : ∀ s₁ : FFTPair k,
        Pr{let outcome ← (prims.ffSampling k
          (Primitives.splitFFT (t₀ + Primitives.adjustTarget ℓ t₁ (Primitives.mergeFFT s₁.1 s₁.2)))
          left >>= fun s₀ =>
          pure (Primitives.mergeFFT s₀.1 s₀.2, Primitives.mergeFFT s₁.1 s₁.2) :
            ProbComp (FFTPair (k + 1)))}[outcome = z] ≤ M ^ (4 * 2 ^ k) * 1 := by
      intro s₁
      refine pointMass_bind_le_mul _ _ z (ihL _) (fun _ => measure_le_one _ _) ?_
      intro s₀ s₀' h₁ h₂
      rw [ne_eq, pointMass_eq_zero_iff, not_not, support_pure, Set.mem_singleton_iff] at h₁ h₂
      have e := Prod.mk.inj (h₁.symm.trans h₂)
      exact Primitives.mergeFFT_injective e.1
    refine le_trans (pointMass_bind_le_mul _ _ z (ihR _) hinner ?_) ?_
    · intro s₁ s₁' h₁ h₂
      rw [ne_eq, pointMass_eq_zero_iff, not_not, mem_support_bind_iff] at h₁ h₂
      obtain ⟨s₀, -, h₁⟩ := h₁
      obtain ⟨s₀', -, h₂⟩ := h₂
      rw [support_pure, Set.mem_singleton_iff] at h₁ h₂
      have e := Prod.mk.inj (h₁.symm.trans h₂)
      exact Primitives.mergeFFT_injective e.2
    · rw [mul_one, ← pow_add, show 4 * 2 ^ k + 4 * 2 ^ k = 4 * 2 ^ (k + 1) by ring]

/-! ## The product bound under the sampler envelope -/

/-- Under `SamplerEnvelope δ`, each leaf draw has mass at most `1 / (σ_min √(2π) - 1) + δ`. -/
theorem Primitives.samplerZ_pointMass_le_of_samplerEnvelope {p : Params} (prims : Primitives p)
    {δ : ℝ≥0∞} (hσmin : 1 < p.sigmaMin * Real.sqrt (2 * Real.pi)) (hZ : prims.SamplerEnvelope δ)
    (μ σ' : ℝ) (hσ' : p.sigmaMin ≤ σ') (hσ'' : σ' ≤ p.sigmaMax) (v : ℤ) :
    Pr{let outcome ← prims.samplerZ μ σ'}[outcome = v] ≤
      ENNReal.ofReal (1 / (p.sigmaMin * Real.sqrt (2 * Real.pi) - 1)) + δ := by
  refine (hZ.pointMass_le μ σ' hσ' hσ'' v).trans ?_
  gcongr ?_ + δ
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hprod : p.sigmaMin * Real.sqrt (2 * Real.pi) ≤ σ' * Real.sqrt (2 * Real.pi) :=
    mul_le_mul_of_nonneg_right hσ' hsqrt.le
  apply ENNReal.ofReal_le_ofReal
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- The product bound under the sampler envelope. -/
theorem Primitives.ffSampling_pointMass_le_of_samplerEnvelope {p : Params} (prims : Primitives p)
    {δ : ℝ≥0∞} (hσmin : 1 < p.sigmaMin * Real.sqrt (2 * Real.pi)) (hZ : prims.SamplerEnvelope δ)
    (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ) (hl : tree.LeavesIn p.sigmaMin p.sigmaMax)
    (z : FFTPair κ) :
    Pr{let outcome ← prims.ffSampling κ t tree}[outcome = z] ≤
      (ENNReal.ofReal (1 / (p.sigmaMin * Real.sqrt (2 * Real.pi) - 1)) + δ) ^ (4 * 2 ^ κ) :=
  Primitives.ffSampling_pointMass_le prims
    (prims.samplerZ_pointMass_le_of_samplerEnvelope hσmin hZ) κ t tree hl z

/-- Once `σ_min √(2π) ≥ 3`, each leaf draw has mass at most `1/2 + δ`; with `δ = 0` the sampler
has at least `4 · 2^κ` bits of min-entropy. -/
theorem Primitives.ffSampling_pointMass_le_half_add_pow {p : Params} (prims : Primitives p)
    {δ : ℝ≥0∞} (h3 : 3 ≤ p.sigmaMin * Real.sqrt (2 * Real.pi)) (hZ : prims.SamplerEnvelope δ)
    (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ) (hl : tree.LeavesIn p.sigmaMin p.sigmaMax)
    (z : FFTPair κ) :
    Pr{let outcome ← prims.ffSampling κ t tree}[outcome = z] ≤
      (ENNReal.ofReal (1 / 2) + δ) ^ (4 * 2 ^ κ) := by
  refine le_trans
    (prims.ffSampling_pointMass_le_of_samplerEnvelope (by linarith) hZ κ t tree hl z) ?_
  have hreal : 1 / (p.sigmaMin * Real.sqrt (2 * Real.pi) - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (a := 2) (b := p.sigmaMin * Real.sqrt (2 * Real.pi) - 1)
      (by norm_num) (by linarith)
  gcongr

/-- The Falcon-512 minimum standard deviation clears the `1/2`-per-draw threshold. -/
theorem falcon512_sigmaMin_sqrt_two_pi_ge_three :
    3 ≤ falcon512.sigmaMin * Real.sqrt (2 * Real.pi) := by
  have hpi := Real.pi_gt_three
  have h6 : (2.44 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hs : falcon512.sigmaMin = (12778336969128337 : ℝ) / 10000000000000000 := rfl
  rw [hs]
  nlinarith [h6]

/-- The Falcon-1024 minimum standard deviation clears the `1/2`-per-draw threshold. -/
theorem falcon1024_sigmaMin_sqrt_two_pi_ge_three :
    3 ≤ falcon1024.sigmaMin * Real.sqrt (2 * Real.pi) := by
  have hpi := Real.pi_gt_three
  have h6 : (2.44 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hs : falcon1024.sigmaMin = (1298280334344292 : ℝ) / 1000000000000000 := rfl
  rw [hs]
  nlinarith [h6]

/-- The Falcon-512 standard-deviation range `[σ_min, σ_max]` is nonempty. -/
theorem falcon512_sigmaMin_le_sigmaMax : falcon512.sigmaMin ≤ falcon512.sigmaMax := by
  rw [show falcon512.sigmaMin = (12778336969128337 : ℝ) / 10000000000000000 from rfl,
    show falcon512.sigmaMax = (18205 : ℝ) / 10000 from rfl]
  norm_num

/-- The Falcon-1024 standard-deviation range `[σ_min, σ_max]` is nonempty. -/
theorem falcon1024_sigmaMin_le_sigmaMax : falcon1024.sigmaMin ≤ falcon1024.sigmaMax := by
  rw [show falcon1024.sigmaMin = (1298280334344292 : ℝ) / 1000000000000000 from rfl,
    show falcon1024.sigmaMax = (18205 : ℝ) / 10000 from rfl]
  norm_num

end Falcon

end
