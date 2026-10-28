/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Collision
import Mathlib.Tactic.Ring

/-! # Independent slopes under affine masking

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). Adding a uniform mask to a scalar multiple of
a slope table hides the slope perfectly, including from an adaptive computation that observes
the entire masked table.
-/

public section

open OracleComp

namespace GroupModel.LinearFunctional

/-- An independent additive mask makes an affine table uniform for any fixed slope and secret. -/
theorem affine_uniform_evalDistEq {F ι : Type} [Ring F] [SampleableType F]
    [Fintype ι] [DecidableEq ι] (α : F) (a : ι → F) :
    (fun b : ι → F => fun i => a i * α + b i) <$> ($ᵗ (ι → F)) =ᵈ
      ($ᵗ (ι → F) : ProbComp _) := by
  apply SampleableType.map_uniformSample_evalDistEq_of_bijective
  constructor
  · intro b c h
    funext i
    exact add_left_cancel (congrFun h i)
  · intro ρ
    exact ⟨fun i => ρ i - a i * α, by funext i; simp⟩

/-- An adaptive view of an affine-masked table leaves its slope table independently uniform.
The output retains the view, public table, and hidden slope, in that order. -/
theorem masked_view_evalDistEq {F ι γ : Type} [Ring F] [SampleableType F]
    [Fintype ι] [DecidableEq ι] (α : F) (view : (ι → F) → ProbComp γ) :
    (do
      let a ← $ᵗ (ι → F)
      let b ← $ᵗ (ι → F)
      let ρ := fun i => a i * α + b i
      let z ← view ρ
      pure (z, ρ, a)) =ᵈ
    (do
      let ρ ← $ᵗ (ι → F)
      let z ← view ρ
      let a ← $ᵗ (ι → F)
      pure (z, ρ, a)) := by
  trans (do
    let a ← $ᵗ (ι → F)
    let ρ ← $ᵗ (ι → F)
    let z ← view ρ
    pure (z, ρ, a))
  · refine _root_.EvalDistEq.bind_right _ fun a => ?_
    simpa only [bind_map_left] using (affine_uniform_evalDistEq α a).bind_left
      (fun ρ => do let z ← view ρ; pure (z, ρ, a))
  · let seen : ProbComp (γ × (ι → F)) := do
      let ρ ← $ᵗ (ι → F)
      let z ← view ρ
      pure (z, ρ)
    simpa only [seen, bind_assoc, pure_bind] using
      OracleComp.EvalDistEq.bind_bind_swap ($ᵗ (ι → F)) seen
        (fun a z => pure (z.1, z.2, a))

/-- A zero affine equation with nonzero slope reveals the masked scalar. -/
theorem affine_extract_eq {F ι : Type*} [Field F] [Fintype ι]
    (L a b : ι → F) (α c : F)
    (hzero : ∑ i, L i * (a i * α + b i) = c)
    (hslope : ∑ i, L i * a i ≠ 0) :
    (c - ∑ i, L i * b i) / (∑ i, L i * a i) = α := by
  apply (div_eq_iff hslope).2
  have he : ∑ i, L i * (a i * α + b i) =
      (∑ i, L i * a i) * α + ∑ i, L i * b i := by
    simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, Finset.sum_mul]
  rw [he] at hzero
  rw [← hzero]
  ring

/-- A zero verification gap in a public view yields an affine guess, except for a hidden
uniform slope collision. The entire public view is drawn before the slope table. -/
private theorem prEvent_zero_gap_le_guess_add {F ι γ : Type} [Field F] [Fintype F]
    [SampleableType F] [Fintype ι] [DecidableEq ι]
    (oa : ProbComp γ) (L : γ → ι → F) (table : γ → ι → F) (c : γ → F)
    (valid : γ → Prop) (j : γ → ι) (α : F)
    (hL : ∀ z ∈ support oa, valid z → L z (j z) ≠ 0) :
    Pr{let z ← oa}[valid z ∧ ∑ i, L z i * table z i = c z] ≤
      Pr{let z ← oa; let a ← $ᵗ (ι → F)}[
        (c z - ∑ i, L z i * table z i + (∑ i, L z i * a i) * α) /
          (∑ i, L z i * a i) = α] + 1 / Fintype.card F := by
  let game : ProbComp (γ × (ι → F)) := do
    let z ← oa
    let a ← $ᵗ (ι → F)
    pure (z, a)
  let bad := fun z : γ => valid z ∧ ∑ i, L z i * table z i = c z
  let guess := fun z : γ × (ι → F) =>
    (c z.1 - ∑ i, L z.1 i * table z.1 i + (∑ i, L z.1 i * z.2 i) * α) /
      (∑ i, L z.1 i * z.2 i)
  have hproj : Prod.fst <$> game =ᵈ oa := by
    simp only [game, map_bind, map_pure]
    conv_rhs => rw [← bind_pure oa]
    exact _root_.EvalDistEq.bind_right oa fun z => by
      simpa only [bind_pure_comp] using OracleComp.EvalDistEq.map_const ($ᵗ (ι → F)) z
  have heq := hproj.prEvent_eq bad
  simp only [prEvent_map] at heq
  have hsplit : Pr{let z ← game}[bad z.1] ≤
      Pr{let z ← game}[guess z = α] +
        Pr{let z ← game}[bad z.1 ∧ ∑ i, L z.1 i * z.2 i = 0] := by
    refine (prEvent_mono game _ _ ?_).trans (prEvent_or_le game _ _)
    intro z hz
    by_cases hs : ∑ i, L z.1 i * z.2 i = 0
    · exact Or.inr ⟨hz, hs⟩
    · apply Or.inl
      simp only [guess, hz.2, sub_self, zero_add, mul_div_cancel_left₀ _ hs]
  have hc : Pr{let z ← game}[bad z.1 ∧ ∑ i, L z.1 i * z.2 i = 0] ≤
      1 / Fintype.card F := by
    have hb := prEvent_bind_le_of_forall_le_of_support oa
      (fun z => (fun a : ι → F => bad z ∧ ∑ i, L z i * a i = 0) <$> ($ᵗ (ι → F))) id
      (ε := 1 / Fintype.card F) (fun z hz => by
        by_cases hv : bad z
        · simpa only [prEvent_norm, id_eq, hv, true_and] using
            prEvent_sum_mul_uniform_le (L z) (j z) (hL z hz hv.1) 0
        · simp only [prEvent_norm, id_eq, hv, false_and, prEvent_false]
          exact zero_le)
    simpa only [game, prEvent_norm, id_eq] using hb
  rw [heq] at hsplit
  have hb := hsplit.trans (add_le_add (le_refl _) hc)
  simpa only [game, bad, guess, prEvent_norm] using hb

/-- A zero gap for an adaptive public view is bounded by extraction from independently masked
bases and one field-sized collision. The extractor uses only its sampled masks and the view. -/
theorem prEvent_zero_gap_le_affine_extract_add {F ι γ : Type} [Field F] [Fintype F]
    [SampleableType F] [Fintype ι] [DecidableEq ι]
    (view : (ι → F) → ProbComp γ) (L : γ → ι → F) (c : γ → F)
    (valid : γ → Prop) (j : γ → ι) (α : F)
    (hL : ∀ ρ z, z ∈ support (view ρ) → valid z → L z (j z) ≠ 0) :
    Pr{let ρ ← $ᵗ (ι → F); let z ← view ρ}[
      valid z ∧ ∑ i, L z i * ρ i = c z] ≤
    Pr{let a ← $ᵗ (ι → F); let b ← $ᵗ (ι → F)
       let z ← view (fun i => a i * α + b i)}[
      (c z - ∑ i, L z i * b i) / (∑ i, L z i * a i) = α] + 1 / Fintype.card F := by
  let seen : ProbComp (γ × (ι → F)) := do
    let ρ ← $ᵗ (ι → F)
    let z ← view ρ
    pure (z, ρ)
  have hb := prEvent_zero_gap_le_guess_add seen (fun z => L z.1) Prod.snd
    (fun z => c z.1) (fun z => valid z.1) (fun z => j z.1) α (by
      intro z hz hv
      simp only [seen, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨ρ, _, y, hy, rfl⟩ := hz
      exact hL ρ y hy hv)
  have hnum (L a b : ι → F) (c : F) :
      c - ∑ i, L i * (a i * α + b i) + (∑ i, L i * a i) * α =
        c - ∑ i, L i * b i := by
    simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  have hd := (masked_view_evalDistEq α view).prEvent_eq (fun z =>
    (c z.1 - ∑ i, L z.1 i * z.2.1 i + (∑ i, L z.1 i * z.2.2 i) * α) /
      (∑ i, L z.1 i * z.2.2 i) = α)
  simp only [prEvent_norm, hnum] at hd
  simpa only [seen, prEvent_norm, ← hd] using hb

end GroupModel.LinearFunctional
