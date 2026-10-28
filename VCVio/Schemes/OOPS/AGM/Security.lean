/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.OOPS.AGM.Game
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Extraction

/-! # OOPS algebraic unforgeability in the random-oracle model

The target-topic degree rule is an admissibility predicate on the existing signature game.
The verification-gap split uses the two named lazy reductions. Only a hidden affine-slope
collision contributes a field-sized loss; no degree-dependent loss is needed.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace OOPS

private abbrev Trace (F T G₁ G₂ : Type) (degree : ℕ) :=
  Explained F (F × T) (SourceGroup G₁ G₂) × List ((T × Fin (degree + 1)) ⊕ (F × T))

/-- Every algebraic OOPS adversary obeying the target-topic degree rule has EUF-CMA advantage
at most the successes of the two named (1,1)-DLog reductions plus one over the field size.
Topics and total signing-query counts are unrestricted. -/
theorem unforgeableAdvantage_le_of_algebraic {F T G₁ G₂ Gₜ : Type}
    [Field F] [Fintype F] [SampleableType F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq T]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) (hA : A.Admissible)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0) :
    SignatureAlg.unforgeableAdvantage
        (ProbCompRuntime.rom ((T × Fin (degree + 1)) →ₒ G₁)) A.toUnforgeableAdversary ≤
      Pr{let b ← DLog11.experiment g₁ g₂ (goodReduction A)}[b = true] +
      Pr{let b ← DLog11.experiment g₁ g₂ (badReduction A)}[b = true] +
      1 / Fintype.card F := by
  classical
  obtain ⟨S₁, hS₁⟩ := exists_weightedInterfaceCovered (terms degree) (fun out => out.value.data)
    (fun κ : F => AGM.rawMain A (κ • g₂))
  obtain ⟨S₂, hS₂⟩ := exists_queriesCovered
    (SignatureAlg.unforgeableExperiment A.toUnforgeableAdversary)
  let S := S₁ ∪ S₂
  have hS : ∀ κ : F, WeightedInterfaceCovered S (terms degree) (fun out => out.value.data)
      (AGM.rawMain A (κ • g₂)) := fun κ => (hS₁ κ).mono Finset.subset_union_left
  have hExp : QueriesCovered S (SignatureAlg.unforgeableExperiment A.toUnforgeableAdversary) :=
    hS₂.mono (fun q hq => by
      cases q with
      | inl n => trivial
      | inr i => exact Finset.mem_union_right _ hq)
  let pub := fun ρ : S → F => do
    let κ ← ($ᵗ F : ProbComp F)
    let z ← AGM.fixedView A (extendTable S 0 ρ) κ
    return (κ, z)
  let game := do
    let ρ ← ($ᵗ (S → F) : ProbComp _)
    let z ← pub ρ
    return (ρ, z)
  let repr := fun (ρ : S → F) (z : Trace F T G₁ G₂ degree) =>
    AGM.goodRepresentation degree ((z.1.coefficients false).headD []) z.2 (extendTable S 0 ρ)
  let gap := fun (z : Trace F T G₁ G₂ degree) (i : S) =>
    AGM.verificationGap degree ((z.1.coefficients false).headD []) z.2 z.1.value.data i.val
  let valid := fun z : F × Trace F T G₁ G₂ degree =>
    z.2.1.value.data ∉ weightedSignedMessages z.2.2 ∧
      admissible degree z.2.1.value.data (weightedSignedMessages z.2.2)
  let win := fun z : (S → F) × F × Trace F T G₁ G₂ degree =>
    z.2.2.1.value.data ∉ weightedSignedMessages z.2.2.2 ∧
      e (AGM.forgery z.2.2.1).2 g₂ =
        e (AGM.scalarHash degree (extendTable S 0 z.1) z.2.2.1.value.data • g₁) (z.2.1 • g₂)
  let good := fun z : (S → F) × F × Trace F T G₁ G₂ degree =>
    (repr z.1 z.2.2).1 /
      (AGM.scalarHash degree (extendTable S 0 z.1) z.2.2.1.value.data -
        (repr z.1 z.2.2).2) = z.2.1
  let bad := fun z : (S → F) × F × Trace F T G₁ G₂ degree =>
    valid z.2 ∧ ∑ i, gap z.2.2 i * z.1 i = 0
  have horder : (do
      let κ ← ($ᵗ F : ProbComp F); let ρ ← $ᵗ (S → F)
      let z ← AGM.fixedView A (extendTable S 0 ρ) κ
      return (ρ, κ, z)) =ᵈ game := by
    simpa only [game, pub, bind_assoc, pure_bind] using
      OracleComp.EvalDistEq.bind_bind_swap ($ᵗ F) ($ᵗ (S → F))
        (fun κ ρ => do let z ← AGM.fixedView A (extendTable S 0 ρ) κ; return (ρ, κ, z))
  have hgame : SignatureAlg.unforgeableAdvantage
      (ProbCompRuntime.rom ((T × Fin (degree + 1)) →ₒ G₁)) A.toUnforgeableAdversary =
      Pr{let z ← game}[win z] := by
    rw [AGM.unforgeableAdvantage_eq_scalarTable A hg₁ S hExp]
    simp only [game, pub, win, prEvent_norm]
  have hgood : Pr{let b ← DLog11.experiment g₁ g₂ (goodReduction A)}[b = true] =
      Pr{let z ← game}[good z] := by
    rw [← horder.prEvent_eq good]
    simp only [DLog11.experiment, prEvent_norm, decide_eq_true_eq]
    let : MeasurableSpace F := ⊤
    rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
    apply MeasureTheory.lintegral_congr
    intro κ
    simpa only [good, repr, prEvent_norm] using
      (AGM.goodReduction_table A κ S (hS κ)).prEvent_eq (· = κ)
  have hsplit : Pr{let z ← game}[win z] ≤
      Pr{let z ← game}[good z] + Pr{let z ← game}[bad z] := by
    apply (prEvent_mono_of_support game win (fun z => good z ∨ bad z) ?_).trans
      (prEvent_or_le game good bad)
    intro z hz hw
    obtain ⟨ρ, _, v, hv, rfl⟩ := by
      simpa only [game, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] using hz
    obtain ⟨κ, _, t, ht, rfl⟩ := by
      simpa only [pub, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] using hv
    change _ ∧ _ at hw
    have hs := AGM.fixedRun_good_sound A κ (extendTable S 0 ρ) t ht
    change (AGM.forgery t.1).2 = ((repr ρ t).1 + (repr ρ t).2 * κ) • g₁ at hs
    have heq : (repr ρ t).1 + (repr ρ t).2 * κ =
        AGM.scalarHash degree (extendTable S 0 ρ) t.1.value.data * κ := by
      apply smul_left_injective F he
      simpa only [hs, LinearMap.map_smul, LinearMap.smul_apply, smul_smul] using hw.2
    by_cases hgap : AGM.scalarHash degree (extendTable S 0 ρ) t.1.value.data -
        (repr ρ t).2 = 0
    · apply Or.inr
      refine ⟨⟨hw.1, AGM.fixedView_admissible A hA κ _ t ht hw.1 hw.2⟩, ?_⟩
      exact (AGM.scalarHash_sub_goodRepresentation_snd degree S ρ
        ((t.1.coefficients false).headD []) t.2 t.1.value.data).symm.trans hgap
    · apply Or.inl
      change _ / _ = κ
      apply (div_eq_iff hgap).2
      linear_combination heq
  obtain ⟨z₀, hz₀⟩ := support_nonempty (AGM.fixedView A (fun _ => 0) (0 : F))
  have hm₀ := (weightedFixedRun_mem_cover S (terms degree) (fun out => out.value.data)
    _ _ _ (hS 0) z₀ hz₀).1
  have hbase : (z₀.1.value.data.2, (0 : Fin (degree + 1))) ∈ S := by
    apply hm₀ ((z₀.1.value.data.2, 0), z₀.1.value.data.1 ^ (0 : ℕ))
    simp only [terms, List.mem_ofFn]
    exact ⟨0, rfl⟩
  let j := fun z : F × Trace F T G₁ G₂ degree =>
    if h : ∃ i : S, gap z.2 i ≠ 0 then Classical.choose h else
      (⟨(z₀.1.value.data.2, 0), hbase⟩ : S)
  have hL : ∀ ρ z, z ∈ support (pub ρ) → valid z → gap z.2 (j z) ≠ 0 := by
    intro ρ z hz hvalid
    obtain ⟨κ, _, t, ht, rfl⟩ := by
      simpa only [pub, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] using hz
    obtain ⟨i, hi⟩ := AGM.exists_signingFunctional_gap_ne_zero degree
      ((t.1.coefficients false).headD []) t.2 t.1.value.data hvalid.2 hvalid.1
    have hm := (weightedFixedRun_mem_cover S (terms degree) (fun out => out.value.data)
      _ _ _ (hS κ) t ht).1
    have hmem : (t.1.value.data.2, i) ∈ S := by
      apply hm ((t.1.value.data.2, i), t.1.value.data.1 ^ i.val)
      simp only [terms, List.mem_ofFn]
      exact ⟨i, rfl⟩
    have hex : ∃ i : S, gap t i ≠ 0 := ⟨⟨_, hmem⟩, hi⟩
    simpa only [j, dite_eq_left hex] using Classical.choose_spec hex
  have hb := prEvent_zero_gap_le_uniform_affine_extract_add pub
    (fun z => gap z.2) (fun _ => (0 : F)) valid j hL
  have hbad : Pr{let b ← DLog11.experiment g₁ g₂ (badReduction A)}[b = true] =
      Pr{let α ← ($ᵗ F : ProbComp F)
         let a ← $ᵗ (S → F); let b ← $ᵗ (S → F)
         let z ← pub (fun i => a i * α + b i)}[
        (-∑ i, gap z.2 i * b i) / (∑ i, gap z.2 i * a i) = α] := by
    simp only [DLog11.experiment, prEvent_norm, decide_eq_true_eq]
    let : MeasurableSpace F := ⊤
    rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
    apply MeasureTheory.lintegral_congr
    intro α
    rw [(AGM.badReduction_table A α S hS).prEvent_eq (· = α)]
    have hswap := OracleComp.EvalDistEq.bind_bind_swap ($ᵗ F)
      (do let a ← ($ᵗ (S → F) : ProbComp _); let b ← $ᵗ (S → F); return (a, b))
      (fun κ ab => do
        let z ← AGM.fixedView A (extendTable S 0 (fun i => ab.1 i * α + ab.2 i)) κ
        return (-∑ i, gap z i * ab.2 i) / (∑ i, gap z i * ab.1 i))
    simpa only [pub, gap, prEvent_norm] using hswap.prEvent_eq (· = α)
  have hb' : Pr{let z ← game}[bad z] ≤
      Pr{let b ← DLog11.experiment g₁ g₂ (badReduction A)}[b = true] +
        1 / Fintype.card F := by
    rw [hbad]
    simpa only [game, bad, prEvent_norm, zero_sub] using hb
  rw [hgame, hgood]
  exact hsplit.trans (by simpa only [add_assoc] using add_le_add (le_refl _) hb')

end OOPS
