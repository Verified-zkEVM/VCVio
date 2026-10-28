/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.SynchronizedPS.Game
public import VCVio.Schemes.SynchronizedPS.Table
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Extraction

/-! # Algebraic security of synchronized PS in the certified-key model

A successful synchronized aggregate yields a linear equation in two secret-key scalars.
The first two reductions cover nonzero denominators. The hash reduction covers the common
zero-denominator event through affine programming, with one field-sized collision loss.
Periods need only decidable equality; finite covers occur exclusively inside the proof.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace SynchronizedPS

private abbrev Trace (F T G₁ G₂ : Type) :=
  Explained F ((T × F) × List ((F × F) × F)) (SourceGroup G₁ G₂) × List (T ⊕ (T × F))

/-- Certified-key synchronized PS unforgeability against an algebraic adversary is bounded by
three named (1,1)-DLog reductions and one over the field size. The once-per-period signing rule
is checked by the experiment's winning event, with no admissibility premise on the adversary. -/
theorem unforgeableAdvantage_le_of_algebraic {F T G₁ G₂ Gₜ : Type}
    [Field F] [Fintype F] [SampleableType F] [DecidableEq F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0) :
    AggregateSignatureAlg.Synchronized.unforgeableAdvantage
        (ProbCompRuntime.rom (T →ₒ G₁)) (publicKeyOf g₂) A.toUnforgeableAdversary ≤
      Pr{let b ← DLog11.experiment g₁ g₂ (xReduction A)}[b = true] +
      Pr{let b ← DLog11.experiment g₁ g₂ (yReduction A)}[b = true] +
      Pr{let b ← DLog11.experiment g₁ g₂ (hashReduction A)}[b = true] +
      1 / Fintype.card F := by
  classical
  obtain ⟨S₁, hS₁⟩ := exists_weightedInterfaceCovered terms (fun out => out.value.data.1)
    (fun k : F × F => AGM.rawMain A (publicKeyOf g₂ k))
  obtain ⟨S₂, hS₂⟩ := exists_queriesCovered
    (AggregateSignatureAlg.Synchronized.unforgeableExperiment
      (publicKeyOf g₂) A.toUnforgeableAdversary)
  let S := S₁ ∪ S₂
  have hS : ∀ x y : F, WeightedInterfaceCovered S terms (fun out => out.value.data.1)
      (AGM.rawMain A (publicKeyOf g₂ (x, y))) := fun x y =>
    (hS₁ (x, y)).mono Finset.subset_union_left
  have hExp : QueriesCovered S (AggregateSignatureAlg.Synchronized.unforgeableExperiment
      (publicKeyOf g₂) A.toUnforgeableAdversary) := hS₂.mono (fun q hq => by
        cases q with
        | inl n => trivial
        | inr t => exact Finset.mem_union_right _ hq)
  let pub := fun ρ : S → F => do
    let x ← ($ᵗ F : ProbComp F)
    let y ← $ᵗ F
    let z ← AGM.fixedView A (extendTable S 0 ρ) x y
    return (x, y, z)
  let game := do
    let ρ ← ($ᵗ (S → F) : ProbComp _)
    let z ← pub ρ
    return (ρ, z)
  let coeff := fun z : Trace F T G₁ G₂ => (z.1.coefficients false).headD []
  let dx := fun (ρ : S → F) (z : Trace F T G₁ G₂) =>
    AGM.xDenominator (coeff z) z.2 z.1.value.data.1 (extendTable S 0 ρ)
  let dy := fun (ρ : S → F) (z : Trace F T G₁ G₂) =>
    AGM.yDenominator (coeff z) z.2 z.1.value.data.1 (extendTable S 0 ρ)
  let k := fun (ρ : S → F) (z : Trace F T G₁ G₂) =>
    AGM.knownTerm (coeff z) z.2 z.1.value.data.1 z.1.value.data.2 (extendTable S 0 ρ)
  let gap := fun (z : Trace F T G₁ G₂) (i : S) =>
    AGM.verificationGap (AGM.selectedWeight (coeff z) z.2 z.1.value.data.1)
      (coeff z) z.2 z.1.value.data.1 i.val
  let valid := fun z : F × F × Trace F T G₁ G₂ =>
    z.2.2.1.value.data.1 ∉ weightedSignedMessages z.2.2.2 ∧
      AggregateSignatureAlg.Synchronized.OnePerPeriod (weightedSignedMessages z.2.2.2)
  let win := fun z : (S → F) × F × F × Trace F T G₁ G₂ =>
    valid z.2 ∧ e (extendTable S 0 z.1 z.2.2.2.1.value.data.1.1 • g₁)
      ((z.2.1 + z.2.2.1 * z.2.2.2.1.value.data.1.2 + offset z.2.2.2.1.value.data.2) • g₂) =
        e (AGM.forgery z.2.2.2.1).2.2 g₂
  let gx := fun z : (S → F) × F × F × Trace F T G₁ G₂ =>
    (k z.1 z.2.2.2 - z.2.2.1 * dy z.1 z.2.2.2) / dx z.1 z.2.2.2 = z.2.1
  let gy := fun z : (S → F) × F × F × Trace F T G₁ G₂ =>
    (k z.1 z.2.2.2 - z.2.1 * dx z.1 z.2.2.2) / dy z.1 z.2.2.2 = z.2.2.1
  let bad := fun z : (S → F) × F × F × Trace F T G₁ G₂ =>
    valid z.2 ∧ ∑ i, gap z.2.2.2 i * z.1 i = 0
  have hgame : AggregateSignatureAlg.Synchronized.unforgeableAdvantage
      (ProbCompRuntime.rom (T →ₒ G₁)) (publicKeyOf g₂) A.toUnforgeableAdversary =
      Pr{let z ← game}[win z] := by
    rw [AGM.unforgeableAdvantage_eq_scalarTable A hg₁ S hExp]
    simp only [game, pub, win, valid, prEvent_norm]
  have horder : (do
      let x ← ($ᵗ F : ProbComp F); let y ← $ᵗ F; let ρ ← $ᵗ (S → F)
      let z ← AGM.fixedView A (extendTable S 0 ρ) x y
      return (ρ, x, y, z)) =ᵈ game := by
    simpa only [game, pub, bind_assoc, pure_bind] using
      OracleComp.EvalDistEq.bind_bind_swap
        (do let x ← ($ᵗ F : ProbComp F); let y ← $ᵗ F; return (x, y)) ($ᵗ (S → F))
        (fun xy ρ => do
          let z ← AGM.fixedView A (extendTable S 0 ρ) xy.1 xy.2
          return (ρ, xy.1, xy.2, z))
  have hx : Pr{let b ← DLog11.experiment g₁ g₂ (xReduction A)}[b = true] =
      Pr{let z ← game}[gx z] := by
    rw [← horder.prEvent_eq gx]
    simp only [DLog11.experiment, prEvent_norm, decide_eq_true_eq]
    let : MeasurableSpace F := ⊤
    rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
    apply MeasureTheory.lintegral_congr
    intro x
    simpa only [gx, coeff, k, dx, dy, prEvent_norm] using
      (AGM.xReduction_table A x S (hS x)).prEvent_eq (· = x)
  have hy : Pr{let b ← DLog11.experiment g₁ g₂ (yReduction A)}[b = true] =
      Pr{let z ← game}[gy z] := by
    rw [← horder.prEvent_eq gy]
    have hswap := OracleComp.EvalDistEq.bind_bind_swap ($ᵗ F) ($ᵗ F)
      (fun x y => do
        let ρ ← ($ᵗ (S → F) : ProbComp _)
        let z ← AGM.fixedView A (extendTable S 0 ρ) x y
        return (ρ, x, y, z))
    rw [hswap.prEvent_eq gy]
    simp only [DLog11.experiment, prEvent_norm, decide_eq_true_eq]
    let : MeasurableSpace F := ⊤
    rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
    apply MeasureTheory.lintegral_congr
    intro y
    simpa only [gy, coeff, k, dx, dy, prEvent_norm] using
      (AGM.yReduction_table A y S (fun x => hS x y)).prEvent_eq (· = y)
  have hsplit : Pr{let z ← game}[win z] ≤
      Pr{let z ← game}[gx z] + Pr{let z ← game}[gy z] + Pr{let z ← game}[bad z] := by
    refine (prEvent_mono_of_support game win (fun z => (gx z ∨ gy z) ∨ bad z) ?_).trans
      ((prEvent_or_le game _ _).trans (add_le_add (prEvent_or_le game gx gy) le_rfl))
    intro z hz hw
    obtain ⟨ρ, _, x, _, y, _, t, ht, rfl⟩ := by
      simpa only [game, pub, bind_assoc, pure_bind, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] using hz
    have hs := AGM.fixedView_sound A (extendTable S 0 ρ) x y t ht
    have hr : x * dx ρ t + y * dy ρ t = k ρ t := by
      apply AGM.scalar_relation
      apply smul_left_injective F he
      simpa only [hs, LinearMap.map_smul, LinearMap.smul_apply, smul_smul,
        mul_comm] using hw.2.symm
    by_cases hdx : dx ρ t = 0
    · by_cases hdy : dy ρ t = 0
      · apply Or.inr
        refine ⟨hw.1, ?_⟩
        have hd := AGM.denominator_eq_sum
          (AGM.selectedWeight (coeff t) t.2 t.1.value.data.1) S ρ (coeff t) t.2 t.1.value.data.1
        change _ = ∑ i, gap t i * ρ i at hd
        rw [← hd]
        split <;> assumption
      · exact Or.inl (Or.inr (AGM.y_quotient_eq x y (dx ρ t) (dy ρ t) (k ρ t) hr hdy))
    · exact Or.inl (Or.inl (AGM.x_quotient_eq x y (dx ρ t) (dy ρ t) (k ρ t) hr hdx))
  obtain ⟨z₀, hz₀⟩ := support_nonempty (AGM.fixedView A (fun _ => 0) (0 : F) 0)
  have hm₀ := (weightedFixedRun_mem_cover S terms (fun out => out.value.data.1)
    _ _ _ (hS 0 0) z₀ hz₀).1
  have hbase : z₀.1.value.data.1.1 ∈ S := hm₀ (z₀.1.value.data.1.1, 1) (by simp [terms])
  let j := fun z : F × F × Trace F T G₁ G₂ =>
    if h : z.2.2.1.value.data.1.1 ∈ S then ⟨z.2.2.1.value.data.1.1, h⟩ else
      (⟨z₀.1.value.data.1.1, hbase⟩ : S)
  have hL : ∀ ρ z, z ∈ support (pub ρ) → valid z → gap z.2.2 (j z) ≠ 0 := by
    intro ρ z hz hv
    obtain ⟨x, _, y, _, t, ht, rfl⟩ := by
      simpa only [pub, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] using hz
    have hm := (weightedFixedRun_mem_cover S terms (fun out => out.value.data.1)
      _ _ _ (hS x y) t ht).1
    have hmem : t.1.value.data.1.1 ∈ S := hm (t.1.value.data.1.1, 1) (by simp [terms])
    simpa only [j, hmem, dite_true, gap] using
      AGM.selectedWeight_gap_ne_zero (coeff t) t.2 t.1.value.data.1 hv.2 hv.1
  have hb := prEvent_zero_gap_le_uniform_affine_extract_add pub
    (fun z => gap z.2.2) (fun _ => (0 : F)) valid j hL
  have hh : Pr{let b ← DLog11.experiment g₁ g₂ (hashReduction A)}[b = true] =
      Pr{let α ← ($ᵗ F : ProbComp F)
         let a ← $ᵗ (S → F); let b ← $ᵗ (S → F)
         let z ← pub (fun i => a i * α + b i)}[
        (-∑ i, gap z.2.2 i * b i) / (∑ i, gap z.2.2 i * a i) = α] := by
    simp only [DLog11.experiment, prEvent_norm, decide_eq_true_eq]
    let : MeasurableSpace F := ⊤
    rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
    apply MeasureTheory.lintegral_congr
    intro α
    rw [(AGM.hashReduction_table A α S hS).prEvent_eq (· = α)]
    have hswap := OracleComp.EvalDistEq.bind_bind_swap
      (do let x ← ($ᵗ F : ProbComp F); let y ← $ᵗ F; return (x, y))
      (do let a ← ($ᵗ (S → F) : ProbComp _); let b ← $ᵗ (S → F); return (a, b))
      (fun xy ab => do
        let z ← AGM.fixedView A (extendTable S 0 (fun i => ab.1 i * α + ab.2 i)) xy.1 xy.2
        return (-∑ i, gap z i * ab.2 i) / (∑ i, gap z i * ab.1 i))
    simpa only [pub, gap, coeff, prEvent_norm] using hswap.prEvent_eq (· = α)
  have hbad : Pr{let z ← game}[bad z] ≤
      Pr{let b ← DLog11.experiment g₁ g₂ (hashReduction A)}[b = true] +
        1 / Fintype.card F := by
    rw [hh]
    simpa only [game, bad, prEvent_norm, zero_sub] using hb
  rw [hgame, hx, hy]
  exact hsplit.trans (by
    simpa only [add_assoc] using add_le_add
      (le_refl (Pr{let z ← game}[gx z] + Pr{let z ← game}[gy z])) hbad)

end SynchronizedPS
