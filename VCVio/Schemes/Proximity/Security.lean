/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Proximity.BadReduction
public import VCVio.Schemes.Proximity.Budget

/-! # Algebraic security of Proximity

The real EUF-CMA game is split into nonzero-gap extraction, zero-gap affine extraction,
and the actual fresh linear-collision event. The masked slope costs exactly one field-sized
term. Finite covers appear only in the proof; slots and the named reductions remain lazy.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace Proximity.AGM

private def view {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂)
    (ρ : Index Slot dimension → F) (κ : F) : ProbComp (Trace F Slot G₁ G₂ dimension) :=
  Weighted.fixedRun (fun i => ρ i • g₁)
    (fun m => Weighted.value ρ (terms m) • (κ • g₁)) (A.rawMain (κ • g₂))

end Proximity.AGM

namespace Proximity

/-- The EUF-CMA advantage of an algebraic adversary is bounded by its two named
(1,1)-discrete-logarithm reductions, one hidden-slope collision, and the actual fresh
linear-collision probability in the original random-oracle execution. -/
theorem unforgeableAdvantage_le {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [Fintype F] [SampleableType F] [DecidableEq F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0) :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Index Slot dimension →ₒ G₁))
      A.toUnforgeableAdversary ≤
      Pr{let b ← DLog11.experiment g₁ g₂ (goodReduction A)}[b = true] +
      Pr{let b ← DLog11.experiment g₁ g₂ (badReduction A)}[b = true] +
      1 / Fintype.card F + Pr{let b ← collisionGame A}[b = true] := by
  classical
  obtain ⟨S, hS⟩ := AGM.exists_base_cover A
  let table := fun ρ : S → F => extendTable S 0 ρ
  let pub := fun ρ : S → F => do
    let κ ← ($ᵗ F : ProbComp F)
    let z ← AGM.view A (table ρ) κ
    return (κ, z)
  let game := do
    let ρ ← ($ᵗ (S → F) : ProbComp _)
    let z ← pub ρ
    return (ρ, z)
  let win := fun z : (S → F) × F × AGM.Trace F Slot G₁ G₂ dimension =>
    z.2.2.1.value.data ∉ AGM.signedMessages z.2.2.2 ∧
      e (AGM.forgery z.2.2.1).2 g₂ =
        e (Weighted.value (table z.1) (terms z.2.2.1.value.data) • g₁) (z.2.1 • g₂)
  let good := fun z : (S → F) × F × AGM.Trace F Slot G₁ G₂ dimension =>
    (AGM.goodRepresentation (table z.1) z.2.2.1 z.2.2.2).const /
      (Weighted.value (table z.1) (terms z.2.2.1.value.data) -
        (AGM.goodRepresentation (table z.1) z.2.2.1 z.2.2.2).lin) = z.2.1
  let valid := fun z : F × AGM.Trace F Slot G₁ G₂ dimension =>
    z.2.1.value.data ∉ AGM.signedMessages z.2.2 ∧
      z.2.1.value.data.1 ≠ AGM.signingVector (AGM.coefficients z.2.1) z.2.2
  let bad := fun z : (S → F) × F × AGM.Trace F Slot G₁ G₂ dimension =>
    valid z.2 ∧ ∑ i, AGM.gap S z.2.2 i * z.1 i = 0
  let collision := fun z : (S → F) × F × AGM.Trace F Slot G₁ G₂ dimension =>
    AGM.FreshCollision z.2.2.1 z.2.2.2
  have horder : (do
      let κ ← ($ᵗ F : ProbComp F); let ρ ← $ᵗ (S → F)
      let z ← AGM.view A (table ρ) κ
      return (ρ, κ, z)) =ᵈ game := by
    simpa only [game, pub, bind_assoc, pure_bind] using
      OracleComp.EvalDistEq.bind_bind_swap ($ᵗ F) ($ᵗ (S → F))
        (fun κ ρ => do let z ← AGM.view A (table ρ) κ; return (ρ, κ, z))
  have hgame : SignatureAlg.unforgeableAdvantage
      (ProbCompRuntime.rom (Index Slot dimension →ₒ G₁)) A.toUnforgeableAdversary =
      Pr{let z ← game}[win z] := by
    rw [AGM.unforgeableAdvantage_eq_table A hg₁ S hS]
    simpa only [prEvent_norm, win, AGM.view, table] using horder.prEvent_eq win
  have hcollision : Pr{let b ← collisionGame A}[b = true] =
      Pr{let z ← game}[collision z] := by
    rw [AGM.collisionGame_eq_table A hg₁ S hS]
    simpa only [prEvent_norm, collision, AGM.view, table] using horder.prEvent_eq collision
  have hgood : Pr{let b ← DLog11.experiment g₁ g₂ (goodReduction A)}[b = true] =
      Pr{let z ← game}[good z] := by
    rw [← horder.prEvent_eq good]
    simp only [DLog11.experiment, prEvent_norm, decide_eq_true_eq]
    let : MeasurableSpace F := ⊤
    rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
    apply MeasureTheory.lintegral_congr
    intro κ
    simpa only [good, prEvent_norm, AGM.goodRepresentation, AGM.view, table] using
      (AGM.goodReduction_table A κ S (hS κ)).prEvent_eq (· = κ)
  have hsplit : Pr{let z ← game}[win z] ≤
      Pr{let z ← game}[good z] +
        (Pr{let z ← game}[bad z] + Pr{let z ← game}[collision z]) := by
    apply (prEvent_mono_of_support game win (fun z => good z ∨ bad z ∨ collision z) ?_).trans
      ((prEvent_or_le game good (fun z => bad z ∨ collision z)).trans
        (add_le_add (le_refl _) (prEvent_or_le game bad collision)))
    intro z hz hw
    obtain ⟨ρ, _, v, hv, rfl⟩ := by
      simpa only [game, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] using hz
    obtain ⟨κ, _, t, ht, rfl⟩ := by
      simpa only [pub, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] using hv
    by_cases hc : t.1.value.data.1 = AGM.signingVector (AGM.coefficients t.1) t.2
    · exact Or.inr (Or.inr ⟨hw.1, hc⟩)
    by_cases hg : (AGM.goodRepresentation (table ρ) t.1 t.2).lin =
        Weighted.value (table ρ) (terms t.1.value.data)
    · apply Or.inr ∘ Or.inl
      refine ⟨⟨hw.1, hc⟩, ?_⟩
      rw [← AGM.gap_eq S ρ t]
      exact sub_eq_zero.mpr hg.symm
    · exact Or.inl (AGM.goodRepresentation_extract A κ (table ρ) t ht he hw.2 hg)
  obtain ⟨z₀, hz₀⟩ := support_nonempty (AGM.view A (table (fun _ => 0)) (0 : F))
  have hm₀ := (Weighted.fixedRun_mem_cover terms S (fun out => out.value.data)
    _ _ _ (hS 0) z₀ hz₀).1
  have hi₀ : (none, z₀.1.value.data.2) ∈ S :=
    hm₀ ((none, z₀.1.value.data.2), 1) (by simp [terms])
  let j := fun z : F × AGM.Trace F Slot G₁ G₂ dimension =>
    if h : ∃ i : S, AGM.gap S z.2 i ≠ 0 then h.choose else ⟨(none, z₀.1.value.data.2), hi₀⟩
  have hL : ∀ ρ z, z ∈ support (pub ρ) → valid z → AGM.gap S z.2 (j z) ≠ 0 := by
    intro ρ z hz hv
    obtain ⟨κ, _, t, ht, rfl⟩ := by
      simpa only [pub, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] using hz
    have hc := Weighted.fixedRun_mem_cover terms S (fun out => out.value.data)
      _ _ _ (hS κ) t ht
    have hn := AGM.gap_ne_zero S t hc.1 hc.2 hv.2
    simpa only [j, dite_eq_left hn] using hn.choose_spec
  have hb := prEvent_zero_gap_le_uniform_affine_extract_add pub
    (fun z => AGM.gap S z.2) (fun _ => 0) valid j hL
  have hbad : Pr{let b ← DLog11.experiment g₁ g₂ (badReduction A)}[b = true] =
      Pr{let α ← ($ᵗ F : ProbComp F)
         let a ← $ᵗ (S → F); let b ← $ᵗ (S → F)
         let z ← pub (fun i => a i * α + b i)}[
        (0 - ∑ i, AGM.gap S z.2 i * b i) / (∑ i, AGM.gap S z.2 i * a i) = α] := by
    simp only [DLog11.experiment, prEvent_norm, decide_eq_true_eq]
    let : MeasurableSpace F := ⊤
    rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
    apply MeasureTheory.lintegral_congr
    intro α
    rw [(AGM.badReduction_table A α S hS).prEvent_eq (· = α)]
    have hswap := OracleComp.EvalDistEq.bind_bind_swap ($ᵗ F)
      (do let a ← ($ᵗ (S → F) : ProbComp _); let b ← $ᵗ (S → F); return (a, b))
      (fun κ ab => do
        let z ← AGM.view A (table (fun i => ab.1 i * α + ab.2 i)) κ
        return (0 - ∑ i, AGM.gap S z i * ab.2 i) / (∑ i, AGM.gap S z i * ab.1 i))
    simpa only [pub, AGM.view, table, prEvent_norm] using hswap.prEvent_eq (· = α)
  have hb' : Pr{let z ← game}[bad z] ≤
      Pr{let b ← DLog11.experiment g₁ g₂ (badReduction A)}[b = true] +
        1 / Fintype.card F := by
    rw [hbad]
    simpa only [game, bad, prEvent_norm] using hb
  rw [hgame, hgood, hcollision]
  exact hsplit.trans (by
    simpa only [add_assoc] using add_le_add (le_refl _) (add_le_add hb' (le_refl _)))

/-- Proximity's EUF-CMA security bound under explicit pathwise hash and signing budgets.
The final term is the actual fresh linear-collision probability with at most `qh` direct hash
replies and `qs` signing replies. It equals the source collision event under `hqueries`. -/
theorem unforgeableAdvantage_le_of_algebraic {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [Fintype F] [SampleableType F] [DecidableEq F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) (qh qs : ℕ)
    (hqueries : A.QueryBound qh qs)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0) :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Index Slot dimension →ₒ G₁))
      A.toUnforgeableAdversary ≤
      Pr{let b ← DLog11.experiment g₁ g₂ (goodReduction A)}[b = true] +
      Pr{let b ← DLog11.experiment g₁ g₂ (badReduction A)}[b = true] +
      1 / Fintype.card F + freshCollisionProbability A qh qs := by
  rw [freshCollisionProbability_eq A qh qs hqueries hg₁]
  exact unforgeableAdvantage_le A hg₁ he

end Proximity
