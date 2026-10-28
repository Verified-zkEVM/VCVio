/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Aggregate.Basic

/-! # Type 2 aggregate extraction

Generation of the second source implies compatibility of its public linear map with the
pairing. This identity permits stripping contributions of arbitrary adversarial public keys.
Distinct messages ensure that the programmed challenge occurs in exactly one position.
-/

public section

namespace BLS.Aggregate

variable {F G₁ G₂ Gₜ M : Type}

/-- A generating second-source point makes the public source map compatible with the pairing.
BGLS needs this identity for every adversarially chosen key when stripping aggregate terms;
linearity of the source map alone does not imply it in a higher-dimensional second source. -/
theorem pairing_sourceMap_eq [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂)
    (hg₂ : Function.Surjective (· • g₂ : F → G₂)) (pk : G₂) :
    e (ψ pk) g₂ = e (ψ g₂) pk := by
  obtain ⟨r, rfl⟩ := hg₂ pk
  simp

private theorem pairing_sum_unprogrammed [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂)
    (hg₂ : Function.Surjective (· • g₂ : F → G₂))
    (H : M → G₁) (r : M → F) (ps : List (G₂ × M))
    (hH : ∀ p ∈ ps, H p.2 = r p.2 • ψ g₂) :
    (ps.map fun p => e (H p.2) p.1).sum =
      e (ps.map fun p => r p.2 • ψ p.1).sum g₂ := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, map_add, LinearMap.add_apply]
    rw [hH p (by simp), map_smul, LinearMap.smul_apply,
      ih (fun q hq => hH q (by simp [hq])), map_smul, LinearMap.smul_apply,
      pairing_sourceMap_eq ψ e g₂ hg₂]

private theorem pairing_sum_programmed [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂)
    (hg₂ : Function.Surjective (· • g₂ : F → G₂))
    (H : M → G₁) (r : M → F) (ps : List (G₂ × M)) (x : F) (msg : M) (h : G₁)
    (hd : (ps.map Prod.snd).Nodup) (hm : (x • g₂, msg) ∈ ps)
    (ht : H msg = h + r msg • ψ g₂)
    (ho : ∀ p ∈ ps, p.2 ≠ msg → H p.2 = r p.2 • ψ g₂) :
    (ps.map fun p => e (H p.2) p.1).sum =
      e h (x • g₂) + e (ps.map fun p => r p.2 • ψ p.1).sum g₂ := by
  induction ps with
  | nil => simp at hm
  | cons p ps ih =>
    obtain ⟨hnot, hd⟩ := List.nodup_cons.mp hd
    rcases List.mem_cons.mp hm with hp | hm
    · subst p
      have hall : ∀ q ∈ ps, H q.2 = r q.2 • ψ g₂ := by
        intro q hq
        apply ho q (by simp [hq])
        intro he
        exact hnot (List.mem_map.mpr ⟨q, hq, he⟩)
      simp only [List.map_cons, List.sum_cons, ht, map_add, LinearMap.add_apply]
      rw [pairing_sum_unprogrammed ψ e g₂ hg₂ H r ps hall]
      simp only [map_smul, LinearMap.smul_apply]
      rw [smul_comm x (r msg)]
      abel
    · have hne : p.2 ≠ msg := by
        intro he
        exact hnot (List.mem_map.mpr ⟨(x • g₂, msg), hm, he.symm⟩)
      have ih' := ih hd hm (fun q hq => ho q (by simp [hq]))
      simp only [List.map_cons, List.sum_cons, ho p (by simp) hne, map_add,
        LinearMap.add_apply, map_smul, LinearMap.smul_apply, ih',
        pairing_sourceMap_eq ψ e g₂ hg₂]
      abel

/-- A valid distinct-message aggregate with one challenge-programmed honest position yields
the co-CDH answer after every scalar contribution is subtracted. The second-source generator
hypothesis justifies stripping arbitrary chosen keys through `pairing_sourceMap_eq`. -/
theorem aggregate_sub_eq [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂)
    (hg₁ : Function.Surjective (· • ψ g₂ : F → G₁))
    (hg₂ : Function.Surjective (· • g₂ : F → G₂)) (he : e (ψ g₂) g₂ ≠ 0)
    (H : M → G₁) (r : M → F) (ps : List (G₂ × M)) (x : F) (msg : M) (h σ : G₁)
    (hd : (ps.map Prod.snd).Nodup) (hm : (x • g₂, msg) ∈ ps)
    (ht : H msg = h + r msg • ψ g₂)
    (ho : ∀ p ∈ ps, p.2 ≠ msg → H p.2 = r p.2 • ψ g₂)
    (hv : e σ g₂ = (ps.map fun p => e (H p.2) p.1).sum) :
    σ - (ps.map fun p => r p.2 • ψ p.1).sum = x • h := by
  apply (BLS.pairing_eq_iff e (ψ g₂) g₂ hg₁ he x h _).mp
  rw [map_sub, LinearMap.sub_apply, hv,
    pairing_sum_programmed ψ e g₂ hg₂ H r ps x msg h hd hm ht ho,
    add_sub_cancel_right]

end BLS.Aggregate
