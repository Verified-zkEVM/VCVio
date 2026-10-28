/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Aggregate.Extraction
public import VCVio.Schemes.BLS.Aggregate.Programming

/-! # Success of the fixed-slot aggregate reduction

A fresh accepted aggregate at the guessed insertion slot transfers through deferred
programming and the shared BLS signing-abort comparison. Type 2 extraction then supplies
the co-CDH answer. Averaging the independent scalar mask preserves this bound.
-/

public section

open OracleComp OracleSpec

namespace BLS.Aggregate

variable {F G₁ G₂ Gₜ M : Type}

private theorem prEvent_programmedTarget_le_reductionAtMask [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (ψ : G₂ →ₗ[F] G₁) {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂))
    (hg₁ : Function.Bijective (· • ψ g₂ : F → G₁))
    (hg₂ : Function.Surjective (· • g₂ : F → G₂)) (he : e (ψ g₂) g₂ ≠ 0)
    (x : F) (j : ℕ) (mask : F) (h : G₁) :
    Pr{let z ← (simulateQ
      (indexedOracle (tagDraw (V := F) j)
        (fun tag => tag.elim (h + mask • ψ g₂) (· • ψ g₂))
        (fun tag => tag.elim 0 (· • ψ (x • g₂))) (some j))
      (withFinalPairings e (A.main (x • g₂)))).run OracleState.empty}[
      ProgrammedTarget (fun z _ => (z.1.1.map Prod.snd).Nodup ∧ e z.1.2 g₂ = z.2)
        (fun z msg => (x • g₂, msg) ∈ z.1.1) j z] ≤
    Pr{let y ← reductionAtMask ψ A j mask g₂ (x • g₂) h}[y = x • h] := by
  let impl := indexedOracle (M := M) (tagDraw (V := F) j)
    (fun tag => tag.elim (h + mask • ψ g₂) (· • ψ g₂))
    (fun tag => tag.elim 0 (· • ψ (x • g₂))) (some j)
  have hproj : (fun z => (z.1.1, z.2)) <$>
      (simulateQ impl (withFinalPairings e (A.main (x • g₂)))).run OracleState.empty =
      (simulateQ impl (withFinalHashes (A.main (x • g₂)))).run OracleState.empty := by
    have hp := congrArg (fun oa => (simulateQ impl oa).run OracleState.empty)
      (withFinalPairings_map_fst e (A.main (x • g₂)))
    simpa only [simulateQ_map, StateT.run_map] using hp
  unfold reductionAtMask
  change _ ≤ Pr{let y ← ((simulateQ impl (withFinalHashes (A.main (x • g₂)))).run
    OracleState.empty >>= _)}[y = x • h]
  rw [← hproj, bind_map_left]
  apply prEvent_le_prEvent_bind_of_support
  intro z hz hw
  obtain ⟨⟨hd, hv⟩, ⟨msg, hm, hf, hc⟩, hb⟩ := hw
  have hstrip := programmed_extraction ψ e g₂ hg₁.2 hg₂ he (A.main (x • g₂))
    (fun tag => tag.elim 0 (· • ψ (x • g₂))) x mask h j z hz hd msg hm hc hv
  simp only [hb, hd, hstrip, ↓reduceIte, not_true_eq_false, Bool.false_eq_true]
  split
  · simp
  · rename_i hn
    exact False.elim (hn (List.any_eq_true.mpr
      ⟨(x • g₂, msg), hm, by simp [hf, hc]⟩))

private theorem prEvent_freshTarget_le_reductionAtMask [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (ψ : G₂ →ₗ[F] G₁) {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂))
    (hg₁ : Function.Bijective (· • ψ g₂ : F → G₁))
    (hg₂ : Function.Surjective (· • g₂ : F → G₂)) (he : e (ψ g₂) g₂ ≠ 0)
    (x : F) (j : ℕ) (mask : F) :
    Pr{let z ← (simulateQ (indexedOracle (fun _ => $ᵗ F) (· • ψ g₂)
      (fun r => x • (r • ψ g₂)) (some j))
      (withFinalPairings e (A.main (x • g₂)))).run OracleState.empty}[
      FreshTarget (fun z _ => (z.1.1.map Prod.snd).Nodup ∧ e z.1.2 g₂ = z.2)
        (fun z msg => (x • g₂, msg) ∈ z.1.1) j z] ≤
    Pr{let h ← ($ᵗ G₁ : ProbComp G₁)
       let y ← reductionAtMask ψ A j mask g₂ (x • g₂) h}[y = x • h] := by
  have hp := prEvent_freshTarget_le_masked (· • ψ g₂) hg₁ (x • ·)
    (fun tag => tag.elim 0 (· • ψ (x • g₂)))
    (fun r => (simulated_signature_eq ψ g₂ x r).symm) j (mask • ψ g₂)
    (withFinalPairings e (A.main (x • g₂)))
    (fun z _ => (z.1.1.map Prod.snd).Nodup ∧ e z.1.2 g₂ = z.2)
    (fun z msg => (x • g₂, msg) ∈ z.1.1)
  refine hp.trans ?_
  let : MeasurableSpace G₁ := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  apply MeasureTheory.lintegral_mono
  intro h
  exact prEvent_programmedTarget_le_reductionAtMask ψ A hg₁ hg₂ he x j mask h

/-- A fresh accepted aggregate at the fixed guessed slot bounds the named reduction's
co-CDH success, averaged over its independent mask and the uniform challenge. -/
theorem prEvent_freshTarget_le_reductionAt [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (ψ : G₂ →ₗ[F] G₁) {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂))
    (hg₁ : Function.Bijective (· • ψ g₂ : F → G₁))
    (hg₂ : Function.Surjective (· • g₂ : F → G₂)) (he : e (ψ g₂) g₂ ≠ 0)
    (x : F) (j : ℕ) :
    Pr{let z ← (simulateQ (indexedOracle (fun _ => $ᵗ F) (· • ψ g₂)
      (fun r => x • (r • ψ g₂)) (some j))
      (withFinalPairings e (A.main (x • g₂)))).run OracleState.empty}[
      FreshTarget (fun z _ => (z.1.1.map Prod.snd).Nodup ∧ e z.1.2 g₂ = z.2)
        (fun z msg => (x • g₂, msg) ∈ z.1.1) j z] ≤
    Pr{let h ← ($ᵗ G₁ : ProbComp G₁)
       let y ← reductionAt ψ A j g₂ (x • g₂) h}[y = x • h] := by
  have havg := le_prEvent_bind_of_forall_le ($ᵗ F : ProbComp F) (by simp)
    (fun mask => do
      let h ← ($ᵗ G₁ : ProbComp G₁)
      let y ← reductionAtMask ψ A j mask g₂ (x • g₂) h
      pure (y = x • h)) id
    (fun mask => by
      simpa only [map_bind, map_pure, Functor.map_map, Function.comp_def, id_eq,
        bind_pure_comp] using
        prEvent_freshTarget_le_reductionAtMask ψ A hg₁ hg₂ he x j mask)
  simp only [map_bind, Functor.map_map, id_eq, bind_pure_comp] at havg
  unfold reductionAt
  simp only [map_bind]
  refine havg.trans_eq ?_
  exact OracleComp.prEvent_bind_bind_swap_of_uniform _ _ _

end BLS.Aggregate
