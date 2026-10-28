/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Aggregate.Execution
public import VCVio.Schemes.BLS.Aggregate.Algebra
public import VCVio.Schemes.BLS.Abort

/-! # Extraction from a programmed aggregate forgery

The shared BLS tag and insertion invariants identify the unique challenge message.
The final verification lookups supply every other cached scalar needed to strip the
adversarially chosen keys from the accepted aggregate.
-/

public section

open OracleComp OracleSpec

namespace BLS.Aggregate

variable {F G₁ G₂ Gₜ M : Type}

/-- A valid distinct-message aggregate containing an honest key at the selected challenge
slot yields the co-CDH solution by subtracting the cached scalar contributions. Signing
responses are arbitrary here: the algebraic extraction only needs a supported indexed run. -/
theorem programmed_extraction [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq M]
    (ψ : G₂ →ₗ[F] G₁) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂)
    (hg₁ : Function.Surjective (· • ψ g₂ : F → G₁))
    (hg₂ : Function.Surjective (· • g₂ : F → G₂)) (he : e (ψ g₂) g₂ ≠ 0)
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) (List (G₂ × M) × G₁))
    (sign : Option F → G₁) (x mask : F) (h : G₁) (j : ℕ)
    (z : ((List (G₂ × M) × G₁) × Gₜ) × OracleState (Option F) M)
    (hz : z ∈ support ((simulateQ
      (indexedOracle (tagDraw j)
        (fun tag => tag.elim (h + mask • ψ g₂) (· • ψ g₂)) sign (some j))
      (withFinalPairings e oa)).run OracleState.empty))
    (hd : (z.1.1.1.map Prod.snd).Nodup) (msg : M)
    (hm : (x • g₂, msg) ∈ z.1.1.1) (hc : z.2.cache msg = some (none, j))
    (hv : e z.1.1.2 g₂ = z.1.2) :
    z.1.1.2 - (z.1.1.1.map fun p => cachedScalar mask z.2 p.2 • ψ p.1).sum = x • h := by
  let hash : Option F → G₁ := fun tag => tag.elim (h + mask • ψ g₂) (· • ψ g₂)
  obtain ⟨hi, hall, hr⟩ := withFinalPairings_support e (tagDraw j) hash sign (some j)
    oa _ (indexInv_empty (some j)) z hz
  have ht := simulateQ_run_preservesInv _ _
    (indexedOracle_preserves_challengeInv hash sign j)
    (withFinalPairings e oa) OracleState.empty
    (by simp [OracleState.empty]) z hz
  apply aggregate_sub_eq ψ e g₂ hg₁ hg₂ he (cachedHash hash z.2) (cachedScalar mask z.2)
    z.1.1.1 x msg h z.1.1.2 hd hm
  · simp [cachedHash, cachedScalar, hc, hash]
  · intro p hp hne
    obtain ⟨v, i, hc'⟩ := hall p hp
    cases v with
    | none =>
      have hij : i = j := ht p.2 i hc'
      subst i
      exact False.elim (hne (hi.unique p.2 msg none none j hc' hc))
    | some r => simp [cachedHash, cachedScalar, hc', hash]
  · exact hv.trans hr

end BLS.Aggregate
