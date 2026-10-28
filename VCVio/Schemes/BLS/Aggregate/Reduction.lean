/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Aggregate.Basic
public import VCVio.Schemes.BLS.Reduction

/-! # The BGLS Type 2 co-CDH solver

An insertion-index guess selects the programmed hash. A fresh uniform mask shifts the
challenge at that slot; all other slots use independently sampled scalar multiples of
`ψ g₂`. The shared BLS indexed oracle records signing queries and aborts when the selected
message is signed. Extraction subtracts the scalar contributions of every listed key.
-/

public section

open OracleComp OracleSpec

namespace BLS.Aggregate

variable {F G₁ G₂ Gₜ M : Type}

/-- Direct hash and signing budgets, and a bound on the length of every supported forgery.
Uniform-sampling queries are unrestricted, and all premises hold for every public key. -/
@[expose] def QueryBound [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂))
    (qH qS N : ℕ) : Prop :=
  ∀ pk, (A.main pk).IsQueryBoundP (· matches .inl (.inr _)) qH ∧
    (A.main pk).IsQueryBoundP (· matches .inr _) qS ∧
    ∀ z ∈ support (A.main pk), z.1.length ≤ N

/-- Query every final message so the extraction cache includes messages first used in the
forgery. This adds at most the length of the output list to the hash budget. -/
@[expose] def withFinalHashes
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) (List (G₂ × M) × G₁)) :
    OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) (List (G₂ × M) × G₁) := do
  let z ← oa
  let _ ← z.1.mapM fun p =>
    ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)).query (.inl (.inr p.2))
  return z

/-- The scalar contribution of a cached message to be stripped from the aggregate.
The challenge slot uses its independently sampled mask; a missing cache entry contributes zero. -/
@[expose] def cachedScalar [Zero F] (mask : F) (st : OracleState (Option F) M) (msg : M) : F :=
  match st.cache msg with
  | some (some r, _) => r
  | some (none, _) => mask
  | none => 0

/-- Fixed-index BGLS solver using the public Type 2 map. The selected answer is
`h + mask • ψ gen₂`; other answers are `r • ψ gen₂`. Signing uses `r • ψ pk`.
After an abort, duplicate messages, or absence of a fresh honest selected entry, it returns
zero. Otherwise it strips every scalar contribution, including the selected entry's mask. -/
@[expose] def reductionAtMask [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (ψ : G₂ →ₗ[F] G₁) {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂))
    (j : ℕ) (mask : F) : CoCDH.IsoAdversary F G₁ G₂ :=
  fun gen₂ pk h => do
    let z ← (simulateQ
      (indexedOracle (tagDraw (V := F) j)
        (fun tag => tag.elim (h + mask • ψ gen₂) (· • ψ gen₂))
        (fun tag => tag.elim 0 (· • ψ pk)) (some j))
      (withFinalHashes (A.main pk))).run OracleState.empty
    if z.2.bad then return 0
    if ¬(z.1.1.map Prod.snd).Nodup then return 0
    if z.1.1.any (fun p => decide (p.1 = pk) && decide (p.2 ∉ z.2.signed) &&
        (match z.2.cache p.2 with | some (none, _) => true | _ => false)) then
      return z.1.2 - (z.1.1.map (fun p => cachedScalar mask z.2 p.2 • ψ p.1)).sum
    else return 0

/-- Fixed-index solver with an independent uniform mask for the programmed hash. -/
@[expose] def reductionAt [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (ψ : G₂ →ₗ[F] G₁) {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂))
    (j : ℕ) : CoCDH.IsoAdversary F G₁ G₂ :=
  fun gen₂ pk h => do
    let mask ← $ᵗ F
    reductionAtMask ψ A j mask gen₂ pk h

/-- BGLS's Type 2 solver with a uniform insertion-index guess. The guessing range has
`max 1 (qH + qS + N)` slots: direct hashes, signing hashes, and final verification hashes.
The maximum with one makes the sampling type inhabited even for zero budgets. -/
@[expose] def reduction [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (ψ : G₂ →ₗ[F] G₁) {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂))
    (qH qS N : ℕ) : CoCDH.IsoAdversary F G₁ G₂ :=
  letI : NeZero (max 1 (qH + qS + N)) := ⟨by omega⟩
  fun gen₂ pk h => do
    let j ← $ᵗ Fin (max 1 (qH + qS + N))
    reductionAt ψ A j.val gen₂ pk h

/-- Uniform scalar masking of a fixed challenge is a uniform group sample whenever
scalar multiplication by the image of the generator is bijective. -/
theorem masked_uniformSample_evalDistEq [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂]
    (ψ : G₂ →ₗ[F] G₁) (g₂ : G₂) (h : G₁)
    (hg : Function.Bijective (· • ψ g₂ : F → G₁)) :
    ((fun r => h + r • ψ g₂) <$> ($ᵗ F : ProbComp F)) =ᵈ ($ᵗ G₁ : ProbComp G₁) := by
  apply SampleableType.map_uniformSample_evalDistEq_of_bijective
  exact (Equiv.addLeft h).bijective.comp hg

/-- The scalar-based signing answer is honest at every unprogrammed message. -/
theorem simulated_signature_eq [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    (ψ : G₂ →ₗ[F] G₁) (g₂ : G₂) (x r : F) :
    r • ψ (x • g₂) = x • (r • ψ g₂) := by
  rw [map_smul]
  exact BLS.simulated_signature_eq (ψ g₂) x r

/-- Subtracting the selected hash's mask from an honest signature extracts the co-CDH answer. -/
theorem sub_mask_eq [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    (ψ : G₂ →ₗ[F] G₁) (g₂ : G₂) (x r : F) (h : G₁) :
    x • (h + r • ψ g₂) - r • ψ (x • g₂) = x • h := by
  rw [simulated_signature_eq, smul_add, add_sub_cancel_right]

end BLS.Aggregate
