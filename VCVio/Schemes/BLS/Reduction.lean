/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Abort
public import VCVio.Schemes.BLS.Execution
public import VCVio.CryptoFoundations.HardnessAssumptions.CoCDH
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! # The BLS index-guessing co-CDH solver

The Boneh–Lynn–Shacham reduction guesses one insertion index and programs its hash answer
with the challenge. Other answers carry sampled scalar preimages. Signing the selected
message raises a persistent abort flag; an aborted run returns zero.
-/

public section

open OracleComp OracleSpec

namespace BLS

variable {F G₁ G₂ Gₜ M : Type}

/-- Separate structural budgets for direct hash and signing queries, uniformly over public
keys. Uniform-sampling queries are unrestricted. -/
@[expose] def QueryBound [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂))
    (qH qS : ℕ) : Prop :=
  ∀ pk, (A.main pk).IsQueryBoundP (· matches .inl (.inr _)) qH ∧
    (A.main pk).IsQueryBoundP (· matches .inr _) qS

/-- Answer hashes with a shared scalar-tag cache and signatures using the first public-key
component. The challenge tag has no available signature and raises the persistent abort flag. -/
@[expose] def embeddingOracle [SampleableType F] [DecidableEq M] [SMul F G₁] [Zero G₁]
    (j : ℕ) (g₁ X₁ h : G₁) :
    QueryImpl ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁))
      (StateT (OracleState (Option F) M) ProbComp) :=
  indexedOracle (tagDraw j) (fun tag => tag.elim h (· • g₁))
    (fun tag => tag.elim 0 (· • X₁)) (some j)

/-- Run the co-CDH solver with a fixed insertion-index guess. The final hash lookup ensures
that an output message not queried by the adversary can still occupy the guessed slot.
An aborted run or a forgery away from the guessed slot returns zero. -/
@[expose] def reductionAt [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂))
    (j : ℕ) : CoCDH.Adversary F G₁ G₂ :=
  fun gen₁ _ X₁ X₂ h => do
    let z ← (simulateQ (embeddingOracle (F := F) j gen₁ X₁ h)
      (withFinalHash (A.main (X₁, X₂)))).run OracleState.empty
    if z.2.bad then return 0
    match z.2.cache z.1.1.1 with
    | some (none, _) => return z.1.1.2
    | _ => return 0

/-- The index-guessing co-CDH reduction. The guess is uniform among `qH + qS + 1` slots,
including hashes introduced by signing and final verification. The co-CDH experiment applies
its ordinary equality test to the output, including the zero fallback on abort. -/
@[expose] def reduction [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂))
    (qH qS : ℕ) : CoCDH.Adversary F G₁ G₂ :=
  fun gen₁ gen₂ X₁ X₂ h => do
    let j ← $ᵗ Fin (qH + qS + 1)
    reductionAt A j.val gen₁ gen₂ X₁ X₂ h

/-- Scalar sampling produces the same hash distribution as a uniform group sample whenever
the generator parametrizes the first source group bijectively. -/
theorem smul_uniformSample_evalDistEq [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    (g₁ : G₁) (hg₁ : Function.Bijective (· • g₁ : F → G₁)) :
    ((· • g₁) <$> ($ᵗ F : ProbComp F)) =ᵈ ($ᵗ G₁ : ProbComp G₁) :=
  SampleableType.map_uniformSample_evalDistEq_of_bijective hg₁

/-- The signature computed from a cached scalar and the first public-key component is the
honest signature of the simulated hash. -/
theorem simulated_signature_eq [Field F] [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (x ρ : F) : ρ • (x • g₁) = x • (ρ • g₁) :=
  smul_comm ρ x g₁

end BLS
