/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Basic
public import VCVio.CryptoFoundations.HardnessAssumptions.CoCDH
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! # BLS index-guessing reduction to Type 3 co-CDH

The reduction for the signature scheme of Boneh, Lynn and Shacham, *Short Signatures from
the Weil Pairing* (ASIACRYPT 2001), guesses a distinct hash input's insertion index.
It programs that input with the co-CDH challenge and answers every other input by sampling
a scalar. Its scalar table is shared by direct hash queries, signing, and a final hash of
the candidate forgery. Signing the programmed input aborts through `OptionT`.

This module defines the reduction and proves its local simulation and extraction laws.
The adaptive distributional comparison with `SignatureAlg.unforgeableExperiment` and
the resulting EUF-CMA probability bound remain open.
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

/-- The private hash table and its insertion counter. An absent cache entry is an unseen
message; a cached `none` is the programmed challenge; a cached `some ρ` records a sampled
scalar. The counter increases only on first visits. -/
abbrev EmbeddingState (F M : Type) := (M →ₒ Option F).QueryCache × ℕ

/-- Obtain a message's scalar tag, programming the `j`th distinct message with the challenge
tag `none`. Other new messages receive independent uniform scalars, retained on repeated visits. -/
@[expose] def embeddingEntry [SampleableType F] [DecidableEq M] (j : ℕ) (msg : M) :
    StateT (EmbeddingState F M) ProbComp (Option F) := do
  let (cache, n) ← get
  match cache msg with
  | some tag => return tag
  | none =>
      let tag ← if n = j then pure none else some <$> ($ᵗ F : ProbComp F)
      set (cache.cacheQuery msg tag, n + 1)
      return tag

/-- Answer the adversary's ambient and signing oracles using a co-CDH challenge `h`.
A scalar tag yields hash `ρ • g₁` and signature `ρ • X₁`. A challenge tag yields hash `h`
and causes immediate signing failure. No secret scalar is used. -/
@[expose] def embeddingOracle [SampleableType F] [DecidableEq M] [SMul F G₁]
    (j : ℕ) (g₁ X₁ h : G₁) :
    QueryImpl ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁))
      (OptionT (StateT (EmbeddingState F M) ProbComp)) :=
  let unif : QueryImpl unifSpec (OptionT (StateT (EmbeddingState F M) ProbComp)) :=
    fun t => liftM (unifSpec.query t : ProbComp _)
  let hash : QueryImpl (M →ₒ G₁) (OptionT (StateT (EmbeddingState F M) ProbComp)) :=
    fun msg => do
      let tag : Option F ← liftM (embeddingEntry (F := F) j msg)
      return tag.elim h (· • g₁)
  let sign : QueryImpl (M →ₒ G₁) (OptionT (StateT (EmbeddingState F M) ProbComp)) :=
    fun msg => do
      let tag : Option F ← liftM (embeddingEntry (F := F) j msg)
      match tag with
      | none => failure
      | some ρ => return ρ • X₁
  (unif + hash) + sign

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
    let attempt : OptionT (StateT (EmbeddingState F M) ProbComp) G₁ := do
      let (msg, σ) ← simulateQ (embeddingOracle j gen₁ X₁ h) (A.main (X₁, X₂))
      let tag : Option F ← liftM (embeddingEntry (F := F) j msg)
      match tag with
      | none => return σ
      | some _ => failure
    let result ← attempt.run.run' (∅, 0)
    return result.getD 0

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

/-- A cached tag is returned without changing the table or insertion counter. -/
theorem embeddingEntry_run_of_cached [SampleableType F] [DecidableEq M]
    (j : ℕ) (msg : M) (s : EmbeddingState F M) (tag : Option F)
    (hc : s.1 msg = some tag) :
    (embeddingEntry j msg).run s = pure (tag, s) := by
  simp [embeddingEntry, hc]

/-- The guessed insertion slot is filled by the challenge tag, without sampling a scalar. -/
theorem embeddingEntry_run_of_target [SampleableType F] [DecidableEq M]
    (msg : M) (s : EmbeddingState F M) (hc : s.1 msg = none) :
    (embeddingEntry s.2 msg).run s = pure (none, s.1.cacheQuery msg none, s.2 + 1) := by
  simp [embeddingEntry, hc]

/-- A fresh message away from the guessed slot gets a uniform scalar and advances the counter. -/
theorem embeddingEntry_run_of_fresh [SampleableType F] [DecidableEq M]
    (j : ℕ) (msg : M) (s : EmbeddingState F M) (hc : s.1 msg = none) (hj : s.2 ≠ j) :
    (embeddingEntry j msg).run s =
      (fun ρ => (some ρ, s.1.cacheQuery msg (some ρ), s.2 + 1)) <$> ($ᵗ F : ProbComp F) := by
  simp [embeddingEntry, hc, hj, map_eq_bind_pure_comp]

/-- A hash query reads the shared tag table and exposes either the programmed challenge or
the corresponding scalar multiple of the generator. -/
theorem embeddingOracle_run_hash [SampleableType F] [DecidableEq M] [SMul F G₁]
    (j : ℕ) (g₁ X₁ h : G₁) (msg : M) (s : EmbeddingState F M) :
    ((embeddingOracle j g₁ X₁ h (.inl (.inr msg))).run).run s =
      (fun z => (some (z.1.elim h (· • g₁)), z.2)) <$> (embeddingEntry j msg).run s := by
  simp [embeddingOracle, OptionT.run_bind, Option.elimM,
    map_eq_bind_pure_comp]

/-- A signing query returns a scalar-derived signature or aborts precisely when its tag is
the programmed challenge. -/
theorem embeddingOracle_run_sign [SampleableType F] [DecidableEq M] [SMul F G₁]
    (j : ℕ) (g₁ X₁ h : G₁) (msg : M) (s : EmbeddingState F M) :
    ((embeddingOracle j g₁ X₁ h (.inr msg)).run).run s =
      (fun z => (z.1.map (· • X₁), z.2)) <$> (embeddingEntry j msg).run s := by
  simp only [add_apply_inr, embeddingOracle, bind_pure_comp, map_eq_bind_pure_comp,
    QueryImpl.add_apply_inr, OptionT.run_bind, Option.elimM, OptionT.run_monadLift,
    monadLift_self, bind_assoc, Function.comp_apply, pure_bind, Option.elim_some, StateT.run_bind]
  apply bind_congr
  rintro ⟨tag, cache⟩
  cases tag <;> rfl

/-- Requesting a signature of the programmed message terminates with failure. -/
theorem embeddingOracle_run_sign_of_target [SampleableType F] [DecidableEq M] [SMul F G₁]
    (j : ℕ) (g₁ X₁ h : G₁) (msg : M) (s : EmbeddingState F M)
    (hc : s.1 msg = some none) :
    ((embeddingOracle j g₁ X₁ h (.inr msg)).run).run s = pure (none, s) := by
  rw [embeddingOracle_run_sign, embeddingEntry_run_of_cached j msg s none hc]
  rfl

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
